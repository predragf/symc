from z3 import *
from modules.simulink.cocosim.cocosimmodel import *
import modules.simulink.cocosim.cocosimmodelmanager as CoCoSimModelManager
from modules.simulink.cocosim.cocosimstatespace import *
from modules.simulink.cocosim.cocosimstatespacegenerator import *
from modules.simulink.cocosim.cocosimstatespacemanager import *
from modules.routinegenerators.routinegenerator import *
from modules.assertiongenerators.assertiongenerator import *
from modules.utils.gcd import *
from modules.utils.utils import *
from modules.simulink.cocosim.stateflow.stateflowmodel import *
import time


class SyMC:

    def __init__(self, _configuration=dict()):
        self.__configure(_configuration)

    def __configure(self, _configuration=dict()):
        self._configuration = _configuration
        self.reuseExistingModel = _configuration.get(
            "reuseExistingModel", "") is True
        self.saveStateSpace = _configuration.get("saveStateSpace", "") is True
        self.useTactics = _configuration.get("useTactics", "") is True

    def __createGoal(self):
        goal = Goal()
        return goal

    def __createSolver(self):
        solver = Solver()
        solver.set("mbqi", True)
        solver.set("unsat-core", True)
        solver.set("mbqi.max_iterations", 100)
        return solver

    def __executeSolver(self, solver):
        result = dict()
        verd = solver.check()
        result["verdict"] = verd
        if verd == sat:
            result["model"] = solver.model()
        else:
            result["unsatcore"] = solver.unsat_core()
        return result

    def __createAndInitializeSolver(self, _goal):
        solver = self.__createSolver()
        if self.useTactics:
            tactic = Then("smt", "elim-term-ite", "elim-and")
            print("Applying tactics on the goal ...")
            _time = time.time()
            parsedAssertions = tactic(_goal).as_expr()
            print("Applying tactic on the goal completed. Time: {0}".format(
                time.time() - _time))
            solver.add(parsedAssertions)
        else:
            solver.add(_goal)
        return solver

    def __obtainModelStateSpace(self, sModel, totalSteps):
        ssg = StateSpaceGenerator()
        # the size of the execution, that is the exexution traces is
        # calculated as the symbolic fixed point of the model multiplied by
        # the WCE coefficient.
        stateSpace = ssg.generateStateSpace(sModel, totalSteps)
        if self.saveStateSpace:
            StateSpaceManager.saveStateSpaceToFile(stateSpace,
                                                   "./models/exec/{0}{1}{2}.ss"
                                                   .format(sModel.getModelName(),
                                                           sModel.getFundamentalSampleTime(),
                                                           totalSteps))
        return stateSpace

    def __generateScriptForChecking(self, smtScript):
        parsedSMTScript = ""
        try:
            parsedSMTScript = z3.parse_smt2_string(smtScript)
        except Exception as ex:
            print("Script parsing failed. \n Reason: {0}".format(ex))
            parsedSMTScript = ""
        return parsedSMTScript

    def __constructPathToModel(self, modelname, stepsize, totalSteps):
        return "./models/exec/{0}-{1}-{2}.smt2".format(modelname, stepsize, totalSteps)

    def __saveExistingSMTModel(self, modelname="", stepsize="", totalSteps="", _smtModel=""):
        pathToSMTModel = self.__constructPathToModel(modelname, stepsize, totalSteps)
        absolutePathSMTModel = os.path.abspath(pathToSMTModel)
        try:
            print("Script saving in progress ...")
            text_file = openFile(absolutePathSMTModel, "w")
            text_file.write(_smtModel)
            text_file.close()
            print("Script saved.")
        except Exception as ex:
            print("Script saving failed. \n Reason: {0}".format(ex))

    def __loadExistingSMTModel(self, modelname="", stepsize="", totalSteps=""):
        existingSmtModel = ""
        pathToSMTModel = self.__constructPathToModel(modelname, stepsize, totalSteps)
        try:
            print("Loading existing model in progress ...")
            with open(pathToSMTModel, 'r') as smtModelFile:
                existingSmtModel = smtModelFile.read()
                print("Existing model loaded.")
        except Exception as ex:
            print("Loading existing model failed. \n Reason: {0}".format(ex))
            existingSmtModel = ""
        return existingSmtModel

    def __generateAssertionsFromProperty(self, propertyAssertion, totalSteps):
        if cUtils.compareStringsIgnoreCase("", propertyAssertion):
            return ""
        propertyAssertions = []
        signalPattern = r'signal_\w{12}'
        usedSignals = re.findall(signalPattern, property)
        for i in range(0, totalSteps):
            assertion = propertyAssertion
            for usedSignal in usedSignals:
                assertion = assertion.replace(usedSignal, "{0}_{1}".format(usedSignal, i))
            propertyAssertions.append(assertion)
        return "\n".join(propertyAssertions)

    def __combineSimulinkAndStateflow(self, sModel, totalSteps):
        baseModel = ""
        simulinkStateSpaceForChecking = self.__obtainModelStateSpace(sModel, totalSteps)
        declarationLib = simulinkStateSpaceForChecking.getDeclarationLib()
        declarations = simulinkStateSpaceForChecking.getDeclarations()
        assertions = simulinkStateSpaceForChecking.getAssertions()
        for block in sModel.getBlocksForTransformation():
            if cUtils.compareStringsIgnoreCase(block.get("BlockType"), "SubSystem") and len(block.get("StateflowContent", {})) > 0:
                stateFLowChart = StateflowModel(block)
                sfDeclarations, sfAssertions = stateFLowChart.generateTransitionRelation(
                    totalSteps, sModel.getConnectionTable())
                declarations = "{0}\n{1}".format(declarations, sfDeclarations)
                assertions = "{0}\n{1}".format(assertions, sfAssertions)

        # Filter out declaration duplicates coming from stateflows with the same names (Needs to be fixed in the future).
        declaration_array = []
        declaration_string = ""
        file1 = open('declarations.txt', 'w')
        for d in declarations.split('\n'):
            if not (d in declaration_array):
                declaration_array.append(d)
            else:
                continue
            declaration_string = "{0}\n{1}".format(declaration_string, d)
        baseModel = "{0}\n{1}\n{2}".format(declarationLib, declaration_string, assertions)
        file1.write(baseModel)
        #file1.write(sfDeclarations)
        file1.close()
        return baseModel

    def __getSMTScript(self, sModel, totalSteps, propertyAssertion):
        # this function is the holy grail for us
        baseModel = ""
        if self.reuseExistingModel:
            baseModel = self.__loadExistingSMTModel(
                sModel.getModelName(), sModel.getFundamentalSampleTime(), totalSteps)
        if baseModel == "":
            baseModel = self.__combineSimulinkAndStateflow(sModel, totalSteps)
        self.__saveExistingSMTModel(sModel.getModelName(),
                                    sModel.getFundamentalSampleTime(), totalSteps, baseModel)
        propertyAssertions = self.__generateAssertionsFromProperty(propertyAssertion, totalSteps)
        return "{0}\n;the propeties start here\n{1}".format(baseModel, propertyAssertions)

    def __createAndPopulateSolver(self, pathToModel, slistPath, totalSteps, propertyAssertion):
        sModel = CoCoSimModelManager.loadModel(pathToModel, slistPath, self._configuration)
        smtModel = self.__getSMTScript(
            sModel, totalSteps, propertyAssertion)
        goal = self.__createGoal()
        smtScript = self.__generateScriptForChecking(smtModel)
        goal.add(smtScript)
        solver = self.__createAndInitializeSolver(goal)
        return solver

    def configure(self, _configuration=dict()):
        self.__configure(_configuration)

    def checkModel(self, pathToModel, slistPath, totalSteps, propertyAssertion=""):
        # stepSize is the fundamental step time
        start = time.time()
        print("COCOSIM Model verification started at {0}".format(
            time.strftime("%H:%M:%S")))
        print("Creating model ...")
        solver = self.__createAndPopulateSolver(
            pathToModel, slistPath, totalSteps, propertyAssertion)
        print("Creating model finished in {0:.3f} seconds.".format(time.time()
                                                                   - start))
        print("Model checking ...")
        start = time.time()
        result = self.__executeSolver(solver)
        print("Model checking finished in {0:.3f} seconds.".format(time.time()
                                                                   - start))
        return result
