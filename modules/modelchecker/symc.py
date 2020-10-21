from z3 import *
from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelmanager import *
from modules.modelchecker.statespace import *
from modules.modelchecker.statespacegenerator import *
from modules.modelchecker.statespacemanager import *
from modules.routinegenerators.routinegenerator import *
from modules.assertiongenerators.assertiongenerator import *
from modules.utils.gcd import *
from modules.utils.utils import *
import time


class SyMC:

    def __init__(self, _configuration=dict()):
        self.__configure(_configuration)

    def __configure(self, _configuration=dict()):
        _wceCoeficient = 2
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

    def __obtainModelStateSpace(self, sModel, stepsize):
        ssg = StateSpaceGenerator()
        # the size of the simulation, that is the exexution traces is
        # calculated as the symbolic fixed point of the model multiplied by
        # the WCE coefficient.
        stateSpace = StateSpace()
        stateSpace = ssg.generateStateSpace(sModel, stepsize,
                                            self.executionLenght)
        if self.saveStateSpace:
            StateSpaceManager.saveStateSpaceToFile(stateSpace,
                                                   "./models/exec/{0}{1}.ss"
                                                   .format(sModel
                                                           .getModelName(),
                                                           self.executionLenght
                                                           ))
        return stateSpace

    def __generateScriptForChecking(self, smtScript):
        parsedSMTScript = ""
        try:
            parsedSMTScript = z3.parse_smt2_string(smtScript)
        except Exception as ex:
            print("Script parsing faild. \n Reason: {0}".format(ex))
            parsedSMTScript = ""
        return parsedSMTScript

    def __constructPathToModel(self, modelname, stepsize):
        return "./models/exec/{0}-{1}.smt2".format(modelname, stepsize)

    def __saveExistingSMTModel(self, modelname="", stepsize="", _smtModel=""):
        pathToSMTModel = self.__constructPathToModel(modelname, stepsize)
        absolutePathSMTModel = os.path.abspath(pathToSMTModel)
        try:
            print("Script saving in progress ...")
            text_file = openFile(absolutePathSMTModel, "w")
            text_file.write(_smtModel)
            text_file.close()
            print("Script saved.")
        except Exception as ex:
            print("Script saving failed. \n Reason: {0}".format(ex))

    def __loadExistingSMTModel(self, modelname="", stepsize=""):
        existingSmtModel = ""
        pathToSMTModel = self.__constructPathToModel(modelname, stepsize)
        try:
            print("Loading existing model in progress ...")
            with open(pathToSMTModel, 'r') as smtModelFile:
                existingSmtModel = smtModelFile.read()
                print("Existing model loaded.")
        except Exception as ex:
            print("Loading existing model failed. \n Reason: {0}".format(ex))
            existingSmtModel = ""
        return existingSmtModel

    def __generateAssertionsFromProperty(self, property):
        assertions = []
        signalPattern = r'signal_\d+'
        usedSignals = re.findall(signalPattern, property)
        for i in range(0, self.executionLenght):
            assertion = property
            for us in usedSignals:
                assertion = assertion.replace(us, "{0}_{1}".format(us, i))
            assertions.append(assertion)
        return assertions

    def __getSMTScript(self, sModel, stepsize, property):
        baseModel = ""
        if self.reuseExistingModel:
            baseModel = self.__loadExistingSMTModel(sModel.getModelName(), stepsize)
        if baseModel == "":
            stateSpaceForChecking = self.__obtainModelStateSpace(sModel,
                                                                 stepsize)
            baseModel = stateSpaceForChecking.genenrateSMT2Script()
            self.__saveExistingSMTModel(sModel.getModelName(), stepsize, baseModel)
            assertions = self.__generateAssertionsFromProperty(property)
            print assertions
        return "{0} \n {1}".format(baseModel, "\n".join(assertions))

    def __createAndPopulateSolver(self, pathToModel, stepsize, property):
        sModel = loadModel(pathToModel)
        self.executionLenght = sModel.getSymbolicFixedPoint() * 2
        smtModel = self.__getSMTScript(sModel, stepsize, property)
        goal = self.__createGoal()
        smtScript = self.__generateScriptForChecking(smtModel)
        goal.add(smtScript)
        solver = self.__createAndInitializeSolver(goal)
        return solver

    def configure(self, _configuration):
        if _configuration is None:
            _configuration = dict()
        self.__configure(_configuration)

    def checkModel(self, pathToModel, stepsize, property=""):
        start = time.time()
        print("Model verification started at {0}".format(
            time.strftime("%H:%M:%S")))
        print("Creating model ...")
        solver = self.__createAndPopulateSolver(pathToModel, stepsize,
                                                property)
        print("Creating model finished in {0:.3f} seconds.".format(time.time()
                                                                   - start))
        print("Model checking ...")
        start = time.time()
        result = self.__executeSolver(solver)
        print("Model checking finished in {0:.3f} seconds.".format(time.time()
                                                                   - start))
        return result
