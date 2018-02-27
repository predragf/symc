from z3 import *
from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelloader import *
from modules.modelchecker.statespace import *
from modules.modelchecker.statespacegenerator import *
from modules.modelchecker.statespacemanager import *
from modules.routinegenerators.routinegenerator import *
from modules.assertiongenerators.assertiongenerator import *
from modules.utils.gcd import *
import time

class SiMC:
    def __init__(self):
        pass

    def __createGoal(self):
        goal = Goal()
        return goal

    def __createSolver(self):
        solver = Solver()
        solver.set("mbqi", True)
        solver.set("unsat-core", True)
        solver.set("mbqi.max_iterations", 100)
        return solver

    def __createAndInitializeSolver(self, _goal, useTactics=False):
        solver = self.__createSolver()
        if useTactics:
            tactic = Then("smt", "elim-term-ite", "elim-and")
            parsedAssertions = tactic(_goal).as_expr()
            solver.add(parsedAssertions)
        else:
            solver.add(_goal)
        return solver

    def __obtainModelStateSpace(self, pathToModel, stepsize,
                                saveStateSpace=False):
        sModel = loadModel(pathToModel)
        ssg = StateSpaceGenerator()
        simulationDuration = sModel.getSymbolicFixedPoint() * 2
        stateSpace = ssg.generateStateSpace(sModel, stepsize, simulationDuration)
        if saveStateSpace:
            StateSpaceManager.saveStateSpaceToFile(stateSpace,
            "./models/{0}{1}.ss".format(sModel.getModelName(), simulationDuration))
        return stateSpace;

    def __generateScriptForChecking(self, smtScript):
        return z3.parse_smt2_string(smtScript)

    def __createAndPopulateSolver(self, pathToModel, stepsize, assumptions):
        stateSpaceForChecking = self.__obtainModelStateSpace(pathToModel,
                                                stepsize)
        stateSpaceSMT = "{0} \n {1}".format(
                                    stateSpaceForChecking.genenrateSMT2Script(),
                                    "\n".join(assumptions))
        goal = self.__createGoal()
        goal.add(self.__generateScriptForChecking(stateSpaceSMT))
        solver = self.__createAndInitializeSolver(goal)
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

    def checkModel(self, pathToModel, stepsize, assumptions=[]):
        start = time.time()
        print("Creating model started at {0}".format(time.ctime()))
        solver = self.__createAndPopulateSolver(pathToModel, stepsize, assumptions)
        end = time.time()
        print("Creating model finished. It took {0} seconds.".format(end - start))
        print("Model checking started.")
        start = time.time()
        result = self.__executeSolver(solver)
        print("Model checking finished. It took {0} seconds.".format(time.time() - start))
        return result
