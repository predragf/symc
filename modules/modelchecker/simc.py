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

    def __createSolver(self, _goal):
        z3.set_option(rational_to_decimal=True)
        tactic = Then("simplify", 'qe')
        solver = Solver()
        solver.add(tactic(_goal).as_expr())
        return solver

    def __obtainModelStateSpace(self, pathToModel, stepsize, simulationDuration):
        sModel = loadModel(pathToModel)
        ssg = StateSpaceGenerator()
        stateSpace = ssg.generateStateSpace(sModel, stepsize, simulationDuration)
        StateSpaceManager.saveStateSpaceToFile(stateSpace, "./models/{0}{1}.ss".format(
                        sModel.getModelName(), simulationDuration))
        return stateSpace;

    def __generateScriptForChecking(self, smtScript):
        return z3.parse_smt2_string(smtScript)

    def __createAndPopulateSolver(self, pathToModel, stepsize, simulationDuration,
                                    assumptions):
        stateSpaceForChecking = self.__obtainModelStateSpace(pathToModel,
                                                stepsize, simulationDuration)
        stateSpaceSMT = "{0} \n {1}".format(
                                    stateSpaceForChecking.genenrateSMT2Script(),
                                    "\n".join(assumptions))
        goal = self.__createGoal()
        goal.add(self.__generateScriptForChecking(stateSpaceSMT))
        solver = self.__createSolver(goal)        
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

    def checkModel(self, pathToModel, stepsize, simulationDuration, assumptions=[]):
        start = time.time()
        print("Creating model started at {0}".format(time.ctime()))
        solver = self.__createAndPopulateSolver(pathToModel, stepsize,
                                                simulationDuration, assumptions)
        end = time.time()
        print("Creating model finished. It took {0} seconds.".format(end - start))
        print("Model checking started.")
        start = time.time()
        result = self.__executeSolver(solver)
        end = time.time()
        print("Model checking finished. It took {0} seconds.".format(end - start))
        return result