from modules.simulink.cocosim.cocosimstatespace import *
from modules.assertiongenerators.cocosim.assertiongenerator import *
from modules.assertiongenerators.cocosim.declarationgenerator import *
from modules.assertiongenerators.cocosim.assertioninstantiator import *


class StateSpaceGenerator:
    def __init__(self):
        self.__initialSetup()

    def __initialSetup(self):
        pass

    def __generateBlockSymbolicState(self, blockPackage, step):
        blockAssertion = AssertionInstantiator.instantiateAssertion(block, step, blockStepSize)
        return blockAssertion

    def __generateSymbolicState(self, step):
        # this function calls the function above and creates assertions for
        # all simulink blocks for that step
        symbolicState = []
        for block in self.blocksForTransformation:
            # all blocks except statflow
            if not (cUtils.compareStringsIgnoreCase(itm.get("BlockType"), "SubSystem") and len(itm.get("StateflowContent", {})) > 0):
                symbolicState.append(self.__generateBlockSymbolicState(block, step))
        return symbolicState

    def __generateModelStateSpace(self, sModel, totalSteps):
        # this function works only for Simulink without Stateflow
        declarations = ""
        sSpace = StateSpace()
        # declarations are fixed
        declarationsTemplate = DeclarationsGenerator.generateDeclarations(
            sModel.getConnectionTable())
        for step in range(0, totalSteps):
            declarations = "{0}\n{1}".format(
                declarations, declarationsTemplate.format(step))
            state = self.__generateSymbolicState(step)
            sSpace.addState(step, state)
        sSpace.setDeclarations(declarations)
        return sSpace

    def generateStateSpace(self, sModel, totalSteps):
        #self.__preprocessModel(sModel, simulationStepSize, simulationDuration)
        return self.__generateModelStateSpace(sModel, totalSteps)
