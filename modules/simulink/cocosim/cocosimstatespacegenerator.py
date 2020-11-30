from modules.simulink.cocosim.cocosimstatespace import *
from modules.assertiongenerators.cocosim.assertiongenerator import *
from modules.assertiongenerators.cocosim.declarationgenerator import *
from modules.assertiongenerators.cocosim.assertioninstantiator import *
import modules.utils.utils as cUtils
import time

class StateSpaceGenerator:
    def __init__(self):
        self.__initialSetup()

    def __initialSetup(self):
        pass

    def __generateBlockSymbolicState(self, blockPackage, step, cTable):
        blockStepSize   = self.__computeBlockStepSize(blockPackage)
        blockPackage_modified = self.__updateSignalTypes(blockPackage, cTable)
        blockAssertion  = AssertionInstantiator.instantiateAssertion(blockPackage, step, blockStepSize)
        return blockAssertion

    def __computeBlockStepSize(self, blockPackage):
        blockSampleTime = blockPackage.get("sampleTime", -1)
        if blockSampleTime == -1:
            blockStepSize = 1;
        else:
            blockStepSize = blockSampleTime / self.fundamentalSampleTime;
        return blockStepSize

    def __updateSignalTypes(self, blockPackage, cTable):
        signal_inputs = blockPackage.get("inputSignals")

        for signal_input in signal_inputs:
            signal_name = signal_input.get("SignalName", "")
            for entry in cTable:
                if cUtils.compareStringsIgnoreCase(entry["SignalName"], signal_name):
                    signal_input["SignalType"] = entry["SignalType"]
                    break

        return blockPackage

    def __generateSymbolicState(self, step, cTable):
        # this function calls the function above and creates assertions for
        # all simulink blocks for that step
        symbolicState = []
        for block in self.blocksForTransformation:
            # all blocks except statflow
            if not (cUtils.compareStringsIgnoreCase(block.get("BlockType"), "SubSystem") and len(block.get("StateflowContent", {})) > 0):
                tmp_symbolicState = self.__generateBlockSymbolicState(block, step, cTable)
                for tmp_state in tmp_symbolicState:
                    symbolicState.append(tmp_state)
        return symbolicState

    def __generateModelStateSpace(self, sModel, totalSteps):
        # this function works only for Simulink without Stateflow
        declarations = ""
        sSpace = StateSpace()
        # declarations are fixed
        self.blocksForTransformation = sModel.packAllBlocksForTransformation()
        self.fundamentalSampleTime   = sModel.getFundamentalSampleTime()
        cTable = sModel.getConnectionTable()
        declarationsTemplate = DeclarationsGenerator.generateDeclarations(sModel, cTable)
        for step in range(0, totalSteps+1): # One extra for stateflow
            declarations = "{0}\n{1}".format(
                declarations, declarationsTemplate.format(step))
            state = self.__generateSymbolicState(step, cTable)
            sSpace.addState(step, state)
        sSpace.setDeclarations(declarations)
        return sSpace

    def generateStateSpace(self, sModel, totalSteps):
        #self.__preprocessModel(sModel)
        return self.__generateModelStateSpace(sModel, totalSteps)
