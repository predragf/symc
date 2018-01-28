from modules.modelchecker.statespace import *
class StateSpaceGenerator:
    def __init__(self):
        pass

    def __calculateSimulationHorizon(self, simulationStepSize, simulationDuration):
        floating = simulationDuration / simulationStepSize
        return int(floating)

    def __calculateBlockStepSize(self, simulationStepSize, blockStepSize):
        floating = blockStepSize / simulationStepSize
        return int(floating)

    def __generateSymbolicState(self, sBlockPackage, step):
        return "{0}_{3} = {1}({2})".format(sBlockPackage["signalname"], sBlockPackage["blockroutine"], sBlockPackage["inputs"], step)

    def generateSignalStateSpace(self, sBlockPackage, simulationStepSize, simulationTimeHorizon):
        #for continuous blocks this will be 0, meaning that a new
        #output must be computed at each simulation step
        statespace = []
        blockSampleTime = sBlockPackage["sampletime"];
        blockStepSize = self.__calculateBlockStepSize(simulationStepSize, blockSampleTime)
        statespace.append(self.__generateSymbolicState(sBlockPackage, 0))
        for step in range(1, simulationTimeHorizon):

            if ((blockStepSize == 0) or ((step % blockStepSize) == 0)):
                statespace.append(self.__generateSymbolicState(sBlockPackage, step))
            else:
                statespace.append(statespace[step - 1])
        return statespace

    def generateStateSpace(self, sModel, simulationStepSize, simuationDuration):
        simulinkModelStateSpace = StateSpace()
        simulationTimeHorizon = self.__calculateSimulationHorizon(simulationStepSize, simuationDuration)
        print(simulationTimeHorizon)
        allBlocks = sModel.getAllBlocks()

        for block in allBlocks:
            blockpackage = sModel.packBlockForTransformation(block["blockid"])
            signalStateSpace = self.generateSignalStateSpace(blockpackage, simulationStepSize, simulationTimeHorizon)
            simulinkModelStateSpace.addTrace(block["blockid"], signalStateSpace)

        return simulinkModelStateSpace
