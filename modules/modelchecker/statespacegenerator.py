from modules.modelchecker.statespace import *
from modules.assertiongenerators.assertiongenerator import *

class StateSpaceGenerator:
    def __init__(self):
        pass


    def __calculateSimulationHorizon(self, simulationStepSize, fundamentalSampleTime,
                                                            simulationDuration):
        simulationHorizon = (simulationDuration / simulationStepSize)
        if fundamentalSampleTime > 0:
            simulationHorizon = (simulationDuration / fundamentalSampleTime)
        return int(simulationHorizon)

    def __calculateBlockStepSize(self, blockSampleTime, fundamentalSampleTime,
                                                            simulationStepSize):
        blockStepSize = (blockSampleTime / simulationStepSize)
        if fundamentalSampleTime > 0:
            blockStepSize = (blockSampleTime / fundamentalSampleTime)
        return int(blockStepSize)

    def __generateSymbolicState(self, sBlockPackage, step):
        ag = AssertionGenerator()
        blockType = sBlockPackage["blocktype"]
        result = "";

        if blockType == "sum":
            result = ag.sum(sBlockPackage, step)
        elif blockType == "gain":
            result = ag.gain(sBlockPackage, step)
        elif blockType == "abs":
            result = ag.abs(sBlockPackage, step)
        elif blockType == "constant":
            result = ag.constant(sBlockPackage, step)
        elif blockType == "switch":
            result = ag.switch(sBlockPackage, step)
        elif blockType == "subtract":
            result = ag.subtract(sBlockPackage, step)
        elif blockType == "relationaloperator":
            result = ag.relational(sBlockPackage, step)
        elif blockType == "saturate":
            result = ag.saturate(sBlockPackage, step)

        return result;

    def generateSignalStateSpace(self, sBlockPackage, simulationStepSize,
                                fundamentalSampleTime, simulationTimeHorizon):
        #for continuous blocks this will be 0, meaning that a new
        #output must be computed at each simulation step
        statespace = []
        blockSampleTime = sBlockPackage["sampletime"];
        blockStepSize = self.__calculateBlockStepSize(blockSampleTime,
                                    fundamentalSampleTime, simulationStepSize)
        statespace.append(self.__generateSymbolicState(sBlockPackage, 0))
        for step in range(1, simulationTimeHorizon):
            if ((blockStepSize == 0) or ((step % blockStepSize) == 0)):
                statespace.append(self.__generateSymbolicState(sBlockPackage,
                                                                step))
            else:
                equalToPrevious = "(= {0}_{1} {0}_{2})"
                signalname = sBlockPackage["signalname"]
                statespace.append(equalToPrevious.format(signalname,
                                                        step, step - 1))
        return statespace

    def __generateModelStateSpace(self, sModel, simulationStepSize,
                                    fundamentalSampleTime, simulationTimeHorizon):
        simulinkModelStateSpace = StateSpace()
        allBlocks = sModel.getAllBlocks()
        for block in allBlocks:
            blockpackage = sModel.packBlockForTransformation(block["blockid"])
            signalStateSpace = self.generateSignalStateSpace(blockpackage,
                                    simulationStepSize, fundamentalSampleTime,
                                    simulationTimeHorizon)
            simulinkModelStateSpace.addTrace(block["blockid"], signalStateSpace)
        return simulinkModelStateSpace

    def generateStateSpace(self, sModel, simulationStepSize, simuationDuration):
        fundamentalSampleTime = sModel.calculateFundamentalSampleTime()
        simulationTimeHorizon = self.__calculateSimulationHorizon(simulationStepSize,
                                        fundamentalSampleTime, simuationDuration)
        return self.__generateModelStateSpace(sModel, simulationStepSize,
                                fundamentalSampleTime, simulationTimeHorizon)
