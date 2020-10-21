from modules.modelchecker.statespace import *
from modules.assertiongenerators.cocosim.declarationgenerator import *


class StateSpaceGenerator:
    def __init__(self):
        self.__initialSetup()

    def __initialSetup(self):
        self.fundamentalSampleTime = 0
        self.simulationTimeHorizon = 0
        self.blocksStepSize = dict()
        self.blocksForTransformation = []
        self.assertionTemplates = dict()

    def __calculateBlockStepSize(self, blockSampleTime, simulationStepSize):
        blockStepSize = (blockSampleTime / simulationStepSize)
        if self.fundamentalSampleTime > 0:
            blockStepSize = (blockSampleTime / self.fundamentalSampleTime)
        intvalue = int(blockStepSize)
        return intvalue

    def __calculateStepSizeForAllBlocks(self, allBlocks, simulationStepSize):
        blocksStepSize = dict()
        for block in allBlocks:
            blockid = block.get("blockid")
            blockSampleTime = block.get("sampletime", 0)
            blocksStepSize[blockid] = self.__calculateBlockStepSize(
                blockSampleTime, simulationStepSize)
        return blocksStepSize

    def __calculateSimulationHorizon(self, simulationStepSize, fundamentalSampleTime,
                                     simulationDuration):
        simulationHorizon = (simulationDuration / simulationStepSize)
        if fundamentalSampleTime > 0:
            simulationHorizon = (simulationDuration / fundamentalSampleTime)
        return int(simulationHorizon)

    def __prepareDeclarationsForVariables(self, cTable):
        declarationString = ""
        for cTableEntry in cTable:
            declarationString = "{0} \n {1}".format(
                declarationString, DeclarationsGenerator.generateDeclaration(cTableEntry))
        return declarationString

    def __preprocessModel(self, sModel, simulationStepSize, simulationDuration):
        self.fundamentalSampleTime = sModel.calculateFundamentalSampleTime()
        self.simulationTimeHorizon = self.__calculateSimulationHorizon(simulationStepSize,
                                                                       self.fundamentalSampleTime, simulationDuration)
        self.blocksStepSize = self.__calculateStepSizeForAllBlocks(sModel.getAllBlocks(),
                                                                   simulationStepSize)
        self.blocksForTransformation = sModel.packAllBlocksForTransformation()
        for block in self.blocksForTransformation:
            blockid = block.get("blockid")
            # self.assertionTemplates[blockid] = AssertionTemplateGenerator.generateBlockAssertion(
            #    block)

    def __generateBlockSymbolicState(self, block, step):
        blockStepSize = self.blocksStepSize.get(block.get("blockid"))
        #symbolicState = AssertionInstantiator.instantiateAssertion(block, step, blockStepSize)
        return symbolicState

    def __generateSymbolicState(self, step):
        symbolicState = []
        for block in self.blocksForTransformation:
            symbolicState.append(self.__generateBlockSymbolicState(block, step))
        return symbolicState

    def __generateModelStateSpace(self, sModel):
        declaration = ""
        simulationTimeHorizon = self.simulationTimeHorizon
        print("Simulation time horizon is: {0}".format(simulationTimeHorizon))
        declarationTemplate = self.__prepareDeclarationsForVariables(sModel.getModelVariables())
        #declarationTemplate = self.__prepareDeclarationsForVariables('')
        sSpace = StateSpace()
        for step in range(0, simulationTimeHorizon):
            declaration += declarationTemplate.format(step)
            state = self.__generateSymbolicState(step)
            sSpace.addState(step, state)
        sSpace.setDeclarations(declaration)
        return sSpace

    def generateStateSpace(self, sModel, simulationStepSize, simulationDuration):
        self.__preprocessModel(sModel, simulationStepSize, simulationDuration)
        return self.__generateModelStateSpace(sModel)
