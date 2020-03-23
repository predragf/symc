
class ParsedSimulinkModel:
    def __init__(self):
        self.modelname = ""
        self.fundamentalsampletime = ""
        self.blocks = []  # this should be a list of ParsedSimulinkBlock
        self.parameters = {}

    def addBlock(self, parsedSimulinkBlock):
        parsedSimulinkBlock.setSimulinkModel(self)
        self.blocks.append(parsedSimulinkBlock)

    def getBlock(self, blockId):
        return next(block for block in self.blocks if block.getBlockId() == blockId)

    def getAllBlocks(self):
        return self.blocks

    def setParameter(self, parameterName, parameterValue):
        self.parameters[parameterName] = parameterValue

    def getParameter(self, parameterName):
        return self.parameters.get(parameterName, None)

    def setModelName(self, modelName):
        self.modelname = modelName

    def getModelName(self):
        return self.modelname

    def setFundamentalSampleTime(self, fundamentalSampleTime):
        self.fundamentalsampletime = fundamentalSampleTime

    def getFundamentalSampleTime(self):
        return self.fundamentalsampletime
