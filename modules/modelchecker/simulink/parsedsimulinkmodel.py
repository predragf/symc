
class ParsedSimulinkModel:
    def __init__(self):
        self.modelname = ""
        self.fundamentalsampletime = ""
        self.blocks = []  # this should be a list of ParsedSimulinkBlock
        # parameters is an object that holds the set of parameters for the simulink model that we cannot account for at this time (so basically this means that the developer can put any parameter and use it later in the transformation)
        self.parameters = {}

    def addBlock(self, parsedSimulinkBlock):
        self.blocks.append(parsedSimulinkBlock)

    def addParameter(self, parameterName, parameterValue):
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
