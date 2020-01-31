from modules.simulink.transformation.parsedsimulinkblock import *
from modules.simulink.transformation.parsedsimulinkline import *
import copy


class ParsedSimulinkBlock:
    def __init__(self):
        self.blockid = ""
        self.name = ""
        self.blocktype = ""
        self.sampletime = -1
        self.parameters = {}
        self.predecessors = []  # list of parsedSimulinkLine

    def getBlockId(self):
        return self.blockid

    def setBlockId(self, blockId):
        self.blockid = blockId

    def setName(self, name):
        self.name = name

    def getName(self):
        return self.name

    def getBlockType(self):
        return self.blocktype

    def addParameter(self, parameterName, parameterValue):
        self[parameterName] = parameterValue

    def getParameter(self, parameterName):
        return self[parameterName]

    def addPredecessor(self, parsedSimulinkBlock):
        self.predecessors.append(parsedSimulinkBlock)

    def getPredecessors(self):
        return self.predecessors

    def setParameters(self, parameters):
        self.parameters = parameters

    def getParameters(self):
        return self.parameters
