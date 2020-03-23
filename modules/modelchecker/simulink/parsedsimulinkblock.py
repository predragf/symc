from modules.modelchecker.simulink.parsedsimulinkblock import *
from modules.modelchecker.simulink.parsedsimulinkline import *
import copy

# TODO: write the complete documentation for the class


class ParsedSimulinkBlock:
    def __init__(self):
        self.blockid = ""
        self.name = ""
        self.blocktype = ""
        self.sampletime = -1
        self.parameters = {}
        self.predecessors = []  # list of parsedSimulinkLine
        self.simulinkmodel = None

    def getBlockId(self):
        """Short summary.

        Returns block identifier
        -------
        type
            String

        """
        return self.blockid

    def setBlockId(self, blockId):
        """Short summary.

        Parameters
        ----------
        blockId : String
            blockId is the unique identifier for the block.

        Returns
        -------
        type
            void.

        """
        self.blockid = blockId

    def setName(self, name):
        self.name = name

    def getName(self):
        return self.name

    def getBlockType(self):
        return self.blocktype

    def setBlockType(self, blockType):
        self.blocktype = blockType

    def setParameter(self, parameterName, parameterValue):
        self[parameterName] = parameterValue

    def getParameter(self, parameterName):
        return self[parameterName]

    def addPredecessor(self, parsedSimulinkLine):
        self.predecessors.append(parsedSimulinkLine)

    def getPredecessors(self):
        return self.predecessors

    def setParameters(self, parameters):
        self.parameters = parameters

    def getParameters(self):
        return self.parameters

    def setSimulinkModel(self, simulinkModel):
        self.simulinkmodel = simulinkModel

    def getSimulinkModel(self):
        return self.simulinkmodel
