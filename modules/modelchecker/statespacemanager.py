import modules.utils.jsonmanager as jsonManager
from modules.modelchecker.statespace import *

class StateSpaceManager:
    @staticmethod
    def saveStateSpaceToFile(stateSpace, fileName):
        jsonManager.saveJsonToFile(stateSpace.getStateSpace(), fileName)

    @staticmethod
    def loadStateSpaceFromFile(fileName):
        stateSpaceJsonObject = jsonManager.openAndLoadJson(fileName)
        return StateSpace(stateSpaceJsonObject)
