import json
import modules.utils.jsonmanager as jsonManager
from modules.simulink.cocosimmodel import CoCoSimModel


class CoCoSimModelManager:

    @staticmethod
    def loadModel(pathToModel):
        jsonData = jsonManager.openAndLoadJson(pathToModel)
        return CoCoSimModel(jsonData)

    @staticmethod
    def saveModel(cocoSimModel, pathToFile):
        sModelTemp = cocoSimModel.getModelJSON().copy()
        modelObject = {}
        modelObject["simulinkmodel"] = sModelTemp
        jsonManager.saveJsonToFile(modelObject, pathToFile)
