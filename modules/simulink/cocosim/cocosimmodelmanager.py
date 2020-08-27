import modules.utils.jsonmanager as jsonManager
from modules.simulink.cocosim.cocosimmodel import CoCoSimModel
from modules.simulink.slistmanager import SListManager


def loadModel(pathToModel, pathToSlist, _configuration={}):
    jsonData = jsonManager.openAndLoadJson(pathToModel)
    slist = SListManager.loadSList(pathToSlist)
    return CoCoSimModel(jsonData, slist, _configuration)


def saveModel(cocoSimModel, pathToFile):
    sModelTemp = cocoSimModel.getModelJSON().copy()
    modelObject = {}
    modelObject["simulinkmodel"] = sModelTemp
    jsonManager.saveJsonToFile(modelObject, pathToFile)
