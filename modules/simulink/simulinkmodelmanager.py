from modules.simulink.simulinkmodel import *
import modules.utils.jsonmanager as jsonManager

def loadModel(pathToModel):
    jsonData = jsonManager.openAndLoadJson(pathToModel)
    return SimulinkModel(jsonData)

def saveModel(sModel, pathToFile):
    sModelTemp = sModel.getModelJSON().copy();
    #remove the additional data
    sModelTemp.pop("signalvariables")
    modelObject = {}
    modelObject["simulinkmodel"] = sModelTemp
    jsonManager.saveJsonToFile(modelObject, pathToFile)
