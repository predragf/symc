from modules.simulink.simulinkmodel import *
import modules.utils.jsonmanager as jsonManager

def loadModel(pathToModel):
    jsonData = jsonManager.openAndLoadJson(pathToModel)
    return SimulinkModel(jsonData)
