import json
from modules.simulink.simulinkmodel import *

def openAndLoadJson(pathToBlockListFile):
    #open file for reading only
    file = open(pathToBlockListFile, "r");
    blockFileListAsString = file.read()
    blockListJson = json.loads(blockFileListAsString)
    return blockListJson

def loadModel(pathToModel):
    jsonData = openAndLoadJson(pathToModel)
    return SimulinkModel(jsonData)
