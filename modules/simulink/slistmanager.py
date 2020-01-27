import modules.utils.utils as cUtils
import re


class SListManager:

    @staticmethod
    def loadSList(pathToSList):
        slistFile = cUtils.openFile(pathToSList)
        slist = {}
        for line in slistFile:
            lineContents = re.split('\s\(|\s"', line)
            blockId = lineContents[2].replace('"', "").strip()
            execOrder = lineContents[0]
            slist[blockId] = execOrder
        return slist

    @staticmethod
    def flattenSList(cocoSimModel, pathToFile):
        sModelTemp = cocoSimModel.getModelJSON().copy()
        modelObject = {}
        modelObject["simulinkmodel"] = sModelTemp
        jsonManager.saveJsonToFile(modelObject, pathToFile)
