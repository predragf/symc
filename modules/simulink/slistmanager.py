import modules.utils.utils as cUtils
import re


class SListManager:

    @staticmethod
    def loadSList(pathToSList):
        slistFile = cUtils.openFile(pathToSList)
        slist = {}
        for line in slistFile:
            lineContents = re.split("\s", line)
            slist[lineContents[2].replace('"', "")] = lineContents[0]
        return slist

    @staticmethod
    def flattenSList(cocoSimModel, pathToFile):
        sModelTemp = cocoSimModel.getModelJSON().copy()
        modelObject = {}
        modelObject["simulinkmodel"] = sModelTemp
        jsonManager.saveJsonToFile(modelObject, pathToFile)
