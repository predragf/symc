import modules.utils.utils as cUtils
import re


class SListManager:

    @staticmethod
    def loadSList(pathToSList):
        slist = {}
        try:
            slistFile = cUtils.openFile(pathToSList)
            for line in slistFile:
                lineContents = re.split("\s", line)
                lineContents_concat = " ".join(lineContents[2:])
                blockId = lineContents_concat.replace('"', "").strip()
                slist[blockId] = lineContents[0]
        except Exception as e:
            print(e)
            slist = {}
        return slist

    @staticmethod
    def flattenSList(cocoSimModel, pathToFile):
        sModelTemp = cocoSimModel.getModelJSON().copy()
        modelObject = {}
        modelObject["simulinkmodel"] = sModelTemp
        jsonManager.saveJsonToFile(modelObject, pathToFile)
