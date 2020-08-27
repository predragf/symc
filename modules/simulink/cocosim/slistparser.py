import re
import modules.utils.utils as cUtils


class SListParser:
    @classmethod
    def __executePattern(self, _row, _pattern):
        result = ""
        matches = re.findall(_pattern, _row)
        if len(matches) > 0:
            result = matches[0]
        return result

    @classmethod
    def __extractIdFromRow(self, _row):
        idPattern = "'(.*?)'"
        return self.__executePattern(_row, idPattern)

    @classmethod
    def __extractExecutionOrderFromRow(self, _row):
        executionOrderPattern = "^([0-9]+:[0-9])+\s"
        return self.__executePattern(_row, executionOrderPattern)

    @classmethod
    def __extractModelName(self, _row):
        modelNamePattern = "simulate(.*)"
        result = self.__executePattern(_row, modelNamePattern)
        return result[1:-1]

    @classmethod
    def __createSortedOrderEntry(self, _row, _parentId):
        result = {}
        result["parentId"] = _parentId.lower().strip()
        result["id"] = self.__extractIdFromRow(_row).lower().strip()
        result["sortedOrderNumber"] = self.__extractExecutionOrderFromRow(_row)
        return result

    @classmethod
    def __openAndProcessSList(self, slistpath):
        slist = []
        modelName = ""
        compositeElementPattern = ".*---- Sorted list for '.*'.*$"
        atomicElementPattern = ".*[0-9]+(:[0-9]+)+.*"
        modelNamePattern = ".*simulate(.*).*"
        currentCompositeNodeId = ""
        with open(slistpath, "r") as sListFile:
            for line in sListFile:
                _row = line.strip()
                if cUtils.compareStringsIgnoreCase(modelName, "") or not cUtils.compareStringsIgnoreCase("", self.__executePattern(_row, modelNamePattern)):
                    modelName = self.__extractModelName(_row)
                    continue
                if not cUtils.compareStringsIgnoreCase("", self.__executePattern(_row, compositeElementPattern)):
                    currentCompositeNodeId = self.__extractIdFromRow(_row)
                    continue
                if not cUtils.compareStringsIgnoreCase("", self.__executePattern(_row, atomicElementPattern)):
                    slist.append(self.__createSortedOrderEntry(_row, currentCompositeNodeId))
                    continue
        return modelName, slist

    @classmethod
    def __processChildren(self, parent, slist):
        for itm in slist:
            if cUtils.compareStringsIgnoreCase(itm["parentId"], parent["id"]):
                itm["sortedOrderNumber"] = "{}:{}".format(
                    parent["sortedOrderNumber"], itm["sortedOrderNumber"])
                self.__processChildren(itm, slist)
        return slist

    @classmethod
    def __orderSList(self, modelName, slist):
        topLevelBlock = next(itm for itm in slist if cUtils.compareStringsIgnoreCase(
            modelName, itm["parentId"]))
        return self.__processChildren(topLevelBlock, slist)

    @classmethod
    def parse(self, _pathtoList):
        slist = []
        modelName = ""
        if not cUtils.compareStringsIgnoreCase("", _pathtoList):
            modelName, slist = self.__openAndProcessSList(_pathtoList)
        return sorted(self.__orderSList(modelName, slist), key=lambda k: k['sortedOrderNumber'])
