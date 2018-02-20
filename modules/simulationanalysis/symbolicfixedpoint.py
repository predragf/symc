import json

class SymbolicFixedPoint:
    @staticmethod
    def calculateFixedPoint(sModel):
        allBlocks = sModel.getAllBlocks()[:]
        allBlocks.sort(key=lambda x: x.get("executionorder", 1000000))
        


    @staticmethod
    def __getAllBlocksWithOutputs(sModel):
        _allConnections = sModel.getAllConnections()
        blockswithouts = set()
        for connection in _allConnections:
            blockswithouts.add(connection.get("sourceblockid"))
        return blockswithouts

    @staticmethod
    def getAllBlockIds(sModel):
        allIds = set()
        for blk in sModel.getAllBlocks():
            allIds.add(blk.get("blockid"))
        return allIds

    @staticmethod
    def getBlockIdsWithNoOutputs(sModel):
        blocksWithOuts = SymbolicFixedPoint.__getAllBlocksWithOutputs(sModel)
        allBlockIds = SymbolicFixedPoint.getAllBlockIds(sModel)
        return blocksWithOuts - allBlockIds
