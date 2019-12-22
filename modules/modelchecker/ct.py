import math
import sys


def calculateCT(simulinkModel, blockid):
    return __calculateCTRecursively(simulinkModel, blockid, [])


def __calculateCTRecursively(simulinkModel, blockid, visitedBlocks):
    """
        This function works only for the linear compositions, and
        not for the feedback loops. Should be fixed in the next iteration
    """
    requiredBlock = simulinkModel.getBlockById(blockid)
    requiredBlockSampleTime = requiredBlock.get("sampletime", "1")
    predecessors = simulinkModel.getBlockPredecessors(blockid)
    requiredBlockSampleTime = int(requiredBlockSampleTime)
    result = sys.maxint
    if requiredBlockSampleTime < 1:
        requiredBlockSampleTime = 1
    # block is the first in the composition
    if not predecessors:
        result = requiredBlockSampleTime
    else:
        predecessorsCTs = []
        visitedBlocks.append(blockid)
        for predecessor in predecessors:
            predecessorId = predecessor.get("blockid")
            if predecessorId in visitedBlocks:
                return sys.maxint
            calculatedCT = __calculateCTRecursively(simulinkModel,
                                                    predecessorId,
                                                    visitedBlocks)
            predecessorsCTs.append(calculatedCT)
        predecessorsCTs.sort(reverse=True)
        maxValue = predecessorsCTs[0]
        ceiling = int(math.ceil(float(maxValue)/int(requiredBlockSampleTime)))
        result = int(ceiling * requiredBlockSampleTime)
    return result
