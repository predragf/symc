from modules.simulink.simulinkmodel import *
import math
import sys

def calculateCT(simulinkModel, blockid):
    return calculateCTRecursively(simulinkModel, blockid, [])

def calculateCTRecursively(simulinkModel, blockid, visitedBlocks):
    requiredBlock = simulinkModel.getBlockById(blockid)
    requiredBlockSampleTime = requiredBlock.get("sampletime", "1")
    predecessors = simulinkModel.getBlockPredecessors(blockid)
    requiredBlockSampleTime = int(requiredBlockSampleTime)
    result = 100000
    if requiredBlockSampleTime < 1:
        requiredBlockSampleTime = 1
    if not predecessors: #block is the first in the composition
        result = requiredBlockSampleTime
    else:
        predecessorsCTs = []
        visitedBlocks.append(blockid)
        for predecessor in predecessors:
            predecessorId = predecessor.get("blockid")
            if predecessorId in visitedBlocks:
                return sys.maxint
            calculatedCT = calculateCTRecursively(simulinkModel, predecessorId, visitedBlocks)
            predecessorsCTs.append(calculatedCT)
        predecessorsCTs.sort(reverse=True)
        maxValue = predecessorsCTs[0]
        ceiling = int(math.ceil(float(maxValue)/int(requiredBlockSampleTime)))        
        result = int(ceiling * requiredBlockSampleTime)
    return result
