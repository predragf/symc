from modules.utils.gcd import *
import modules.utils.utils as cUtils

class SimulinkModel:

    def __init__(self, _simulinkmodeljson):
        self.simulinkModelJson = _simulinkmodeljson.get("simulinkmodel")
        self.simulinkModelJson["signalvariables"] = self.__createVariables()
        self.simulinkModelJson["internalstatevariables"] = self.__createInternalStateVariables()
        self.symbolicFixedPoint = self.__calculateModelFixedPoint()

    def __getLinesFromSameSource(self, _pivot, _allLines):
        samelines = []
        samelines.append(_pivot)
        indexesForPopping = []
        for i in range(0, len(_allLines)):
            if(_allLines[i].get("sourceblockid") == _pivot.get("sourceblockid") and
                _allLines[i].get("sourceportnumber") == _pivot.get("sourceportnumber")):
                indexesForPopping.append(i)
        for itm in reversed(indexesForPopping):
            samelines.append(_allLines.pop(itm))
        return samelines

    def __createVariables(self):
        #get a local copy of all connections
        variables = {}
        allConnections = self.getAllConnections()[:]
        variableIndex = 1
        while(len(allConnections) > 0):
            pivot = allConnections.pop(0)
            samelines = self.__getLinesFromSameSource(pivot, allConnections)
            for line in samelines:
                variables[line.get("name")] = "signal_{0}".format(variableIndex)
            variableIndex = variableIndex + 1

        return variables

    def __createInternalStateVariables(self):
        allBlocks = self.getAllBlocks()
        internalstatevariables = dict()
        internalstatenum = 0
        for blk in allBlocks:
            _blockid = blk.get("blockid")
            _parameters = blk.get("parameters")
            _initialvalue = _parameters.get("initialvalue", "")
            if _initialvalue != "":
                internalstatenum = internalstatenum + 1
                internalstatevariables[_blockid] = "internalstate_{0}".format(internalstatenum)
        return internalstatevariables

    def getAllBlocks(self):
        return self.simulinkModelJson.get("blocks")

    def getAllInputs(self):
        return self.simulinkModelJson.get("inputs")

    def getAllOutputs(self):
        return self.simulinkModelJson.get("outputs")

    def getBlockById(self, blockid):
        result = {}
        allBlocks = self.getAllBlocks()
        for block in allBlocks:
            if block.get("blockid") == blockid:
                result = block
                break
        return result

    def getAllConnections(self):
        return self.simulinkModelJson.get("connections")

    def getSignalVariables(self):
        return self.simulinkModelJson.get("signalvariables")

    def getInternalStateVariables(self):
        return self.simulinkModelJson["internalstatevariables"]

    def getConnectionSignalVariable(self, _lineName):
        allSignalVariables = self.getSignalVariables()
        return allSignalVariables[_lineName]

    def getModelName(self):
        modelName = self.simulinkModelJson.get("modelname")
        if modelName is None:
            modelName = ""
        return modelName

    def getModelJSON(self):
        return self.simulinkModelJson

    def __getBlockConnections(self, blockid, connectionType="all"):
        allconnections = self.getAllConnections()
        blockConnections = []
        for connection in allconnections:
            if (((connectionType == "output" or connectionType == "all") and
                    connection.get("sourceblockid") == blockid)
                or ((connectionType == "input" or connectionType == "all") and
                    connection.get("destinationblockid") == blockid)
                ):
                blockConnections.append(connection)
        return blockConnections

    def __getConnectionByName(self, cName):
        result = None
        for conn in self.getAllConnections():
            if conn.get("name") == cName:
                result = conn
                break
        return result

    def getBlockOutputConnections(self, blockid):
        return self.__getBlockConnections(blockid, "output")

    def getBlockInputConnections(self, blockid):
        return self.__getBlockConnections(blockid, "input")

    def getBlockInputs(self, blockid):
        result = []
        connections = self.getAllConnections()
        for connection in connections:
            if connection.get("destinationblockid") == blockid:
                result.append(connection.copy())
        return result

    def getBlockPredecessors(self, blockid):
        predecessors = []
        modelConnections = self.getAllConnections()
        for connection in modelConnections:
            if connection.get("destinationblockid") == blockid:
                sourceblockid = connection.get("sourceblockid")
                sourceBlock = self.getBlockById(sourceblockid)
                predecessors.append(sourceBlock)
        return predecessors

    def __parseConnection(self, iconn):
        sourceBlock = self.getBlockById(iconn.get("sourceblockid"))
        _input = {}
        _input["connection"] = iconn
        _input["signalvariable"] = self.getConnectionSignalVariable(iconn.get("name"))
        _input["sourceblock"] = sourceBlock
        return _input

    def __createInputs(self, blockid):
        inputconnections = self.getBlockInputConnections(blockid);
        inputs = []
        for iconn in inputconnections:
            inputs.append(self.__parseConnection(iconn))
        return inputs

    def packBlockForTransformation(self, blockid):
        blockForTransformation = self.getBlockById(blockid).copy()
        outConns = self.getBlockOutputConnections(blockid)
        blockForTransformation["inputs"] = self.__createInputs(blockid)
        blockForTransformation["internalstatevariable"] = self.simulinkModelJson["internalstatevariables"].get(blockid, "")
        if len(outConns) > 0:
            signalname = outConns[0].get("name")
            blockForTransformation["signalname"] = signalname
            blockForTransformation["signalvariable"] = self.getSignalVariables().get(signalname)
        else:
            blockForTransformation["signalname"] = ""

        return blockForTransformation

    def packAllBlocksForTransformation(self):
        allBlocksPacked = []
        allBlocks = self.getAllBlocks()
        for block in allBlocks:
            blockid = block.get("blockid")
            blockPackage = self.packBlockForTransformation(blockid)
            allBlocksPacked.append(blockPackage)
        return allBlocksPacked

    def calculateFundamentalSampleTime(self):
        allBlocks = self.getAllBlocks()
        sampletimes = set()
        for block in allBlocks:
            ts = block.get("sampletime")
            if ts == 0:
                '''-1 denotes that there is at least one continuous-time
                block which means that we must construct the complete state space
                '''
                return -1
            else:
                sampletimes.add(ts)
        return gcdList(list(sampletimes))

    def getModelVariables(self):
        modelVariables = self.getSignalVariables().values()
        modelVariables.extend(self.getInternalStateVariables().values())
        noDuplicates = set(modelVariables)
        return list(noDuplicates)

    def __getBlockDataDependencyChain(self, blockid, direction="backward", visitedblocks=set()):
        if blockid not in visitedblocks:
            visitedblocks.add(blockid)
            blocksForExamination = ""
            if direction == "backward":
                connections = self.__getBlockConnections(blockid, "input")
                blocksForExamination = "sourceblockid"
            else:
                connections = self.__getBlockConnections(blockid, "ouput")
                blocksForExamination = "destinationblockid"
            for bConn in connections:
                visitedblocks = self.__getBlockDataDependencyChain(
                                bConn.get(blocksForExamination), direction, visitedblocks)
        return visitedblocks

    def getBackwardBlockDataDependencyChain(self, blockid):
        return self.__getBlockDataDependencyChain(blockid, "backward")

    def getForwardBlockDataDependencyChain(self, blockid):
        return self.__getBlockDataDependencyChain(blockid, "forward")

    def __determineFixedPoint(self, outTs, predecessorsTs):
        fixedPoint = outTs
        for predecessorTs in predecessorsTs:
            if(predecessorTs < outTs):
                continue
            if(predecessorTs >= outTs):
                interFP = (int(predecessorTs / outTs) +
                                            (predecessorTs % outTs > 0)) * outTs
                fixedPoint = max(fixedPoint, interFP)
        return fixedPoint

    def __calculateBlockSymbolicFixedPointResursively(self, sBlock, predecessors):
        predecessorsFixedPoints = []
        blockSampleTime = sBlock.get("sampletime", "0")
        for prd in predecessors:
            predecessorsFixedPoints.append(self.__calculateBlockSymbolicFixedPoint(prd))
        return self.__determineFixedPoint(blockSampleTime, predecessorsFixedPoints)

    def __calculateBlockSymbolicFixedPoint(self, sBlock):
        sfp = cUtils.to_int(sBlock.get("symbolicfixedpoint", "-1"))
        if sfp > -1:
            return sfp
        _blockInputs = self.getBlockPredecessors(sBlock.get("blockid"))
        blockExecutionOrderId = cUtils.to_int(sBlock.get("executionorder", ""))
        blockSymbolicFixedPoint = cUtils.to_int(sBlock.get("sampletime", "0"))
        predecessorsForProcessing = []
        for blk in self.getBlockPredecessors(sBlock.get("blockid")):
            execId = cUtils.to_int(blk.get("executionorder", ""))
            if execId < blockExecutionOrderId:
                predecessorsForProcessing.append(blk)
        if(len(predecessorsForProcessing) > 0 and blockSymbolicFixedPoint != 0):
            blockSymbolicFixedPoint = self.__calculateBlockSymbolicFixedPointResursively(sBlock,
                                                                predecessorsForProcessing)
        sBlock["symbolicfixedpoint"] = blockSymbolicFixedPoint
        return blockSymbolicFixedPoint

    def __getLoopCreatingConnections(self, sBlock):
        loopCreatingConnections = []
        blockExecutionOrder = cUtils.to_int(sBlock.get("executionorder"))
        outlines = self.getBlockOutputConnections(sBlock.get("blockid"))
        for outline in outlines:
            successorBlock = self.getBlockById(outline.get("destinationblockid"))
            successorExecutionOrder = cUtils.to_int(successorBlock.get("executionorder"))
            if(successorExecutionOrder < blockExecutionOrder):
                loopCreatingConnections.append(outline)
        return loopCreatingConnections[:]

    def __buildLoops(self, currentBlockId, loopEndBlockId, loops):
        result = []
        if len(loops) < 1:
            return result
        elif loopEndBlockId == currentBlockId:
            for loop in loops:
                loop.append(currentBlockId)
            result = loops
        else:
            outlines = self.getBlockOutputConnections(currentBlockId)
            loopsForParsing = []
            for outLine in outlines:
                for loop in loops:
                    if (currentBlockId in loop):
                        continue
                    else:
                        temp = loop[:]
                        temp.append(currentBlockId)
                        loopsForParsing.append(temp)

                #result.extend(self.__buildLoops(outLine.get("destinationblockid"), loopEndBlockId, loopsForParsing))
        return loopsForParsing

    def __findAllLoopCreatingConnections(self):
        loopCreatingConnections = []
        allBlocks = self.getAllBlocks()
        for blk in allBlocks:
            blockLoopCreatingConnections = self.__getLoopCreatingConnections(blk)
            loopCreatingConnections.extend(blockLoopCreatingConnections)
        return loopCreatingConnections

    def __findAllLoops(self):
        allLoops = []
        loopCreatingConnections = self.__findAllLoopCreatingConnections()
        dummyLoops = []
        dummyLoops.append([])
        for loopCreatingConnection in loopCreatingConnections:
            allLoops.append(self.__buildLoops(loopCreatingConnection,
            loopCreatingConnection.get("sourceblockid"), dummyLoops))
        return allLoops

    def test(self):
        return self.__findAllLoopCreatingConnections()

    def __calculateModelFixedPoint(self):
        allBlocks = self.getAllBlocks()
        fixedPoint = -1
        counter = 0
        for blk in allBlocks:
            interFP = self.__calculateBlockSymbolicFixedPoint(blk)
            fixedPoint = max(fixedPoint, interFP)
        return fixedPoint
