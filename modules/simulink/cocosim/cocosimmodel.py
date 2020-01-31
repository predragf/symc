import modules.utils.utils as cUtils
import modules.utils.gcd as gcd
import modules.logging.logmanager as LogManager
import copy
from modules.modelchecker.simulink import *


class CoCoSimModel:

    def __init__(self, _simulinkmodeljson, _slist, _configuration={}):
        print("CoCoSimModel initiation started")
        self.__createAttributes(_simulinkmodeljson, _slist, _configuration)
        self.__preProcessModel()
        print("CoCoSimModel initiation ended")

    def __createAttributes(self, _simulinkmodeljson, _slist, _configuration):
        self.logger = LogManager.LogManager.getLogger(__name__)
        self.compositeBlockTypes = ["subsystem"]
        self.noncomputationalBlocks = _configuration.get("noncomputationalblocks", [])
        self.portBlockTypes = ["inport", "outport"]
        self.rawSimulinkModelJson = _simulinkmodeljson
        self.sortedOrderList = _slist
        self.flatSimulinkModelJson = {}
        self.signalvariables = []
        self.fundamentalSampleTime = None
        self.allBlocks = self.__getAllBlocks()
        self.connectionTable = {}

    def __preProcessModel(self):
        self.connectionTable = self.__createConnectionTable()
        self.__adjustExecutionOrder(self.sortedOrderList)
        self.__calculateSampleTimes()

    def __getAllComputationalBlocks(self):
        computationalBlocks = []
        for blk in self.getAllBlocks():
            if not any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", "None")) for s in self.noncomputationalBlocks):
                computationalBlocks.append(blk)
        return computationalBlocks

    def __getAllPortBlocks(self):
        # this needs to be optimized later
        allPortBlocks = []
        for blk in self.getAllBlocks():
            if any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", "None")) for s in self.portBlockTypes):
                allPortBlocks.append(blk)
        return allPortBlocks

    def __extractSignalType(self, block, portNumber):
        signalType = ""
        try:
            compiledInPortTypes = block.get("CompiledPortDataTypes", {})
            if not (cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "inport") or cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "Outport")):
                compiledInPortTypes = compiledInPortTypes.get("Inport")
            elif cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "inport"):
                compiledInPortTypes = compiledInPortTypes.get("Outport")
            elif cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "outport"):
                compiledInPortTypes = compiledInPortTypes.get("Inport")
            if type(compiledInPortTypes) is not list:
                compiledInPortTypes = [compiledInPortTypes]
            signalType = compiledInPortTypes[int(portNumber) - 1]
        except Exception as exc:
            self.logger.exception("extract signal failed: {0}:{1}:{2}".format(
                block.get("BlockType"), block.get("Origin_path"), exc))
            pass
        return signalType

    def __createConnectionTableEntry(self, destinationBlock, outConnectionOfDestinationBlock, signalIdentifier):

        result = {
            "SrcBlockHandle": outConnectionOfDestinationBlock.get("SrcBlock"),
            "SrcPort": outConnectionOfDestinationBlock.get("SrcPort", ""),
            "DstBlockHandle": destinationBlock.get("Handle"),
            "DstPort": outConnectionOfDestinationBlock.get("Type", ""),
            "SignalType": self.__extractSignalType(destinationBlock,
                                                   outConnectionOfDestinationBlock.get("Type", "")),
            "SignalName": "signal_{0}".format(signalIdentifier)
        }
        return result

    def __createAllDestinationEntries(self):
        destinationEntries = []
        """
        destinationBlocks = self.__getAllComputationalBlocks()
        destinationBlocks.extend(self.__getAllPortBlocks())
        """
        destinationBlocks = self.getAllBlocks()
        identifier = 0
        for destinationBlock in destinationBlocks:
            outputBlockConnections = destinationBlock.get("PortConnectivity", {})
            # if only one connection then it is a signle object
            # then we must make it into a list, such that we can iterate
            if (type(outputBlockConnections)) == dict:
                outputBlockConnections = [outputBlockConnections]
            for outputConnection in outputBlockConnections:
                # this is a check for incomming connection
                if type(outputConnection.get("SrcBlock")) == float:
                    identifier += 1
                    destinationEntries.append(
                        self.__createConnectionTableEntry(destinationBlock, outputConnection, identifier))
        return destinationEntries

    def __findEntryByDestination(self, _handle, _port, _partialTable):

        for entry in _partialTable:
            if cUtils.compareStringsIgnoreCase(entry.get("DstBlockHandle", ""), _handle) and (_port is None or cUtils.compareStringsIgnoreCase(entry.get("DstPort"), _port)):
                return entry
        return None

    def __findOutPortBlockByPortNumner(self, ssBlock, portNumber):
        result = None
        ssBlockContent = ssBlock.get("Content", {})
        for innerBlockId in ssBlockContent:
            try:
                ssInnerBlock = ssBlockContent.get(innerBlockId, {})
                if not isinstance(portNumber, int):
                    portNumber = int(portNumber)
                intPortNumber = portNumber + 1
                if cUtils.compareStringsIgnoreCase(ssInnerBlock.get("BlockType", ""), "Outport"):
                    outPortBlockNumber = int(ssInnerBlock.get("Port", "-1"))
                    if intPortNumber == outPortBlockNumber:
                        result = ssInnerBlock
                        break
            except Exception as e:
                self.logger.exception(e)
        return result

    def __traceSubSystemBlock(self, ssBlock, connection, partialTable):
        result = connection
        portNumber = connection.get("SrcPort", "-1")
        try:
            outPortBlock = self.__findOutPortBlockByPortNumner(ssBlock, portNumber)
            newConnection = self.__findEntryByDestination(
                outPortBlock.get("Handle"), None, partialTable)
            if not newConnection is None:
                newConnection = self.__mapConnectionSource(newConnection, partialTable)
                result["SrcBlockHandle"] = newConnection.get("SrcBlockHandle", "")
                result["SrcPort"] = newConnection.get("SrcPort", "")
        except Exception as exc:
            self.logger.exception("{0}:{1}:{2}".format(ssBlock.get("Origin_path"), exc, portNumber))
        return result

    def __traceInPortBlock(self, inPortBlock, connection, partialTable):

        portNumber = inPortBlock.get("Port", None)
        try:
            portNumberAsInteger = int(portNumber)
            newConnection = self.__findEntryByDestination(
                cUtils.stringify(inPortBlock.get("ParentHandle", "")), portNumberAsInteger, partialTable)
            if newConnection is None:  # this should work for inports on model level which shall be translated into blocks, and eventually becoming signals
                return connection
            newConnection = self.__mapConnectionSource(newConnection, partialTable)
            connection["SrcPort"] = newConnection.get("SrcPort", "")
            connection["SrcBlockHandle"] = newConnection.get("SrcBlockHandle")
        except Exception as e:
            self.logger.exception(e)
        return connection

    def __traceMuxBlock(self, muxBlock, connection, partialTable):
        # TODO: to be implemented
        return connection

    def __traceDemuxBlock(self, demuxBlock, connection, partialTable):
        # TODO: to be implemented
        return connection

    def __mapConnectionSource(self, connection, partialTable):
        """
        Initially the connections have been created. However, some of the sources might be
        an atomic computational block and in such cases we must find the atomic computational block which writes to that signal
        """
        sourceBlock = self.getBlockById(connection.get("SrcBlockHandle", ""))
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "subsystem"):
            connection = self.__traceSubSystemBlock(sourceBlock, connection, partialTable)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "demux"):
            connection = self.__traceDemuxBlock(sourceBlock, connection, partialTable)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "mux"):
            connection = self.__traceMuxBlock(sourceBlock, connection, partialTable)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "inport"):
            connection = self.__traceInPortBlock(sourceBlock, connection, partialTable)
        return connection

    def __createConnectionTable(self):
        connectionTable = self.__createAllDestinationEntries()
        finalTable = []
        for connection in connectionTable:
            connection = self.__mapConnectionSource(connection, connectionTable)
            if connection is not None:
                finalTable.append(connection)
        return finalTable

    def __calculateSubSystemSampleTime(self, ssBlock):
        sampleTime = -1.0
        istriggered = False
        portConectivity = ssBlock.get("PortConnectivity", {})
        if not isinstance(portConectivity, list):
            portConectivity = [portConectivity]
        for line in portConectivity:
            if cUtils.compareStringsIgnoreCase(line.get("Type", ""), "Trigger"):
                triggerBlock = self.getBlockById(line.get("SrcBlock", ""))
                sampleTime = triggerBlock.get("sample_time", "-1")
                istriggered = True
        if not istriggered and not (ssBlock.get("ParentHandle", None) is None):
            parentSubSystemBlock = self.getBlockById(
                cUtils.stringify(ssBlock.get("ParentHandle", "")))
            sampleTime = self.__calculateSubSystemSampleTime(parentSubSystemBlock)
        return sampleTime

    def __flattenSubSystem(self, ssBlock, sampleTime=None):
        # this is fully implemented
        allBlocks = [ssBlock]
        innerContents = ssBlock.get("Content", {})
        ssBlockId = ssBlock.get("Handle", "")
        for blkName in innerContents:
            blk = innerContents.get(blkName)
            try:
                if any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", None)) for s in self.compositeBlockTypes):
                    blk["ParentHandle"] = repr(ssBlockId)
                    allBlocks.extend(self.__flattenSubSystem(blk, sampleTime))
                else:
                    blk["ParentHandle"] = repr(ssBlockId)
                    blk["calculated_sample_time"] = sampleTime
                    allBlocks.append(blk)
            except Exception as e:
                self.logger.exception(e)
        return allBlocks

    def __adjustExecutionOrder(self, _slist):
        # implemented
        for blk in self.getAllBlocks():
            blockPath = blk.get("Origin_path", "").lower()
            """ execution order - 1 denotes that it has no execution order
             that is, it is not included in the slist and as such
             sould not be included in the transformation"""
            _number = int(_slist.get(blockPath, "-1"))
            blk["ExecutionOrder"] = str(_number).zfill(2)

    def __createSignalsAndVariables(self):
        self.__createConnectionTable()

    def __getModelMetaData(self):
        # implemented
        sModelJson = self.getModelJSON()
        metaData = sModelJson.get("meta")
        return metaData if metaData is not None else {}

    def getBlockPredecessors(self, blockHandle):
        predecessors = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(entry.get("DstBlockHandle", ""), blockHandle):
                predecessorBlock = self.getBlockById(entry.get("SrcBlockHandle", ""))
                predecessors.append(predecessorBlock)
        return predecessors

    def __buildDependencyChain(self, _handle, visitedblocks=set()):
        if _handle not in visitedblocks:
            visitedblocks.add(_handle)
            predecessors = self.getBlockPredecessors(_handle)
            for predecessor in predecessors:
                visitedblocks = self.__buildDependencyChain(
                    predecessor.get("Handle", ""), visitedblocks)
        return visitedblocks

    def getDependencyChain(self, blockHandle):
        dependencyChain = []
        dependencyChainHandles = self.__buildDependencyChain(blockHandle)
        for dependencyChainHandle in dependencyChainHandles:
            dependencyChain.append(self.getBlockById(dependencyChainHandle))
        return dependencyChain

    def getModelName(self):
        # implemented
        defaultValue = ""
        metaData = self.__getModelMetaData()
        modelName = metaData.get("file_path")
        return modelName if modelName is not None else defaultValue

    def getModelJSON(self):
        # getter function
        return self.rawSimulinkModelJson

    def __calculateFundamentalSampleTime(self):
        sampleTimes = set()
        for blk in self.allBlocks:
            sTime = float(blk.get("calculated_sample_time", "-1"))
            if sTime >= 0:
                sampleTimes.add(sTime)
        return gcd.gcd(sampleTimes)

    def __calculateSampleTimes(self):
        for blk in self.allBlocks:
            if any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", "")) for s in self.compositeBlockTypes):
                blk["calculated_sample_time"] = self.__calculateSubSystemSampleTime(blk)
            else:
                parentSS = self.getBlockById(cUtils.stringify(blk.get("ParentHandle")))
                blk["calculated_sample_time"] = self.__calculateSubSystemSampleTime(parentSS)
        return

    def __getAllBlocks(self):
        allBlocks = []
        firstLevelComposite = 0
        content = self.rawSimulinkModelJson.get(
            self.getModelName()).get("Content", {})
        blocks = 0
        for blkId in content:
            blocks = blocks + 1
            try:
                blk = content.get(blkId)
                if any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", "")) for s in self.compositeBlockTypes):
                    allBlocks.extend(self.__flattenSubSystem(blk))
                else:
                    allBlocks.append(blk)
            except Exception as e:
                self.logger.exception(e)
        return allBlocks

    def getAllBlocks(self):
        return self.allBlocks

    def getBlockById(self, blockId):
        result = {}
        if not isinstance(blockId, str):
            blockId = repr(blockId)
        for blk in self.getAllBlocks():
            if cUtils.compareStringsIgnoreCase(repr(blk.get("Handle")), blockId) or cUtils.compareStringsIgnoreCase(blk.get("Name"), blockId) or cUtils.compareStringsIgnoreCase(blk.get("Path"), blockId) or cUtils.compareStringsIgnoreCase(blk.get("Origin_path"), blockId):
                result = blk
                break
        return result

    def getBlocksForTransformation(self):
        raise Exception("To be implemented")

    def getModelVariables(self):
        raise Exception("To be implemented")

    def packBlockForTransformation(self, block):
        blockCopy = copy.deepcopy(block)
        blockCopy["predecessorBlocks"] = self.getBlockPredecessors(
            blockCopy.get("Handle"))
        return blockCopy

    def packAllBlocksForTransformation(self):
        packedBlocksForTransformation = []
        for block in self.allBlocks:
            if not any(cUtils.compareStringsIgnoreCase(nonComputationalBlockType, blockCopy.get("BlockType")) for nonComputationalBlockType in self.noncomputationalBlocks):
                packedBlocksForTransformation.append(self.packBlockForTransformation(block))
        return packedBlocksForTransformation

    def calculateFundamentalSampleTime(self):
        if self.fundamentalSampleTime is None:
            self.fundamentalSampleTime = self.__calculateFundamentalSampleTime()
        return self.fundamentalSampleTime

    def __createParsedSimulinkModel(self):
        parsedSimulinkModel = ParsedSimulinkModel()
        parsedSimulinkModel.setName(self.getModelName())
        parsedSimulinkModel.setFundamentalSampleTime(self.getFundamentalSampleTime())
        return parsedSimulinkModel

    def __createParsedBlockParameters(self, simulinkBlock):
        parameters = {}

        return parameters

    def __createParsedSimulinkBlock(self, simulinkBlock):
        parsedSimulinkBlock = ParsedSimulinkBlock()
        parsedSimulinkBlock.setName(simulinkBlock.get("Name", ""))
        parsedSimulinkBlock.setBlockId(simulinkBlock.get("Origin_path"))
        parsedSimulinkBlock.setBlockType(simulinkBlock.get("BlockType"))
        parsedSimulinkBlock.setParameters(self.__createParsedBlockParameters(simulinkBlock))
        return parsedSimulinkBlock

    def parseModel(self):
        parsedSimulinkModel = self.__createParsedSimulinkModel()
        for sBlock in self.allBlocks:
            if not cUtils.compareStringsIgnoreCase(sBlock.get("ExecutionOrder", "-1"), "-1"):
                parsedSimulinkModel.addBlock(self.__createParsedSimulinkBlock(sBlock))
                # mandatory set of functions end
        return parsedSimulinkModel
