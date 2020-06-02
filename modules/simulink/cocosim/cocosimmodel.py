import modules.utils.utils as cUtils
import modules.utils.gcd as gcd
import modules.logging.logmanager as LogManager
import copy
from modules.modelchecker.simulink.parsedsimulinkline import *
from modules.modelchecker.simulink.parsedsimulinkblock import *
from modules.modelchecker.simulink.parsedsimulinkmodel import *
from copy import deepcopy
import numpy as np


class CoCoSimModel:

    def __init__(self, _simulinkmodeljson, _slist, _configuration={}):
        print("CoCoSimModel initiation started")
        self.__createAttributes(_simulinkmodeljson, _slist, _configuration)
        self.__preProcessModel()
        self.packedBlocks = self.packAllBlocksForTransformation()
        self.symbolicFixedPoint = self.__calculateModelFixedPoint()
        print 'fixedpoint', self.symbolicFixedPoint
        self.writePackedBlocksToFile()
        self.writeConnectionTableToFile()
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
        self.parameterTable = self.__getParameterTable()

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

    def __findAllEntriesByDestination(self, _handle):
        allEntries = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(entry.get("DstBlockHandle", ""), _handle):
                allEntries.append(entry)
        return allEntries

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

    def __traceOutPortBlock(self, outPortBlock, connection, partialTable):

        portNumber = outPortBlock.get("Port", None)
        #try:
        portNumberAsInteger = int(portNumber)
        newConnection       = self.__findEntryByDestination(
                cUtils.stringify(outPortBlock.get("ParentHandle", "")), portNumberAsInteger, partialTable)
        if newConnection is None:  # this should work for outports on model level which shall be translated into blocks, and eventually becoming signals
            return connection
        destinationBlock  = self.getBlockById(newConnection.get('DstBlockHandle'))
        outPortBlock = self.__findOutPortBlockByPortNumner(destinationBlock, connection.get('SrcPort', ''))
        destinationPortConnectivity = destinationBlock.get('PortConnectivity')
        for k in range(len(destinationPortConnectivity)):
            if (destinationPortConnectivity[k].get('Type') == str(portNumber)) and (str(destinationPortConnectivity[k].get('SrcBlock')) == '[]'):
                connection['DstBlockHandle'] = destinationBlock.get('PortConnectivity')[k].get('DstBlock')

        return connection

    def __traceMuxBlock(self, muxBlock, connection, partialTable):
        try:
            newConnection = self.__findEntryByDestination(
                    cUtils.stringify(muxBlock.get('Handle', '')), None, partialTable)

            if newConnection is None:  # this should work for inports on model level which shall be translated into blocks, and eventually becoming signals
                return connection

            sourceBlock = self.getBlockById(cUtils.stringify((muxBlock.get('Handle'))))
            muxPort = muxBlock.get('PortConnectivity', '')
            returnConnection = []
            for k in range(len(muxPort)-1):
                tmpConnection          = deepcopy(connection)
                port                   = muxPort[k]
                destinationBlockNumber = tmpConnection.get('DstBlockHandle', '')
                destinationBlock       = self.getBlockById(destinationBlockNumber)
                sourceBlockNumber      = port.get('SrcBlock')
                if cUtils.compareStringsIgnoreCase(destinationBlock.get('BlockType', ''), "Demux") is False:
                    tmpConnection["SrcBlockHandle"] = sourceBlockNumber
                    tmpConnection                   = self.__mapConnectionSource(tmpConnection, partialTable)
                    tmpConnection["SrcPort"]        = k
                    returnConnection.append(tmpConnection)
        except Exception as e:
            self.logger.exception(e)

        return returnConnection

    def __traceDemuxBlock(self, demuxBlock, connection, partialTable):
        try:
            newConnection = self.__findEntryByDestination(
                    cUtils.stringify(demuxBlock.get('Handle', '')), None, partialTable)

            if newConnection is None:  # this should work for inports on model level which shall be translated into blocks, and eventually becoming signals
                return connection

            sourceBlock       = self.getBlockById(cUtils.stringify((demuxBlock.get('Handle'))))
            port              = demuxBlock.get('PortConnectivity', '')[0]
            sourceBlockNumber = port.get('SrcBlock')
            sourceBlock       = self.getBlockById(sourceBlockNumber)

            if cUtils.compareStringsIgnoreCase(sourceBlock.get('BlockType', ''), "Mux"):
                muxSourceBlock               = sourceBlock.get('PortConnectivity')
                destinationBlock             = muxSourceBlock[connection.get('SrcPort', '')]
                connection["SrcPort"]        = connection.get("SrcPort", "")
                connection['SrcBlockHandle'] = destinationBlock.get('SrcBlock')
                connection                   = self.__mapConnectionSource(connection, partialTable)
            else:
                connection["SrcBlockHandle"] = connection.get('DstBlockHandle')
                newDestinationConnection     = self.__mapConnectionSource(connection, partialTable)
                connection["SrcPort"]        = connection.get("SrcPort", "")
                connection["SrcBlockHandle"] = sourceBlockNumber
                newSourceConnection          = self.__mapConnectionSource(connection, partialTable)
                connection["SrcPort"]        = newSourceConnection.get("SrcPort", "")
                connection["SrcBlockHandle"] = newSourceConnection.get('SrcBlockHandle', '')
                connection["DstBlockHandle"] = newDestinationConnection.get('DstBlockHandle', '')
        except Exception as e:
            self.logger.exception(e)

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
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "outport"):
            connection = self.__traceOutPortBlock(sourceBlock, connection, partialTable)

        return connection

    def __createConnectionTable(self):
        connectionTable = self.__createAllDestinationEntries()
        finalTable = []
        for connection in connectionTable:
            connection = self.__mapConnectionSource(connection, connectionTable)
            if connection is not None:
                try:
                    for k in range(len(connection)):
                        tmpConnection = connection[k]
                        finalTable.append(tmpConnection)
                except:
                    destinationBlock = self.getBlockById(connection["DstBlockHandle"])
                    sourceBlock = self.getBlockById(connection["SrcBlockHandle"])
                    if not (cUtils.compareStringsIgnoreCase(destinationBlock.get("BlockType", ""), "mux") or 
                        cUtils.compareStringsIgnoreCase(destinationBlock.get("BlockType", ""), "demux") or 
                        cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "mux") or 
                        cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "demux")):
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
        predecessorIndices = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(entry.get("DstBlockHandle", ""), blockHandle):
                predecessorIndex = entry.get('SrcBlockHandle', '')
                predecessorBlock = self.getBlockById(predecessorIndex)
                predecessors.append(predecessorBlock)
                predecessorIndices.append(predecessorIndex)
        return predecessors, predecessorIndices

    def getBlockSuccessors(self, blockHandle):
        successors = []
        successorIndices = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(entry.get("SrcBlockHandle", ""), blockHandle):
                successorIndex = entry.get('DstBlockHandle', '')
                successorBlock = self.getBlockById(successorIndex)
                successors.append(successorBlock)
                successorIndices.append(successorIndex)
        return successors, successorIndices

    def __buildDependencyChain(self, _handle, visitedblocks=set()):
        if _handle not in visitedblocks:
            visitedblocks.add(_handle)
            predecessors, _ = self.getBlockPredecessors(_handle)
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
            try:
                blk["calculated_sample_time"] = float(blk["calculated_sample_time"])
                if blk["calculated_sample_time"] == -1:
                    blk["calculated_sample_time"] = float(self.__getGlobalSampleTime())                    
            except Exception as e:
                blk["calculated_sample_time"] = float(self.parameterTable[blk['calculated_sample_time']])
        return self
		
    def __calculateModelFixedPoint(self):
        allBlocks = self.getAllBlocks()
        fixedPoint = -1
        counter = 0
        for blk in allBlocks:
            interFP = self.__calculateBlockSymbolicFixedPoint(blk)
            fixedPoint = max(fixedPoint, interFP)
        return fixedPoint

    def __calculateBlockSymbolicFixedPoint(self, sBlock):
        sfp = cUtils.to_int(sBlock.get("symbolicfixedpoint", "-1"))
        if sfp > -1:
            return sfp
        _blockInputs = self.getBlockPredecessors(sBlock.get("Handle"))
        blockExecutionOrderId = cUtils.to_int(sBlock.get("ExecutionOrder", ""))
        blockSymbolicFixedPoint = sBlock['calculated_sample_time']
        predecessorsForProcessing = []
        predecessors, _ = self.getBlockPredecessors(sBlock.get("Handle"))
        for blk in predecessors:
            execId = cUtils.to_int(blk.get("ExecutionOrder", ""))
            if execId < blockExecutionOrderId:
                predecessorsForProcessing.append(blk)
        if (len(predecessorsForProcessing) > 0 and blockSymbolicFixedPoint != 0):
            blockSymbolicFixedPoint = self.__calculateBlockSymbolicFixedPointRecursively(sBlock,
                                                                predecessorsForProcessing)
        sBlock["symbolicfixedpoint"] = blockSymbolicFixedPoint
        return blockSymbolicFixedPoint

    def __calculateBlockSymbolicFixedPointResursively(self, sBlock, predecessors):
        predecessorsFixedPoints = []
        blockSampleTime = sBlock['calculated_sample_time']
        for prd in predecessors:
            predecessorsFixedPoints.append(self.__calculateBlockSymbolicFixedPoint(prd))
        return self.__determineFixedPoint(blockSampleTime, predecessorsFixedPoints)

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

    def __getParameter(self, param):
        
        parameter_val = self.parameterTable[param]

        return parameter_val

    def __getParameterTable(self):
        
        parameterTable = {'T_brake_pedal': 0.01, 'T_brake_ctrl': 0.02, 'T_spd_est': 0.02, 'T_abs': 0.01, 'T_veh': 0.005, 'T_sim': 0.005}

        return parameterTable
    def __getGlobalSampleTime(self):

        globalSampleTime = self.parameterTable['T_sim']

        return globalSampleTime

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
        _, blockCopy["predecessorBlocks"] = self.getBlockPredecessors(blockCopy.get("Handle"))
        _, blockCopy["successorBlocks"]   = self.getBlockSuccessors(blockCopy.get("Handle"))
        return blockCopy

    def packAllBlocksForTransformation(self):
        packedBlocksForTransformation = []
        for block in self.allBlocks:
            blockCopy = self.packBlockForTransformation(block)
            if not any(cUtils.compareStringsIgnoreCase(nonComputationalBlockType, blockCopy.get("BlockType")) for nonComputationalBlockType in self.noncomputationalBlocks):
                packedBlocksForTransformation.append(blockCopy)
        return packedBlocksForTransformation

    def writePackedBlocksToFile(self):
        f = open('packedTable.txt', 'w')
        for con in self.packedBlocks:
            f.write(str(con))
            f.write('\n')

        f.close()

    def writeConnectionTableToFile(self):
        f = open('table.txt', 'w')
        for con in self.connectionTable:
            f.write(str(con))
            f.write('\n')

        f.close()

    def calculateFundamentalSampleTime(self):
        if self.fundamentalSampleTime is None:
            self.fundamentalSampleTime = self.__calculateFundamentalSampleTime()
        return self.fundamentalSampleTime

    def __createParsedSimulinkModel(self):
        parsedSimulinkModel = ParsedSimulinkModel()
        parsedSimulinkModel.setModelName(self.getModelName())
        parsedSimulinkModel.setFundamentalSampleTime(self.calculateFundamentalSampleTime())
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
        blockLines = self.__findAllEntriesByDestination(simulinkBlock.get("Handle"))

        return parsedSimulinkBlock

    def parseModel(self):
        parsedSimulinkModel = self.__createParsedSimulinkModel()
        for sBlock in self.allBlocks:
            if not cUtils.compareStringsIgnoreCase(sBlock.get("ExecutionOrder", "-1"), "-1"):
                parsedSimulinkModel.addBlock(self.__createParsedSimulinkBlock(sBlock))
                pass

        return parsedSimulinkModel
