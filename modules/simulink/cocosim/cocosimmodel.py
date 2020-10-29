import modules.utils.utils as cUtils
import modules.utils.gcd as gcd
import modules.logging.logmanager as LogManager
import copy
from copy import deepcopy
import time

class CoCoSimModel:

    def __init__(self, _simulinkmodeljson, _slist, _configuration={}):
        print("CoCoSimModel initiation started")
        self.__createAttributes(_simulinkmodeljson, _slist, _configuration)
        self.__preProcessModel()
        self.packedBlocksForTransformation = None  # self.__packAllBlocksForTransformation()
        self.symbolicFixedPoint = self.__calculateModelSymbolicFixedPoint()
        print("CoCoSimModel initiation ended")

    def __createAttributes(self, _simulinkmodeljson, _slist, _configuration):
        self.configuration = _configuration
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
        self.__adjustExecutionOrder(self.sortedOrderList)
        self.__addPortNumbers()
        self.connectionTable = self.__createConnectionTable()
        self.__calculateSampleTimes()

    def __getAllComputationalBlocks(self):
        computationalBlocks = []
        for blk in self.getAllBlocks():
            if not any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", "None")) for s in self.noncomputationalBlocks):
                computationalBlocks.append(blk)
        return computationalBlocks

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
            signalType = compiledInPortTypes[int(portNumber)]
        except Exception as exc:
            self.logger.exception("extract signal failed: {0}:{1}:{2}".format(
                block.get("BlockType"), block.get("Origin_path"), exc))
            pass
        return signalType

    def __addPortNumbers(self):
        # this function assigns port numbers to all ports of blocks
        # because initially the block ports have no numbers (index)
        allBlocks = self.__getAllBlocks()
        pConnectivity = {}
        for blk in allBlocks:
            outPortNumber = 0
            inPortNumber = 0
            try:
                pConnectivity = blk.get("PortConnectivity", {})
            except Exception as e:
                continue
            for port in pConnectivity:
                try:
                    # out port has handle in the DstBlock field
                    if type(port.get("DstBlock", "")) is float and port.get("Type", "string").isnumeric():
                        port["PortNumber"] = outPortNumber
                        port["PortType"] = "out"
                        outPortNumber = outPortNumber + 1
                    # in port has handle in the SrcBlock field
                    elif type(port.get("SrcBlock", "")) is float and port.get("Type", "string").isnumeric():
                        port["PortNumber"] = inPortNumber
                        port["PortType"] = "in"
                        inPortNumber = inPortNumber + 1
                except Exception as e:
                    continue

    def __createConnectionTableEntry(self, destinationBlock, outConnectionOfDestinationBlock, signalId):
        # this function creates connection table entry from a block and a port
        dstPortNumber = outConnectionOfDestinationBlock.get("PortNumber", "")
        return {
            "SrcBlockHandle": outConnectionOfDestinationBlock.get("SrcBlock"),
            "SrcPort": outConnectionOfDestinationBlock.get("SrcPort", ""),
            "DstBlockHandle": destinationBlock.get("Handle"),
            "DstPort": dstPortNumber,
            "SignalType": self.__extractSignalType(destinationBlock,
                                                   dstPortNumber),
            "SignalName": "signal_{0}".format(signalId)
        }

    def __createDesitinationEntriesForBlock(self, sBlock):
        # this function creates all the connections incomming to a given block (sBlock)
        blockDestinationEntries = []
        outputBlockPorts = sBlock.get("PortConnectivity", {})
        # if only one connection then it is a signle object
        # then we must make it into a list, such that we can iterate
        if (type(outputBlockPorts)) == dict:
            outputBlockPorts = [outputBlockPorts]
        for outputBlockPort in outputBlockPorts:
            # this is a check for incomming connection
            if cUtils.compareStringsIgnoreCase(outputBlockPort.get("PortType", ""), "in"):
                blockDestinationEntries.append(
                    self.__createConnectionTableEntry(
                        sBlock, outputBlockPort, cUtils.generateRandomLetterSequence(12)))
        return blockDestinationEntries

    def __createDesitnationEntriesForPorts(self, subSystemBlock):
        # this function creates all connections comming to ports of subsystem
        # we need this function because the port blocks are not part of allBlocks
        destinationEntries = []
        content = subSystemBlock.get("Content", {})
        for key in content.keys():
            try:
                child = content[key]
                if cUtils.compareStringsIgnoreCase(child.get("BlockType", ""), "Outport"):
                    pc = child.get("PortConnectivity")
                    if (type(pc)) == dict:
                        pc = [pc]
                    for _port in pc:
                        destinationEntries.append(self.__createConnectionTableEntry(
                            child, _port, cUtils.generateRandomLetterSequence(12)))
            except:
                continue
        return destinationEntries

    def __createAllDestinationEntries(self):
        destinationEntries = []
        destinationBlocks = self.getAllBlocks()
        for destinationBlock in destinationBlocks:
            destinationEntries.extend(self.__createDesitinationEntriesForBlock(destinationBlock))
            if cUtils.compareStringsIgnoreCase(destinationBlock.get("BlockType"), "SubSystem") and destinationBlock.get("StateflowContent", None) is None:
                destinationEntries.extend(self.__createDesitnationEntriesForPorts(destinationBlock))
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

    def __findOutPortBlockByPortNumber(self, ssBlock, portNumber):
        # this function maps subsystem block to an output port
        # inside of the subsystem
        result = None
        ssBlockContent = ssBlock.get("Content", {})
        for innerBlockId in ssBlockContent:
            try:
                ssInnerBlock = ssBlockContent.get(innerBlockId, {})
                if not isinstance(portNumber, int):
                    portNumber = int(portNumber)
                # this is because block that corresponds to a port is 1-based,
                # whereas the numbering of port numbers of composite block is 0-based
                intPortNumber = portNumber + 1
                if cUtils.compareStringsIgnoreCase(ssInnerBlock.get("BlockType", ""), "Outport"):
                    outPortBlockNumber = int(ssInnerBlock.get("Port", "-1"))
                    if intPortNumber == outPortBlockNumber:
                        result = ssInnerBlock
                        break
            except Exception as e:
                self.logger.exception(e)
        return result

    def __traceSubSystemBlock(self, ssBlock, connection, partialTable, stack):
        # this function is called when the source of the coonection is a subSystemBlock
        # because in the final table the source and the destination must be computationalBlocks
        result = []
        portNumber = connection.get("SrcPort", "-1")
        try:
            outPortBlock = self.__findOutPortBlockByPortNumber(ssBlock, portNumber)
            existingConnection = self.__findEntryByDestination(
                outPortBlock.get("Handle"), None, partialTable)
            if existingConnection is not None:
                newConnections = self.__mapConnectionSource(existingConnection, partialTable, stack)
                if newConnections is not None and type(newConnections) is not list:
                    newConnections = [newConnections]
                for nc in newConnections:
                    result.append(self.__mergeConnections(nc, connection))
            # this else should in principle never happen
            else:
                result = [connection]
        except Exception as exc:
            self.logger.exception("{0}:{1}:{2}".format(ssBlock.get("Origin_path"), exc, portNumber))

        return result

    def __traceInPortBlock(self, inPortBlock, connection, partialTable, stack):
        # this function is called when the source of the coonection is an in port block
        # because in the final table the source and the destination must be computationalBlocks
        portNumber = inPortBlock.get("Port", None)
        result = []
        try:
            portNumberAsInteger = int(portNumber)
            # because ports as blocks are 1-based and ports as part of composite
            # blocks are 0-based
            newConnections = self.__findEntryByDestination(
                cUtils.stringify(inPortBlock.get("ParentHandle", "")), portNumberAsInteger - 1, partialTable)
            # this should work for inports on model level which shall be translated into variables, and eventually becoming signals
            if newConnections is None:
                return [connection]
            newConnections = self.__mapConnectionSource(newConnections, partialTable, stack)
            if newConnections is not None and type(newConnections) is not list:
                newConnections = [newConnections]
            for nc in newConnections:
                result.append(self.__mergeConnections(nc, connection))
        except Exception as e:
            self.logger.exception(e)
        return result

    def __traceMuxBlock(self, muxBlock, connection, partialTable, stack):
        # this function is called when the source of the coonection is a mux block
        # because in the final table the source and the destination must be computationalBlocks
        # the main idea is to have a stack where we keep the ports from demux blocks from which
        # we have reached this mux block, in order to know which port to resume from
        # if stack is empty, that means that either there is no demux or there
        # is a computational block between the mux and demux
        result = []
        try:
            existingConnection = self.__findEntryByDestination(
                cUtils.stringify(muxBlock.get('Handle', '')), None, partialTable)
            # check if no connection exists. In that case, the input into the mux blocks
            # is a input of the model. Consequently, return the connection
            if existingConnection is None:
                return connection
            # if there is an existing connection, process it
            portConectivity = muxBlock.get("PortConnectivity", {})
            portNumberToTraceback = -1
            if len(stack) > 0:
                portNumberToTraceback = stack.pop()
            if not isinstance(portConectivity, list):
                portConectivity = [portConectivity]
            for port in portConectivity:
                if (not cUtils.compareStringsIgnoreCase(port.get("PortNumber"), str(portNumberToTraceback))) and portNumberToTraceback >= 0:
                    continue
                returnConnection = self.__findEntryByDestination(
                    muxBlock.get("Handle"), port.get("PortNumber", ""), partialTable)
                result.extend(self.__mapConnectionSource(
                    returnConnection, partialTable, stack))
        except Exception as e:
            self.logger.exception(e)
        return result

    def __traceDemuxBlock(self, demuxBlock, connection, partialTable, stack):
        # this function is called when the source of the coonection is a mux block
        # because in the final table the source and the destination must be computationalBlocks
        # the main idea is to have a stack where we keep the ports from demux blocks from which
        # we have reached this mux block, in order to know which port to resume from
        # if stack is empty, that means that either there is no demux or there
        # is a computational block between the mux and demux
        newConnection = {}
        # create fresh copy of the stack
        newStack = stack[:]
        try:
            newConnection = self.__findEntryByDestination(
                cUtils.stringify(demuxBlock.get('Handle', '')), None, partialTable)
            if newConnection is None:  # this should work for inports on model level which shall be translated into blocks, and eventually becoming signals
                return connection
            newStack.append(connection.get("SrcPort"))
        except Exception as e:
            self.logger.exception(e)
            newConnection = {}

        return self.__mapConnectionSource(newConnection, partialTable, newStack)

    def __traceBusSelectorBlock(self, busSelectorBlock, connection, partialTable, stack):
        return self.__traceDemuxBlock(busSelectorBlock, connection, partialTable, stack)

    def __traceBusCreatorBlock(self, busCreatorBlock, connection, partialTable, stack):
        return self.__traceMuxBlock(busCreatorBlock, connection, partialTable, stack)

    def __mapConnectionSource(self, connection, partialTable, stack):
        """
        Initially all the connections have been created. However, some of the sources might not be
        an atomic computational block and in such cases we must find the atomic computational block which writes to that signal
        """
        sourceBlock = self.getBlockById(connection.get("SrcBlockHandle", ""))
        # subsystem is not a stateflow
        if (cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "subsystem") and (sourceBlock.get("StateflowContent", None) is None)):
            connection = self.__traceSubSystemBlock(sourceBlock, connection, partialTable, stack)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "demux"):
            connection = self.__traceDemuxBlock(sourceBlock, connection, partialTable, stack)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "mux"):
            connection = self.__traceMuxBlock(sourceBlock, connection, partialTable, stack)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "inport"):
            connection = self.__traceInPortBlock(sourceBlock, connection, partialTable, stack)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "busselector"):
            connection = self.__traceBusSelectorBlock(sourceBlock, connection, partialTable, stack)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "buscreator"):
            connection = self.__traceBusCreatorBlock(sourceBlock, connection, partialTable, stack)

        return connection if type(connection) is list else [connection]

    def __modifyFinalTableConnection(self, connection, finalTable):
        # Check if signal already exists in the connection table
            # (i.e. same source block handle and source port)
        if connection == {}:
            return {}
        newConnection = deepcopy(connection)
        srcBlockHandle = newConnection.get('SrcBlockHandle', "")
        srcPort = newConnection.get('SrcPort', "")
        for entry in finalTable:
            if entry == {}:
                continue
            tmpSrcBlockHandle = entry.get("SrcBlockHandle", "")
            tmpSrcPort = entry.get("SrcPort")
            if cUtils.compareStringsIgnoreCase(tmpSrcBlockHandle, srcBlockHandle) and cUtils.compareStringsIgnoreCase(tmpSrcPort, srcPort):
                newConnection["SignalName"] = entry.get("SignalName", "")
                break
        return newConnection

    def __mergeConnections(self, sourceExtractionConnection, destinationExtractionConnection):
        return {
            "SrcBlockHandle": sourceExtractionConnection.get("SrcBlockHandle", ""),
            "SrcPort": sourceExtractionConnection.get("SrcPort", ""),
            "DstBlockHandle": destinationExtractionConnection.get("DstBlockHandle", ""),
            "DstPort": destinationExtractionConnection.get("DstPort", ""),
            "SignalType": destinationExtractionConnection.get("SignalType", ""),
            "SignalName": sourceExtractionConnection.get("SignalName", "")
        }

    def __createConnectionTable(self):
        # after this connection table has all the signals and destinationBlocks
        # we just need to adjust the sources
        connectionTable = self.__createAllDestinationEntries()
        finalTable = []
        stack = []
        for connection in connectionTable:
            dstBlockHandle = connection.get("DstBlockHandle")
            dstBlock = self.getBlockById(dstBlockHandle)
            if (cUtils.compareStringsIgnoreCase(dstBlock.get("ExecutionOrder", "-1"), "-1") or dstBlock.get("BlockType", "") in self.noncomputationalBlocks) and dstBlock.get("StateflowContent", None) is None:
                continue
            mappedConnection = self.__mapConnectionSource(connection, connectionTable, stack)
            for mc in mappedConnection:
                combinedConnection = self.__mergeConnections(mc, connection)
                combinedConnection = self.__modifyFinalTableConnection(
                    combinedConnection, finalTable)
                if combinedConnection != {}:
                    finalTable.append(combinedConnection)
        return [dict(t) for t in {tuple(d.items()) for d in finalTable}]

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
        # this function replaces subsystem block with by a set of its constituent blocks
        # the main role is to basically assign a sample time of the inner blocks,
        # which when assigned and combined with the execution order number allows them
        # to be treated as an independent units outside of the subsystem
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
        # assigns execution order for each block that is in the slist
        # slist is obtained from matlab and passed as a parameter into the
        # CoCoSimModel class
        # if the block is not in the slist, it gets -1 for execution order
        # the main rationale is that if the block is not in the slist, it will
        # not be included in the analysis model
        for blk in self.getAllBlocks():
            blockPath = blk.get("Origin_path", "").lower().strip()
            _number = int(_slist.get(blockPath, "-1"))
            blk["ExecutionOrder"] = str(_number).zfill(2)

    def __getModelMetaData(self):
        # returns meta-data of the CoCoSim-exported JSON
        sModelJson = self.getModelJSON()
        metaData = sModelJson.get("meta")
        return metaData if metaData is not None else {}

    def __getBlockPredecessors(self, blockHandle):
        # function that returns a list of blocks which signals are
        # input into the block given by the handle
        # based on the connection table
        predecessors = []
        predecessorIndices = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(entry.get("DstBlockHandle", ""), blockHandle):
                predecessorIndex = entry.get('SrcBlockHandle', '')
                predecessorBlock = self.getBlockById(predecessorIndex)
                predecessors.append(predecessorBlock)
                predecessorIndices.append(predecessorIndex)
        # why do we need the indicies???
        return predecessors, predecessorIndices

    def __getBlockSuccessors(self, blockHandle):
        # list of all blocks to whom the output signals from the block given
        # by the block handle are direct inputs
        # based on the connection table
        successors = []
        successorIndices = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(entry.get("SrcBlockHandle", ""), blockHandle):
                successorIndex = entry.get('DstBlockHandle', '')
                successorBlock = self.getBlockById(successorIndex)
                successors.append(successorBlock)
                successorIndices.append(successorIndex)
        return successors, successorIndices

    def __getBlockInputSignals(self, blockHandle):
        inputSignals = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(blockHandle, entry.get("DstBlockHandle")):
                inputSignals.append(entry)
        return inputSignals

    def __getBlockOutputSignals(self, blockHandle):
        outputSignals = []
        for entry in self.connectionTable:
            if cUtils.compareStringsIgnoreCase(blockHandle, entry.get("SrcBlockHandle")):
                outputSignals.append(entry)
        return outputSignals

    def __buildDependencyChain(self, _handle, visitedblocks=set()):
        # function for recursive call of the public one (see blow)
        if _handle not in visitedblocks:
            visitedblocks.add(_handle)
            predecessors, _ = self.__getBlockPredecessors(_handle)
            for predecessor in predecessors:
                visitedblocks = self.__buildDependencyChain(
                    predecessor.get("Handle", ""), visitedblocks)
        return visitedblocks

    def getDependencyChain(self, blockHandle):
        # this function build a data and control dependency between the blocks in the model.
        # we just give a block, and the function will return a list of blocks
        # which directly contribute to the output that this block produces. This is
        # very useful for isolating parts of the system for certain properties
        dependencyChain = []
        dependencyChainHandles = self.__buildDependencyChain(blockHandle)
        for dependencyChainHandle in dependencyChainHandles:
            dependencyChain.append(self.getBlockById(dependencyChainHandle))
        return dependencyChain

    def __extractModelNameFromMetaData(self, metaData={}):
        # self descriptive what the function does
        modelName = metaData.get("file_path", "")
        begining = 0
        end = len(modelName)
        if "/" in modelName:
            begining = modelName.rindex("/")+1
        if ".mdl" in modelName:
            end = modelName.rindex(".mdl")
        return modelName[begining:end]

    def getModelName(self):
        # self descriptive function
        metaData = self.__getModelMetaData()
        return self.__extractModelNameFromMetaData(metaData)

    def getModelJSON(self):
        # raw JSON getter
        return self.rawSimulinkModelJson

    def __calculateFundamentalSampleTime(self):
        # function that calculates the fundamental sample time of the model
        # fundamental sample time is the Greates Common Divisor of all sample times in the model
        sampleTimes = set()
        for blk in self.allBlocks:
            sTime = float(blk.get("calculated_sample_time", "-1"))
            if sTime >= 0:
                sampleTimes.add(sTime)

        # Added if all sample times are -1
        if sampleTimes == set():
            sTimeSpecified = self.rawSimulinkModelJson.get(
            'meta').get('sampleTime')
            sampleTimes.add(float(sTimeSpecified))

        return gcd.gcd(sampleTimes)

    def __calculateSampleTimes(self):
        # if the sample times are given as variables, then the mapping
        # between the variables and the values should be provided in the
        # configuration object
        #
        # I need to check if this function also works if sample times are given
        # as numbers
        sampleTimes = self.configuration.get("sample_times", {})
        # this function calculates and assigns sample times for all blocks in the model
        for blk in self.allBlocks:
            if any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", "")) for s in self.compositeBlockTypes):
                blk["calculated_sample_time"] = self.__calculateSubSystemSampleTime(blk)
            else:
                parentSS = self.getBlockById(cUtils.stringify(blk.get("ParentHandle")))
                blk["calculated_sample_time"] = self.__calculateSubSystemSampleTime(parentSS)
            try:
                calculatedSampleTime = blk.get("calculated_sample_time", "")
                # try to convert what you got into a number (float)
                blk["calculated_sample_time"] = float(calculatedSampleTime)
            except Exception as e:
                # this exception is hit only if the float conversion above fails
                # in that case, the sample time is in the dictionary of sample times
                blk["calculated_sample_time"] = sampleTimes.get(calculatedSampleTime, float("-1"))
        return self

    def __calculateModelSymbolicFixedPoint(self):
        # model fixed point is basically the completeness treshold for bounded model checking
        # the fixed point procedure represents an implementation of the algorithm proposed
        # by Filipovikj et al. in Bounded invariance checking of simulink models
        allBlocks = self.getAllBlocks()
        fixedPoint = -1
        for blk in allBlocks:
            interFP = self.__calculateBlockSymbolicFixedPoint(blk)
            fixedPoint = max(fixedPoint, interFP)
        return fixedPoint

    def __calculateBlockSymbolicFixedPoint(self, sBlock):
        # calcucalting the fixed point for a block
        # the fixed point procedure represents an implementation of the algorithm proposed
        # by Filipovikj et al. in Bounded invariance checking of simulink models
        sfp = cUtils.to_int(sBlock.get("symbolicfixedpoint", "-1"))
        if sfp > -1:
            return sfp
        blockExecutionOrderId = cUtils.to_int(sBlock.get("ExecutionOrder", ""))
        blockSymbolicFixedPoint = sBlock.get('calculated_sample_time', "")
        predecessorsForProcessing = []
        predecessors, _ = self.__getBlockPredecessors(sBlock.get("Handle"))
        for blk in predecessors:
            execId = cUtils.to_int(blk.get("ExecutionOrder", ""))
            if execId < blockExecutionOrderId:
                predecessorsForProcessing.append(blk)
        if (len(predecessorsForProcessing) > 0 and blockSymbolicFixedPoint != 0):
            blockSymbolicFixedPoint = self.__calculateBlockSymbolicFixedPointResursively(sBlock,
                                                                                         predecessorsForProcessing)
        sBlock["symbolicfixedpoint"] = blockSymbolicFixedPoint
        return blockSymbolicFixedPoint

    def __calculateBlockSymbolicFixedPointResursively(self, sBlock, predecessors):
        # calcucalting the fixed point for a block
        # the fixed point procedure represents an implementation of the algorithm proposed
        # by Filipovikj et al. in Bounded invariance checking of simulink models
        predecessorsFixedPoints = []
        blockSampleTime = sBlock['calculated_sample_time']
        for prd in predecessors:
            predecessorsFixedPoints.append(self.__calculateBlockSymbolicFixedPoint(prd))
        return self.__determineFixedPoint(blockSampleTime, predecessorsFixedPoints)

    def __determineFixedPoint(self, outTs, predecessorsTs):
        fixedPoint = outTs
        for predecessorTs in predecessorsTs:
            if(cUtils.compareStringsIgnoreCase(predecessorTs, "")):
                predecessorTs = -1
            if(predecessorTs < outTs):
                continue
            if(predecessorTs >= outTs):
                interFP = (int(predecessorTs / outTs) +
                           (predecessorTs % outTs > 0)) * outTs
                fixedPoint = max(fixedPoint, interFP)
        return fixedPoint

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
        # initialize block for transformation the first time the
        # function is called
        if self.packedBlocksForTransformation is None:
            self.packedBlocksForTransformation = self.packAllBlocksForTransformation()
        return self.packedBlocksForTransformation

    def getModelVariables(self):
        connectionTable = self.connectionTable
        modelVariables = set()
        for con in connectionTable:
            modelVariables.add(con['SignalName'])
        return list(modelVariables)

    def __packBlockForTransformation(self, block):
        # we create deep-copy becase we modify the block (add the extra parameters)
        # but we do not want the original block object to be modified
        blockCopy = copy.deepcopy(block)
        _handle = blockCopy.get("Handle")
        blockCopy["predecessorBlocks"] = self.__getBlockPredecessors(_handle)[0]
        blockCopy["successorBlocks"] = self.__getBlockSuccessors(_handle)[0]
        blockCopy["inputSignals"] = self.__getBlockInputSignals(_handle)
        blockCopy["outputSignals"] = self.__getBlockOutputSignals(_handle)
        return blockCopy

    def packAllBlocksForTransformation(self):
        packedBlocksForTransformation = []
        for block in self.allBlocks:
            blockCopy = self.__packBlockForTransformation(block)
            if not any(cUtils.compareStringsIgnoreCase(nonComputationalBlockType, blockCopy.get("BlockType")) for nonComputationalBlockType in self.noncomputationalBlocks):
                packedBlocksForTransformation.append(blockCopy)
        return packedBlocksForTransformation

    def getFundamentalSampleTime(self):
        if self.fundamentalSampleTime is None:
            self.fundamentalSampleTime = self.__calculateFundamentalSampleTime()
        return self.fundamentalSampleTime

    def getSymbolicFixedPoint(self):
        return cUtils.to_int(self.symbolicFixedPoint)

    def getConnectionTable(self):
        return self.connectionTable
