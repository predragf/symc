import modules.utils.utils as cUtils


class CoCoSimModel:

    def __init__(self, _simulinkmodeljson, _slist, _configuration={}):
        self.rawSimulinkModelJson = _simulinkmodeljson
        self.flatSimulinkModelJson = {}
        self.signalvariables = []
        self.internalstatevariables = []
        self.compositeBlockTypes = ["subsystem"]
        self.noncomputationalBlocks = _configuration.get("noncomputationalblocks", [])
        self.portBlockTypes = ["inport", "outport"]
        self.connectionTable = None
        self.__adjustExecutionOrder(_slist)

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
            if  not (cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "inport") or cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "Outport")):
                compiledInPortTypes = compiledInPortTypes.get("Inport")
            elif cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "inport"):
                compiledInPortTypes = compiledInPortTypes.get("Outport")
            elif cUtils.compareStringsIgnoreCase(block.get("BlockType", ""), "outport"):
                compiledInPortTypes = compiledInPortTypes.get("Inport")
            if type(compiledInPortTypes) is not list:
                compiledInPortTypes = [compiledInPortTypes]
            signalType = compiledInPortTypes[int(portNumber) - 1]
        except Exception as exc:
            print("extract signal failed: {0}:{1}:{2}".format(block.get("BlockType"), block.get("Origin_path"), exc))
            pass
        return signalType

    def __createConnectionTableEntry(self, destinationBlock, outConnectionOfDestinationBlock, signalIdentifier):

        result = {
        "SrcBlockHandle": outConnectionOfDestinationBlock.get("SrcBlock"),
        "SrcPort": outConnectionOfDestinationBlock.get("SrcPort",""),
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
        result = {}
        for entry in _partialTable:
            if entry.get("DstBlockHandle", "") == _handle and entry.get("DstPort") == _port:
                result = entry
                break
        return result

    def __traceSubSystem(self, ssBlock, connection, partialTable):
        ssContent = ssBlock.get("Content", {})
        for blkId in ssContent:
            try:
                childBlock = ssContent.get(blkId, {})
                portBlockPortNumber = childBlock.get("Port", "-100")
                connectionPortNumber = connection.get("SrcPort", "-123")
                print("-----+++++{0}".format(connectionPortNumber))
                if connectionPortNumber == "":
                    print(childBlock.get("BlockType"))
                if cUtils.compareStringsIgnoreCase(childBlock.get("BlockType", ""), "Outport") and int(portBlockPortNumber) == int(connectionPortNumber) + 1:
                    print("fnatre")
                    _handle = repr(childBlock.get("Handle", ""))
                    _port = childBlock.get("Port", "")
                    newConnection = self.__findEntryByDestination(_handle, _port, partialTable)
                    newConnection = self.__mapConnectionSource(newConnection, partialTable)
                    connection["SrcBlockHandle"] = newConnection.get("SrcBlockHandle", "")
                    connection["SrcPort"] = newConnection.get("SrcPort", "")
            except Exception as e:
                print("failure: {0}:{1}".format(e, blkId))
                pass
        return connection

    def __mapConnectionSource(self, connection, partialTable):
        """
        Initially the connections have been created. However, some of the sources might be
        an atomic computational block and in such cases we must find the atomic computational block which writes to that signal
        """
        sourceBlock = self.getBlockById(connection.get("SrcBlockHandle", ""))
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "subsystem"):
            connection = self.__traceSubSystem(sourceBlock, connection, partialTable)
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "demux"):
            pass
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "mux"):
            pass
        if cUtils.compareStringsIgnoreCase(sourceBlock.get("BlockType", ""), "inport"):
            pass
        return connection

    def createConnectionTable(self):
        connectionTable = self.__createAllDestinationEntries()
        for connection in connectionTable:
            connection = self.__mapConnectionSource(connection, connectionTable)
            pass
        return connectionTable

    def __flattenSubSystem(self, ssBlock):
        # this is fully implemented
        allBlocks = [ssBlock]
        innerContents = ssBlock.get("Content", {})
        ssBlockId = ssBlock.get("Handle", "")
        for blkName in innerContents:
            blk = innerContents.get(blkName)
            try:
                if any(cUtils.compareStringsIgnoreCase(s, blk.get("BlockType", None)) for s in self.compositeBlockTypes):
                    allBlocks.extend(self.__flattenSubSystem(blk))
                else:
                    blk["ParentHandle"] = ssBlockId
                    allBlocks.append(blk)
            except:
                continue
        return allBlocks

    def flatenSimulinkModel(self):
        # this needs to be made private when done
        result = self.__createAllDestinationEntries()
        return result

    def __adjustExecutionOrder(self, _slist):
        # implemented
        for blk in self.getAllBlocks():
            blockPath = blk.get("Origin_path", "").lower()
            """ execution order - 1 denotes that it has no execution order
             that is, it is not included in the slist and as such
             sould not be included in the transformation"""
            _number = int(_slist.get(blockPath, "-1"))
            blk["ExecutionOrder"] = str(_number).zfill(2)

    def __getModelMetaData(self):
        # implemented
        sModelJson = self.getModelJSON()
        metaData = sModelJson.get("meta")
        return metaData if metaData is not None else {}

    def getModelName(self):
        # implemented
        defaultValue = ""
        metaData = self.__getModelMetaData()
        modelName = metaData.get("file_path")
        return modelName if modelName is not None else defaultValue

    def getModelJSON(self):
        # getter function
        return self.rawSimulinkModelJson

    # mandatory set of functions start

    def getAllBlocks(self):
        # this is fully implemented
        allBlocks = []
        firstLevelComposite = 0
        content = self.rawSimulinkModelJson.get(
            self.getModelName()).get("Content", {})
        for blkId in content:
            try:
                blk = content.get(blkId)
                if blk.get("BlockType", "").lower() in self.compositeBlockTypes:
                    allBlocks.extend(self.__flattenSubSystem(blk))
                else:
                    allBlocks.append(blk)
            except:
                continue
        return allBlocks

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

    def packAllBlocksForTransformation(self):
        raise Exception("To be implemented")

    def calculateFundamentalSampleTime(self):
        raise Exception("To be implemented")

    # mandatory set of functions end
