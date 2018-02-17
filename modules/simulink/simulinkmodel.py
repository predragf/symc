from modules.utils.gcd import *

class SimulinkModel:
    def __init__(self, _simulinkmodeljson):
        self.simulinkModelJson = _simulinkmodeljson.get("simulinkmodel")
        self.simulinkModelJson["signalvariables"] = self.__createVariables()
        self.simulinkModelJson["internalstatevariables"] = self.__createInternalStateVariables()

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

    def getAllConnections(self):
        return self.simulinkModelJson.get("connections")

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

    def _getBlockConnections(self, blockid, connectionType):
        allconnections = self.getAllConnections()
        blockConnections = []
        for connection in allconnections:
            if ((connectionType == "ouput" and
                    connection.get("sourceblockid") == blockid)
                or (connectionType == "input" and
                    connection.get("destinationblockid") == blockid)
                ):
                blockConnections.append(connection)
        return blockConnections

    def getBlockOutputConnections(self, blockid):
        return self._getBlockConnections(blockid, "ouput")

    def getBlockInputConnections(self, blockid):
        return self._getBlockConnections(blockid, "input")

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
