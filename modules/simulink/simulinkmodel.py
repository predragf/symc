from modules.utils.gcd import *

class SimulinkModel:
    def __init__(self, _simulinkmodeljson):
        self.simulinkModelJson = _simulinkmodeljson["simulinkmodel"]
        self.simulinkModelJson["signalvariables"] = self.__createVariables()

    def __getLinesFromSameSource(self, _pivot, _allLines):
        samelines = []
        samelines.append(_pivot)
        indexesForPopping = []

        for i in range(0, len(_allLines)):
            if(_allLines[i]["sourceblockid"] == _pivot["sourceblockid"] and
                _allLines[i]["sourceportnumber"] == _pivot["sourceportnumber"]):
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
                variables[line["name"]] = "signal_variable_{0}".format(variableIndex)
            variableIndex = variableIndex + 1

        return variables

    def __processModel(self):
        pass

    def getAllBlocks(self):
        return self.simulinkModelJson["blocks"]

    def getAllConnections(self):
        return self.simulinkModelJson["connections"]

    def getAllInputs(self):
        return self.simulinkModelJson["inputs"]

    def getAllOutputs(self):
        return self.simulinkModelJson["outputs"]

    def getBlockById(self, blockid):
        result = {}
        allBlocks = self.getAllBlocks()
        for block in allBlocks:
            if block["blockid"] == blockid:
                result = block
                break
        return result

    def getAllConnections(self):
        return self.simulinkModelJson["connections"]

    def getSignalVariables(self):
        return self.simulinkModelJson["signalvariables"]

    def getConnectionSignalVariable(self, _lineName):
        allSignalVariables = self.getSignalVariables()
        return allSignalVariables[_lineName]

    def getModelName(self):
        modelName = self.simulinkModelJson["modelname"]
        if modelName is None:
            modelName = ""
        return modelName

    def _getBlockConnections(self, blockid, connectionType):
        allconnections = self.getAllConnections()
        blockConnections = []
        for connection in allconnections:
            if ((connectionType == "ouput" and
                    connection["sourceblockid"] == blockid)
                or (connectionType == "input" and
                    connection["destinationblockid"] == blockid)
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
            if connection["destinationblockid"] == blockid:
                result.append(connection)
        return result

    def getBlockPredecessors(self, blockid):
        predecessors = []
        modelConnections = self.getAllConnections()
        for connection in modelConnections:
            if connection["destinationblockid"] == blockid:
                sourceblockid = connection["sourceblockid"]
                sourceBlock = self.getBlockById(sourceblockid)
                predecessors.append(sourceBlock)
        return predecessors

    def __createInputs(self, blockid):
        inputconnections = self.getBlockInputConnections(blockid);
        inputs = ""
        for iconn in inputconnections:
            inputs += "{0}#{1}#{2},".format(iconn["destinationportnumber"],
                                        iconn["name"],
                                        self.getConnectionSignalVariable(iconn["name"]))
        return inputs[:len(inputs) - 1]

    def packBlockForTransformation(self, blockid):
        blockForTransformation = self.getBlockById(blockid)
        outConns = self.getBlockOutputConnections(blockid)
        blockForTransformation["inputs"] = self.__createInputs(blockid)
        if len(outConns) > 0:
            blockForTransformation["signalname"] = outConns[0]["name"]
        else:
            blockForTransformation["signalname"] = ""            

        return blockForTransformation

    def calculateFundamentalSampleTime(self):
        allBlocks = self.getAllBlocks()
        sampletimes = set()
        for block in allBlocks:
            ts = block["sampletime"]
            if ts == 0:
                '''-1 denotes that there is at least one continuous-time
                block which means that we must construct the complete state space
                '''
                return -1
            else:
                sampletimes.add(ts)
        return gcdList(list(sampletimes))
