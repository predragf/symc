from modules.utils.gcd import *

class SimulinkModel:
    def __init__(self, _simulinkmodeljson):
        self.simulinkModelJson = _simulinkmodeljson["simulinkmodel"]

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

    def packBlockForTransformation(self, blockid):
        blockForTransformation = self.getBlockById(blockid)
        outConns = self.getBlockOutputConnections(blockid)
        blockForTransformation["signalname"] = outConns[0]["name"]
        inputconnections = self.getBlockInputConnections(blockid);
        inputs = ""
        for iconn in inputconnections:
            inputs += "{0}#{1},".format(iconn["destinationportnumber"],
                                        iconn["name"])
        inputs = inputs[:len(inputs) - 1]
        blockForTransformation["inputs"] = inputs
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
