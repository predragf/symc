class CoCoSimModel:

    def __init__(self, _simulinkmodeljson, _slist):
        self.rawSimulinkModelJson = _simulinkmodeljson
        self.flatSimulinkModelJson = {}
        self.signalvariables = []
        self.internalstatevariables = []
        self.compositeBlockTypes = ["subsystem"]
        self.__adjustExecutionOrder(_slist)

    def __flattenSubSystem(self, ssBlock):
        # this is fully implemented
        atomicBlocks = []
        innerContents = ssBlock.get("Content", {})
        for blkName in innerContents:
            blk = innerContents.get(blkName)
            try:
                if blk.get("BlockType", "")in self.compositeBlockTypes:
                    atomicBlocks.extend(self.__flattenSubSystem(blk))
                else:
                    atomicBlocks.append(blk)
            except:
                continue
        return atomicBlocks

    def __flatenSimulinkModel(self):
        

    def __getBlocksFirstLevel(self):
        # this is fully imeplemented
        blocks = []
        nonExisting = "Non-Existing"
        content = self.rawSimulinkModelJson.get(self.getModelName()).get("Content", {})
        for item in content:
            block = content.get(item)
            try:
                if not block.get("BlockType", nonExisting) == nonExisting:
                    blocks.append(block)
            except:
                continue
        return blocks

    def __adjustExecutionOrder(self, _slist):
        # implemented
        for blk in self.getAllBlocks():
            blockPath = blk.get("Path", "").lower()
            """ execution order -1 denotes that it has no execution order
             that is, it is not included in the slist and as such
             sould not be included in the transformation"""
            blk["ExecutionOrder"] = _slist.get(blockPath, "-1")

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
        atomicBlocks = []
        for blk in self.__getBlocksFirstLevel():
            try:
                if blk.get("BlockType", "").lower() in self.compositeBlockTypes:
                    atomicBlocks.extend(self.__flattenSubSystem(blk))
                else:
                    atomicBlocks.append(blk)
            except:
                continue
        return atomicBlocks

    def getBlocksForTransformation(self):
        raise Exception("To be implemented")

    def getModelVariables(self):
        raise Exception("To be implemented")

    def packAllBlocksForTransformation(self):
        raise Exception("To be implemented")

    def calculateFundamentalSampleTime(self):
        raise Exception("To be implemented")

    # mandatory set of functions end
