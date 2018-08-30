class Block:
    def __init__(self, _name, _ts, _initialvalue, _function, _inputs):
        self.name = _name
        self.ts = _ts
        self.initialvalue = _initialvalue
        self.function = _function
        self.inputs = _inputs
        self.output = ""

    def generateStep(self, _step):
        output = ""
        if _step < self.ts:
            output = self.initialvalue
        else:
            output = self.function
            for _blk in self.inputs:
                replacement = "#{0}#".format(_blk.getName())
                output = output.replace(replacement, _blk.getOutput)

    def getOutput(self):
        return self.output

    def getName(self):
        return self.name
