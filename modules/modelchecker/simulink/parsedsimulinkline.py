
class ParsedSimulinkLine:
    def __init__(self):
        self.name = ""  # this is the same as the signal name
        self.signaltype == ""  # value assigned from SimulinkSignalTypeEnum
        self.sourceportnumber = -1  # this is the source port number
        self.destinationblock = {}  # this is supposed to be a parsed Simulink block
        self.destinationportnumber = -1  # this is the destination port number

    def getName(self):
        return self.name

    def setName(self, name):
        self.name = name

    def getSignalType(self):
        return self.signaltype

    def setSignalType(self, signaltype):
        self.signaltype = signaltype

    def getSourcePortNumber(self):
        return self.sourceportnumber

    def setSourcePortNumber(self, sourceprortnumber):
        self.sourceportnumber = sourceprortnumber

    def setDestinationBlock(self, parsedSimulinkBlock):
        self.destinationblock = parsedSimulinkBlock

    def getDestinationBlock(self):
        return self.destinationblock

    def setDestinationPortNumber(self, destinationportnumber):
        self.destinationportnumber = destinationportnumber

    def getDestionationPortNumber(self):
        return self.destinationportnumber
