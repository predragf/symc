class DeclarationsGenerator(object):
    """docstring for DeclarationsGenerator."""

    @staticmethod
    def mapSignalTypeToSMTSort(self, signalType):
        mappingDict = {"double": "real", "uint8": "Int", "boolean": "Bool", "single": "Real"}
        return mappingDict.get(signalType)

    @staticmethod
    def generateDeclaration(self, cTableEntry):
        declarationString = "(declare-const {0}_{{0}} {1}})"
        return declarationString.format(cTableEntry.get("SignalName"), mapSignalTypeToSMTSort(cTableEntry.get("SignalType")))
