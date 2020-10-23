class DeclarationsGenerator():
    """docstring for DeclarationsGenerator."""

    @staticmethod
    def mapSignalTypeToSMTSort(signalType):
        mappingDict = {"double": "Real", "uint8": "Int", "boolean": "Bool", "single": "Real"}
        return mappingDict.get(signalType)

    @staticmethod
    def generateDeclaration(cTableEntry):
        declarationString = "(declare-const {0}_{{0}} {1})"
        return declarationString.format(cTableEntry.get("SignalName"), DeclarationsGenerator.mapSignalTypeToSMTSort(cTableEntry.get("SignalType")))

    @staticmethod
    def generateDeclarations(cTable):
        declarations = ""
        for entry in cTable:
            declarations = "{0} \n {1}".format(
                declarations, DeclarationsGenerator.generateDeclaration(entry))
        return declarations
