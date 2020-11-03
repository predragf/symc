import time
class DeclarationsGenerator():
    """docstring for DeclarationsGenerator."""

    @staticmethod
    def mapSignalTypeToSMTSort(signalType):
        mappingDict = {"double": "Real", "uint8": "Int",
                       "auto": "Real", "boolean": "Bool", "single": "Real"}
        return mappingDict.get(signalType)

    @staticmethod
    def generateDeclaration(cTableEntry):
        declarationString = "(declare-const {0}_{{0}} {1})"
        return declarationString.format(cTableEntry.get("SignalName"), DeclarationsGenerator.mapSignalTypeToSMTSort(cTableEntry.get("SignalType")))

    @staticmethod
    def generateDeclarations(cTable):
        declaredSignals = set()
        declarations = ""
        for entry in cTable:
            signalName = entry["SignalName"]
            if signalName in declaredSignals:
                continue
            declaredSignals.add(signalName)
            declarations = "{0} \n {1}".format(
                declarations, DeclarationsGenerator.generateDeclaration(entry))
        return declarations
