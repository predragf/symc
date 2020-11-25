import time
import modules.utils.utils as cUtils

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
    def generateDeclarations(sModel, cTable):
        declaredSignals = set()
        declaredInternalSignals = set()
        declarations = ""
        fileCTable = open('CTable.txt', 'w')
        for entry in cTable:
            signalName = entry["SignalName"]
            fileCTable.writelines(str(entry) + '\n')
            entryBlock = sModel.getBlockById(entry["DstBlockHandle"])
            if cUtils.compareStringsIgnoreCase(entryBlock.get("BlockType"), "DiscreteIntegrator"):
                internal_variable = "{0}_{1}".format(entryBlock.get("Name"), int(entryBlock.get("Handle")))
                if internal_variable not in declaredInternalSignals:
                    declaredInternalSignals.add(internal_variable)
                    internal_variable_type = "Real"
                    internal_declaration = "(declare-const {0}_{{0}} {1})".format(internal_variable, internal_variable_type)
                    declarations = "{0} \n {1}".format(declarations, internal_declaration)
            if signalName in declaredSignals:
                continue
            declaredSignals.add(signalName)
            declarations = "{0} \n {1}".format(
                declarations, DeclarationsGenerator.generateDeclaration(entry))

        fileCTable.close()

        return declarations
