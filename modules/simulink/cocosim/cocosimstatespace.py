import re
import modules.utils.utils as cUtils


class StateSpace:

    def __init__(self, _stateSpace=dict(), _declarations=""):
        self.statespace = _stateSpace.copy()
        self.declarations = _declarations
        self.setDeclarationLib()

    def addState(self, position, state):
        self.statespace[position] = state

    def getStateSpace(self):
        return self.statespace

    def getStateAtPosition(self, position):
        return self.statespace.get(position, [])

    def getAllStates(self):
        allstates = []
        allstates.extend(self.statespace.values())
        return allstates

    def getStatesRange(self, start=0, howmany=0):
        states = []
        if howmany > 0:
            for stateNo in range(start, start + howmany):
                states.append(self.getStateAtPosition(stateNo))
        return states

    def setDeclarations(self, _declarations=""):
        self.declarations = _declarations

    def setDeclarationLib(self):
        declarationLib_string = ""
        libfile = open('declarationLib.txt', 'r')
        declarationLib_string = libfile.read()
        libfile.close()
        self.declarationLib = declarationLib_string

    def __getStatesForParsing(self, start=0, howmany=0):
        statesForParsing = []
        if howmany > 0:
            statesForParsing = self.getStatesRange(start, howmany)
        else:
            statesForParsing = self.getAllStates()
        return statesForParsing

    def __extractVariables(self, assertion):
        _vars = set()
        smtKeywords = ["ite", "assert", "and", "or"]
        generalPattern = re.compile("[a-zA-Z0-9_]+")
        numberPattern = re.compile("^[-]?[0-9]*([.,][0-9]+)?$")
        matches = generalPattern.findall(assertion)
        for m in matches:
            if (numberPattern.match(m) == None and
                    m.lower() not in smtKeywords):
                _vars.add(m)
        return _vars

    def __loadCustomFunctions(self, customFunctionsFileLocation):
        cFunctions = ""
        try:
            _file = open(customFunctionsFileLocation, "r")
            cFunctions = _file.read()
        except:
            print("{0} could not be loaded.".format(pathToJsonFile))
        return cFunctions

    def getDeclarations(self):
        return self.declarations

    def getDeclarationLib(self):
        return self.declarationLib

    def getAssertions(self, start=0, howmany=0):
        statesForParsing = self.__getStatesForParsing(start, howmany)
        stateAssertions = ""
        for state in statesForParsing:
            if not cUtils.compareStringsIgnoreCase(str(state).strip(), ""):
                stateAssertions += "\n".join(state)
        return stateAssertions

    def getSMTScript(self):
        return "{0}\n{1}".format(self.getDeclarations(), self.getAssertions())
