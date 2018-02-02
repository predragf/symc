import re

class StateSpace:

    def __init__(self, _stateSpace={}):
        self.statespace = _stateSpace

    def addTrace(self, signalName, signalTrace):
        self.statespace[signalName] = signalTrace

    def getStateSpace(self):
        return self.statespace

    def __getStateSpaceVariables(self):
        return self.statespace.keys()

    def getStateAtPosition(self, position):
        state = []
        _vars = self.__getStateSpaceVariables()

        for _var in _vars:
            state.append(self.statespace[_var][position])

        return state

    def getAllStates(self):
        states = []
        _vars = self.__getStateSpaceVariables()
        if len(_vars) > 0:
            numberOfStates = len(self.statespace[_vars[0]])
            for position in range(0, numberOfStates):
                state = []
                for _var in _vars:
                    state.append(self.statespace[_var][position])
                    states.append(state)
        return states

    def getStatesRange(self, start=0, howmany=0):
        states = []
        if howmany > 0:
            for stateNo in range(start, start + howmany):
                states.append(self.getStateAtPosition(stateNo))
        return states

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

    def __generateDeclarations(self, variables):
        declarations = []
        for _var in variables:
            declarations.append("(declare-const {0} Real)".format(_var))
        return declarations

    def genenrateSMT2Script(self, start=0, howmany=0):
        statesForParsing = self.__getStatesForParsing(start, howmany)
        assertions = []
        allVars = set()
        for state in statesForParsing:
            for assertion in state:
                _vars = self.__extractVariables(assertion)
                allVars = allVars | _vars
                assertions.append("(assert {0})".format(assertion))
        print("The model has {0} variables".format(len(allVars)))
        declarationsAssertions = self.__generateDeclarations(allVars)
        return "{0} \n {1}".format("\n".join(declarationsAssertions),
                                    "\n".join(assertions))
