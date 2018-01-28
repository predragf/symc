class StateSpace:

    def __init__(self):
        self.statespace = {}

    def addTrace(self, signalName, signalTrace):
        self.statespace[signalName] = signalTrace

    def getStateSpace(self):
        return self.statespace

    def getStateAtPosition(self, position):
        state = []
        _vars = self.statespace.keys()

        for _var in _vars:
            state.append(self.statespace[_var][position])

        return state
    def getStates(self, start, howmany):
        states = []
        for stateNo in range(start, start + howmany):
            states.append(self.getStateAtPosition(stateNo))

        return states
