class Simulator:

    def __init__(self, _listOfBlocks=[]):
        self.blocks = _listOfBlocks
        self.trace = []

    def __orderBlocksByExecutionId(self):
        self.blocks = sorted(self.blocks, key=lambda k: k[executionOrder])

    def simulate(self, simulationDuration):
        for step in range(0, simulationDuration):
