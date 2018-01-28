class AssertionGenerator:
    def __init__(self):
        pass

    def __extractInputs(self, sBlockPackage):
        inputs = sBlockPackage["inputs"]
        inputs = inputs.split(',')
        return " ".join(inputs)

    def add(self, sBlockPackage, simulationstep):
        #here one also needs to know the simulation step from which
        #the inputs shall be taken
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage)
        assertion = "(= {0}_{1} (+ {2}))"
        return assertion.format(signalname, simulationstep, inputs)

    def gain(self, sBlockPackage, simulationstep):
        pass
