class RoutineGenerator:
    def __init__(self):
        pass

    def add(self, sBlockPackage, simulationstep):
        inputs = sBlockPackage["inputs"]
        inputs = inputs.split(',')
        expression = ""
        for i in range(0, (len(inputs) - 1)):
            expression += inputs[i] + " + "
        expression += inputs[len(inputs) - 1]
        signal = sBlockPackage["signalname"]
        return "{0}_{1} = {2}".format(signal, simulationstep, expression)

    def abs(self, sBlockPackage):
        pass

    def gain(self, sBlockPackage):
        pass
