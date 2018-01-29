class AssertionGenerator:
    def __init__(self):
        pass

    def __extractInputs(self, sBlockPackage, step):
        inputs = sBlockPackage["inputs"]
        inputs = inputs.split(',')
        return "_{0} ".format(step).join(inputs)

    def add(self, sBlockPackage, simulationstep):
        #here one also needs to know the simulation step from which
        #the inputs shall be taken
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        assertion = "(= {0}_{1} (+ {2}_{1}))"
        return assertion.format(signalname, simulationstep, inputs)

    def gain(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        _gain = sBlockPackage["parameters"]["gain"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        assertion = "(= {0}_{1} (* {2} {3}_{1}))"
        return assertion.format(signalname, simulationstep, _gain, inputs)

    def abs(self, sBlockPackage, simulationstep):
        iteTemplate = "(ite (< {1}_{2} 0) (= {0}_{2} (* -1 {1}_{2})) (= {0}_{2} {1}_{2}))"
        signalname = sBlockPackage["signalname"]
        _input = self.__extractInputs(sBlockPackage, simulationstep)
        return iteTemplate.format(signalname, _input, simulationstep)

    def greaterThan(self, sBlockPackage, simulationstep):
        #to be implemented
        pass

    def subtract(self, sBlockPackage, simulationstep):
        #to be implemented
        pass
