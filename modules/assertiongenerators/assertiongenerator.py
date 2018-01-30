import re

class AssertionGenerator:
    def __init__(self):
        pass

    def __adjustInput(self, _input, step):
        assertionPattern = "^\(.*\)$"
        numberPattern = "^[-]?[0-9]*([.,][0-9]+)?$"

        if re.match(assertionPattern, _input) == None and re.match(numberPattern, _input) == None:
            _input = "{0}_{1}".format(_input, step)

        return _input

    def __extractInputs(self, sBlockPackage, step):
        inputs = sBlockPackage["inputs"]
        inputs = inputs.split(',')
        result = [None] * len(inputs)
        for _input in inputs:            
            parts = _input.split("#")
            portNumber = int(parts[0])
            result[portNumber - 1] = self.__adjustInput(parts[1], step)
        return result

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
        return assertion.format(signalname, simulationstep, _gain, inputs[0])

    def abs(self, sBlockPackage, simulationstep):
        iteTemplate = "(ite (< {1}_{2} 0) (= {0}_{2} (* -1 {1}_{2})) (= {0}_{2} {1}_{2}))"
        signalname = sBlockPackage["signalname"]
        _input = self.__extractInputs(sBlockPackage, simulationstep)
        return iteTemplate.format(signalname, _input, simulationstep)

    def relational(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        operator = sBlockPackage["parameters"]["relationtype"]
        return "(ite ({1} {2} {3}) (= {0} True) (= {0} False))".format(signalname, operator, inputs[0], inputs[1])

    def subtract(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        return "(= {0} (- {1} {2}))".format(signalname, inputs[0], inputs[1])

    def saturate(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        return "(= {0} (saturate {1}))".format(signalname, inputs[0])

    def switch(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        condition = sBlockPackage["parameters"]["condition"]
        condition = condition.replace("u2", inputs[1])
        return "(ite ({1}) (= {0} {2}) (= {0} {3}))".format(signalname, condition, inputs[0], inputs[2])

    def constant(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        _value = sBlockPackage["parameters"]["value"]
        return "(= {0}_{1} {2})".format(signalname, simulationstep, _value)
