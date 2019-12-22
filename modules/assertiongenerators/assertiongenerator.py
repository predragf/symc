import re


class AssertionGenerator:
    def __init__(self):
        pass

    def __adjustInput(self, _input, step):
        assertionPattern = "^\(.*\)$"
        numberPattern = "^[-]?[0-9]*([.,][0-9]+)?$"
        if (re.match(assertionPattern, _input) == None
                and re.match(numberPattern, _input) == None):
            _input = "{0}_{1}".format(_input, step)
        return _input

    def __extractInputs(self, sBlockPackage, step):
        inputs = sBlockPackage["inputs"]
        inputs = inputs.split(',')
        result = [None] * len(inputs)
        for _input in inputs:
            try:
                parts = _input.split("#")
                portNumber = int(parts[0])
                result[portNumber - 1] = self.__adjustInput(parts[1], step)
            except excp:
                print("Filed to extract input: {}".format(str(inputs)))
        return result

    def sum(self, sBlockPackage, simulationstep):
        # here one also needs to know the simulation step from which
        # the inputs shall be taken
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        assertion = "(= {0}_{1} (+ {2}_{1}))"
        return assertion.format(signalname, simulationstep, inputs)

    def gain(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        _gain = sBlockPackage["parameters"]["gain"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        assertion = "(= {0}_{1} (* {2} {3}))"
        return assertion.format(signalname, simulationstep, _gain, inputs[0])

    def abs(self, sBlockPackage, simulationstep):
        iteTemplate = """(ite (< {1}_{2} 0) (= {0}_{2}
                            (* -1 {1}_{2})) (= {0}_{2} {1}_{2}))"""
        signalname = sBlockPackage["signalname"]
        _input = self.__extractInputs(sBlockPackage, simulationstep)
        return iteTemplate.format(signalname, _input, simulationstep)

    def relational(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        operator = sBlockPackage["parameters"]["relationtype"]
        return """(ite ({1} {2} {3}) (= {0}_{4} 1)
        (= {0}_{4} 0))""".format(signalname, operator, inputs[0],
                                 inputs[1], simulationstep)

    def subtract(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        return "(= {0}_{3} (- {1} {2}))".format(signalname, inputs[0],
                                                inputs[1], simulationstep)

    def saturate(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        lowerLimit = sBlockPackage["parameters"]["lowerlimit"]
        upperLimit = sBlockPackage["parameters"]["upperlimit"]
        return """(and (=> (<= {2} {4}) (= {0}_{1} {4})) (=>
        (and (>= {2} {4}) (<= {2} {3})) (= {0}_{1} {2}))
        (=> (>= {2} {3}) (= {0}_{1} {3})))""".format(signalname, simulationstep,
                                                     inputs[0], upperLimit, lowerLimit)

    def switch(self, sBlockPackage, simulationstep):
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        signalname = sBlockPackage["signalname"]
        condition = sBlockPackage["parameters"]["condition"]
        condition = condition.replace("u2", inputs[1]).split(" ")
        condition = "{0} {1} {2}".format(condition[1], condition[0], condition[2])
        return """(ite ({1}) (= {0}_{4} {2}) (= {0}_{4} {3}))""".format(signalname,
                                                                        condition, inputs[0], inputs[2], simulationstep)

    def constant(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        _value = sBlockPackage["parameters"]["value"]
        return "(= {0}_{1} {2})".format(signalname, simulationstep, _value)

    def max(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        return """(ite (> {1} {2}) (= {0}_{3} {1}) (= {0}_{3} {2}))""".format(signalname,
                                                                              inputs[0], inputs[1], simulationstep)

    def abs(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        return """(ite (> {1} 0) (= {0}_{3} {1}) (= {0}_{3} (* -1 {1})))""".format(
            signalname, inputs[0], simulationstep)

    def product(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        return """(= {0} (* {1}))""".format(signalname, " ".join(inputs).lstrip())

    def unitdelay(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        # TODO: Implement this function.
        return ""

    def divide(self, sBlockPackage, simulationstep):
        signalname = sBlockPackage["signalname"]
        inputs = self.__extractInputs(sBlockPackage, simulationstep)
        # TODO: Implement this function.
        return ""
