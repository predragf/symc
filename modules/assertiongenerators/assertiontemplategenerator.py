from modules.assertiongenerators.assertiongeneratorutils import *

class AssertionTemplateGenerator:

    @staticmethod
    def abs(blockForTransformation):
        _input = blockForTransformation.get("inputs")[0]
        inputSignalName = _input.get("signalvariable")
        signalName = blockForTransformation.get("signalvariable")
        return "(ite (>= {0}_{{0}} 0.0) (= {1}_{{0}} {0}_{{0}}) (= {1}_{{0}} (- {0}_{{0}})))".format(inputSignalName, signalName)

    @staticmethod
    def constant(blockForTransformation):
        signalName = blockForTransformation.get("signalvariable")
        parameters = blockForTransformation.get("parameters")
        constantValue = parameters.get("value")
        return "(= {0}_{{0}} {1})".format(signalName, constantValue)

    @staticmethod
    def gain(blockForTransformation):
        _input = blockForTransformation.get("inputs")[0]
        inputSignalName = _input.get("signalvariable")
        signalName = blockForTransformation.get("signalvariable")
        parameters = blockForTransformation.get("parameters")
        gain = parameters.get("gain")
        return "(= {0}_{{0}} (* {1}_{{0}} {2}))".format(signalName,
                                                        inputSignalName, gain)

    @staticmethod
    def minmax(blockForTransformation):
        _firstInput = blockForTransformation.get("inputs")[0]
        _secondInput = blockForTransformation.get("inputs")[1]
        _firstSignalName = _firstInput.get("signalvariable")
        _secondSignalName = _secondInput.get("signalvariable")

        _outSignalName = blockForTransformation.get("signalvariable")

        _parameters = blockForTransformation.get("parameters")
        _mode = _parameters.get("mode")
        _operator = "<"
        if _mode.lower() == "max":
            _operator = ">"

        return "(ite ({0} {1}_{{0}} {2}_{{0}}) (= {3}_{{0}} {1}_{{0}}) (= {3}_{{0}} {2}_{{0}}))".format(_operator, _firstSignalName, _secondSignalName, _outSignalName)

    @staticmethod
    def product(blockForTransformation):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _inputsString = AssertionGeneratorUtils.parseProductInputs(blockForTransformation)
        return "(= {0}_{{0}} {1})".format(_outSignalName, _inputsString)

    @staticmethod
    def sum(blockForTransformation):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _inputsString = AssertionGeneratorUtils.parseSumInputs(blockForTransformation)
        return "(= {0}_{{0}} {1})".format(_outSignalName, _inputsString)

    @staticmethod
    def relationaloperator(blockForTransformation):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _parameters = blockForTransformation.get("parameters")
        _operator = _parameters.get("relationtype")

        _firstInput = blockForTransformation.get("inputs")[0]
        _secondInput = blockForTransformation.get("inputs")[1]

        _firstSignalName = _firstInput.get("signalvariable")
        _secondSignalName = _secondInput.get("signalvariable")

        return "(ite ({0} {1}_{{0}} {2}_{{0}}) (= {3}_{{0}} 1) (= {3}_{{0}} 0))".format(_operator, _firstSignalName, _secondSignalName, _outSignalName)

    @staticmethod
    def saturate(blockForTransformation):
        _parameters = blockForTransformation.get("parameters")
        _input = blockForTransformation.get("inputs")[0]
        _inputSignalName = _input.get("signalvariable")
        _outSignalName = blockForTransformation.get("signalvariable")

        _lowerLimit = _parameters.get("lowerlimit")
        _upperLimit = _parameters.get("upperlimit")

        return "(ite (> {0}_{{0}} {2}) (= {1}_{{0}} {2}) (ite (< {0}_{{0}} {3}) (= {1}_{{0}} {3}) (= {0}_{{0}} {1}_{{0}})))".format(_inputSignalName, _outSignalName, _upperLimit, _lowerLimit)

    @staticmethod
    def signum(blockForTransformation):
        _input = blockForTransformation.get("inputs")[0]
        _inputSignalName = _input.get("signalvariable")
        _outSignalName = blockForTransformation.get("signalvariable")
        return "(ite (= {0}_{{0}} 0) (= {1}_{{0}} 0) (ite (< {0}_{{0}} 0) (= {1}_{{0}} -1) (= 1 {1}_{{0}})))".format(_inputSignalName, _outSignalName)

    @staticmethod
    def switch(blockForTransformation):
        _parameters = blockForTransformation.get("parameters")
        _firstInput = blockForTransformation.get("inputs")[0]
        _controlInput = blockForTransformation.get("inputs")[1]
        _secondInput = blockForTransformation.get("inputs")[2]
        _outSignalName = blockForTransformation.get("signalvariable")
        condition = _parameters.get("condition")
        condition = condition.split(" ")
        return "(ite ({0} {1}_{{0}} {2}) (= {3}_{{0}} {4}_{{0}}) (= {3}_{{0}} {5}_{{0}}))".format(condition[1], _controlInput.get("signalvariable"), condition[2], _outSignalName, _firstInput.get("signalvariable"), _secondInput.get("signalvariable"))

    @staticmethod
    def round(blockForTransformation):
        _input = blockForTransformation.get("inputs")[0]
        _outSignalName = blockForTransformation.get("signalvariable")
        return """(ite (>= 0.5 (- {0}_{{0}} (to_int {0}_{{0}}))) (= {1}_{{0}} (to_int {0}_{{0}})) (= {1}_{{0}}
        (+ 1 (to_int {0}_{{0}}))))""".format(
                                            _input.get("signalvariable"), _outSignalName)

    @staticmethod
    def unitdelay(blockForTransformation):
        _outSignalName = blockForTransformation.get("signalvariable")
        _stateVariable = blockForTransformation.get("internalstatevariable", "")
        _input = blockForTransformation.get("inputs")[0]
        #assertion = """(and (= {0}_{{0}} {1}_{{1}}) (= {1}_{{0}} {2}_{{0}}))""".format(
                                        #_outSignalName, _stateVariable, _input.get("signalvariable"))
        assertion = "(= {0}_{{0}} {1}_{{1}})".format(_outSignalName, _input.get("signalvariable"))
        return assertion

    @staticmethod
    def rt(blockForTransformation):
        result = AssertionTemplateGenerator.unitdelay(blockForTransformation)
        return result

    @staticmethod
    def stateflow(blockForTransformation):
        _outSignalName = blockForTransformation.get("signalvariable")
        _input1 = blockForTransformation.get("inputs")[0]
        _input2 = blockForTransformation.get("inputs")[1]
        assertionTemplate = "(= {0}_{{0}} (BSR {1}_{{0}} {2}_{{0}}))".format(_outSignalName,
        _input1.get("signalvariable"), _input2.get("signalvariable"))
        return assertionTemplate

    @staticmethod
    def lookup(blockForTransformation):
        _outSignalName = blockForTransformation.get("signalvariable")
        _input1 = blockForTransformation.get("inputs")[0]
        assertionTemplate = "(= {0}_{{0}} (LOOKUP {1}_{{0}}))".format(_outSignalName,
        _input1.get("signalvariable"))
        return assertionTemplate

    @staticmethod
    def generateInitialConfiguration(blockForTransformation):
        _parameters = blockForTransformation.get("parameters")
        _outSignalName = blockForTransformation.get("signalvariable", "")
        _initalvalue = _parameters.get("initialvalue", "")
        _initialConditionAssertion = "no initial state"
        if not (_initalvalue == ""):
            _initialConditionAssertion = "(= {0}_0 {1})".format(_outSignalName,
            _initalvalue)
        return _initialConditionAssertion


    @staticmethod
    def modelinput(blockForTransformation):
        return ""

    @staticmethod
    def generateBlockAssertion(blockForTransformation):
        blocktype = blockForTransformation.get("blocktype")
        assertion = ""
        try:
            assertiongenerationfunction = getattr(AssertionTemplateGenerator, blocktype)
            assertion = assertiongenerationfunction(blockForTransformation)
        except Exception as e:
            """for now we handle the exception. bad coding practice, but will be
            rewritten in future"""
            assertion = str(e)
        return assertion

    @staticmethod
    def generateConstantDeclarationAssertion(signalName):
        declarationTemplate = "(declare-const {0}_{{0}} Real)"
        return declarationTemplate.format(signalName)
