import modules.utils.utils as cUtils
import time

class AssertionGeneratorUtils:

    @staticmethod
    def parseProductInputs(input_signals, operators):
        result = ""
        firstOperator = "1"
        template = "({0} {1} {2})"
        for index, _input in enumerate(_inputs):
            secondOperator = "{0}_{{0}}".format(_input)
            _operator = operators[index]
            result = template.format(_operator, firstOperator, secondOperator)
            firstOperator = result
        return result

    @staticmethod
    def parseSumInputs(input_signals, input_signal_types, operators):
        result = ""
        firstOperator = "0"
        template = "({0} {1} {2})"
        for index, _input in enumerate(input_signals):
            if cUtils.compareStringsIgnoreCase(input_signal_types[index], 'boolean'):
                secondOperator = '(bool2real {0}_{{0}})'.format(_input)
            else:
                secondOperator = "{0}_{{0}}".format(_input)
            _operator = operators[index]
            result = template.format(_operator, firstOperator, secondOperator)
            firstOperator = result
        return result

    @staticmethod
    def parseLogicInputs(inputSignals, input_signal_types, operator):
        result = ""
        if operator == "AND":
            firstOperator = "true"
            symbolic_operator = 'and'
            not_operator = ''
        elif operator == "OR":
            firstOperator = "false"
            symbolic_operator = 'or'
            not_operator = ''
        elif operator == "NAND":
            firstOperator = "true"
            symbolic_operator = 'and'
            not_operator = 'not'
        elif operator == "NOR":
            firstOperator = "false"
            symbolic_operator = 'or'
            not_operator = 'not'
        elif operator == "XOR":
            firstOperator = "false"
            symbolic_operator = 'xor'
            not_operator = ''
        elif operator == "NXOR":
            firstOperator = "false"
            symbolic_operator = 'or'
            not_operator = 'not'
        elif operator == "NOT":
            return "(not {0}_{{0}})".format(inputSignals[0]["SignalName"])
        else:
            return ""

        template = "({0} {1} {2})"
        for index, _input in enumerate(inputSignals):
            secondOperator = "{0}_{{0}}".format(_input["SignalName"]) if cUtils.compareStringsIgnoreCase(
                "boolean", _input["SignalType"]) else "(= 1 {0}_{{0}})".format(_input["SignalName"])
            result = template.format(symbolic_operator, firstOperator, secondOperator)
            firstOperator = result

        if not_operator == 'not':
            result = '(not {0})'.format(result)
        return result

    @staticmethod
    def parseSwitchInputs(inputSignals, criteria):
        firstSignal = [inputSignal for inputSignal in inputSignals if inputSignal["DstPort"] == 0][0]
        secondSignal = [inputSignal for inputSignal in inputSignals if inputSignal["DstPort"] == 1][0]
        thirdSignal = [inputSignal for inputSignal in inputSignals if inputSignal["DstPort"] == 2][0]
        result = ""
        criteria_operator = criteria[1]
        criteria_comparison = criteria[2]
        neq_operator = (criteria_operator == '~=')
        if neq_operator:
            criteria_operator = '='
            template = "(ite (not ({0} {1} {2})) {3} {4})"
        else:
            template = "(ite ({0} {1} {2}) {3} {4})"

        first_signal = "{0}_{{0}}".format(firstSignal["SignalName"])
        comparison_signal = "{0}_{{0}}".format(secondSignal["SignalName"]) if not cUtils.compareStringsIgnoreCase(
            "boolean", secondSignal["SignalType"]) else "(ite {0}_{{0}} 1 0)".format(secondSignal["SignalName"])
        third_signal = "{0}_{{0}}".format(thirdSignal["SignalName"])
        result = template.format(criteria_operator, comparison_signal,
                                 criteria_comparison, first_signal, third_signal)

        return result

    @staticmethod
    def parseIfInputs(input_signals, output_signals, criteria):
        result = []
        output_if = "{0}_{{0}}".format(output_signals[0])
        output_else = "{0}_{{0}}".format(output_signals[1])
        criteria_operator = criteria[1]
        criteria_comparison = criteria[2]
        neq_operator = (criteria_operator == '~=')
        if neq_operator:
            criteria_operator = '='
            template = "(ite (not ({0} {1} {2})) {3} {4})"
        else:
            template = "(ite ({0} {1} {2}) {3} {4})"

        comparison_signal = "{0}_{{0}}".format(input_signals[0])

        resultIf = template.format(criteria_operator, comparison_signal,
                                   criteria_comparison, "true", "false")
        resultElse = template.format(criteria_operator, comparison_signal,
                                     criteria_comparison, "false", "true")

        resultIfString = "(= {0}_{{0}} {1})".format(output_if, resultIf)
        resultElseString = "(= {0}_{{0}} {1})".format(output_else, resultElse)

        return (resultIfString, resultElseString)

    @staticmethod
    def generateVacousState(block):
        _output_signals = block.get("outputSignals")[0]
        _outSignal_name = _output_signals["SignalName"]
        return "(= {0}_{{0}} {0}_{{1}})".format(_outSignal_name)

    @staticmethod
    def generateInitialState(block):
        _initialConditionSource = block.get("InitialConditionSource")
        if cUtils.compareStringsIgnoreCase(_initialConditionSource, "external"):
            _initialSignal = generateInitialValueExternal(block)
            _initialvalue  = "{0}_0".format(_initialSignal)
        else:
            _initialvalue = block.get("InitialCondition")

        _output_signal = block.get("outputSignals")
        _output_signal = _output_signal[0]
        _output_signal_name = _output_signal.get("SignalName", "")

        if cUtils.compareStringsIgnoreCase(block.get("BlockType"), "UnitDelay"):
            if cUtils.compareStringsIgnoreCase(_output_signal.get("SignalType"), 'boolean'):
                _output_signal_string = "(bool2real {0}_0)".format(_output_signal_name)
            else:
                _output_signal_string = "{0}_0".format(_output_signal_name)
            return "(= {0} {1})".format(_output_signal_string, _initialvalue)

        _internalstatevariable = "{0}_{1}".format(block.get("Name"), int(block.get("Handle")))

        assertion = "(= {0}_0 {2})\n(= {0}_0 {1}_0)".format(_internalstatevariable, _output_signal_name, _initialvalue)
        return assertion

def generateInitialValueExternal(block):
    input_signals = block.get("inputSignals")
    external_signal = [input_signal for input_signal in input_signals if input_signal["DstPort"] == 2][0]
    initialSignal = external_signal["SignalName"]

    return initialSignal
