import modules.utils.utils as cUtils


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
    def parseSumInputs(input_signals, operators):
        result = ""
        firstOperator = "0"
        template = "({0} {1} {2})"
        for index, _input in enumerate(input_signals):
            secondOperator = "{0}_{{0}}".format(_input)
            _operator = operators[index]
            result = template.format(_operator, firstOperator, secondOperator)
            firstOperator = result
        return result

    @staticmethod
    def parseLogicInputs(inputSignals, operator):
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
        _outSignalName = block.get("signalvariable")
        return "(= {0}_{{0}} {0}_{{1}})".format(_outSignalName)

    @staticmethod
    def generateInitialState(block):
        _internalstatevariable = block.get("internalstatevariable")
        _outSignalName = block.get("signalvariable")
        _parameters = block.get("parameters")
        _initialvalue = _parameters.get("initialvalue", "-726")
        assertion = "(and (= {0}_0 {2}) (= {0}_0 {1}_0))".format(
            _internalstatevariable, _outSignalName, _initialvalue)
        return assertion
