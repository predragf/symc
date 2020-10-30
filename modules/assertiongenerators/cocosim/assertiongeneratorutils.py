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
    def parseLogicInputs(input_signals, operator):
        result = ""
        if operator == "AND":
            firstOperator     = "True"
            symbolic_operator = 'and'
            not_operator      = ''
        elif operator == "OR":
            firstOperator     = "False"
            symbolic_operator = 'or'
            not_operator      = ''
        elif operator == "NAND":
            firstOperator     = "True"
            symbolic_operator = 'and'
            not_operator      = 'not'
        elif operator == "NOR":
            firstOperator     = "False"
            symbolic_operator = 'or'
            not_operator      = 'not'
        elif operator == "XOR":
            firstOperator     = "False"
            symbolic_operator = 'xor'
            not_operator      = ''
        elif operator == "NXOR":
            firstOperator     = "False"
            symbolic_operator = 'or'
            not_operator      = 'not'
        elif operator == "NOT":
            return "(not {0}_{{0}})".format(input_signal[0])
        else:
            return ""

        template = "({0} {1} {2})"
        for index, _input in enumerate(input_signals):
            secondOperator = "{0}_{{0}}".format(_input)
            result         = template.format(symbolic_operator, firstOperator, secondOperator)
            firstOperator  = result

        if not_operator == 'not':
            result = '(not {0})'.format(result)
        return result

    @staticmethod
    def parseSwitchInputs(input_signals, criteria):
        result = ""
        criteria_operator   = criteria[1]
        criteria_comparison = criteria[2]
        neq_operator        = (criteria_operator == '~=')
        if neq_operator:
            criteria_operator = '='
            template          = "(ite not ({0} {1} {2}) {3} {4})"
        else:
            template          = "(ite ({0} {1} {2}) {3} {4})"

        first_signal        = "{0}_{{0}}".format(input_signals[0])
        comparison_signal   = "{0}_{{0}}".format(input_signals[1])
        third_signal        = "{0}_{{0}}".format(input_signals[2])

        result = template.format(criteria_operator, comparison_signal, criteria_comparison, first_signal, third_signal)

        return result

    @staticmethod
    def parseIfInputs(input_signals, output_signals, criteria):
        result = []
        output_if           = "{0}_{{0}}".format(output_signals[0])
        output_else    	    = "{0}_{{0}}".format(output_signals[1])
        criteria_operator   = criteria[1]
        criteria_comparison = criteria[2]
        neq_operator        = (criteria_operator == '~=')
        if neq_operator:
            criteria_operator = '='
            template            = "(ite not ({0} {1} {2}) {3} {4})"
        else:
            template            = "(ite ({0} {1} {2}) {3} {4})"

        comparison_signal   = "{0}_{{0}}".format(input_signals[0])

        resultIf         = template.format(criteria_operator, comparison_signal, criteria_comparison, "True", "False")
        resultElse       = template.format(criteria_operator, comparison_signal, criteria_comparison, "False", "True")

        resultIfString   = "(= {0}_{{0}} {1})".format(output_if, resultIf)
        resultElseString = "(= {0}_{{0}} {1})".format(output_else, resultElse)
        
        return (resultIfString, resultElseString)

    @staticmethod
    def generateVacousState(block, cTable):
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
