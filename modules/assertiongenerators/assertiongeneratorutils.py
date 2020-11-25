class AssertionGeneratorUtils:

    @staticmethod
    def parseProductInputs(productBlock):
        result = ""
        _inputs = productBlock.get("inputs")
        _parameters = productBlock.get("parameters")
        _opInputs = _parameters.get("inputs")
        firstOperator = "1"
        template = "({0} {1} {2})"
        for index, _input in enumerate(_inputs):
            secondOperator = "{0}_{{0}}".format(_input.get("signalvariable"))
            _operator = _opInputs[index]
            result = template.format(_operator, firstOperator, secondOperator)
            firstOperator = result
        return result

    @staticmethod
    def parseSumInputs(sumBlock):
        result = ""
        _inputs = sumBlock.get("inputs")
        _parameters = sumBlock.get("parameters")
        _opInputs = _parameters.get("signs")
        firstOperator = "0"
        template = "({0} {1} {2})"
        for index, _input in enumerate(_inputs):
            secondOperator = "{0}_{{0}}".format(_input.get("signalvariable"))
            _operator = _opInputs[index]
            result = template.format(_operator, firstOperator, secondOperator)
            firstOperator = result
        return result

    @staticmethod
    def generateVacousState(block):
        _outSignalName = block.get("signalvariable")
        return "(= {0}_{{0}} {0}_{{1}})".format(_outSignalName)

    @staticmethod
    def generateInitialState(block):
        print('Inside')
        _internalstatevariable = block.get("internalstatevariable")
        _outSignalName = block.get("signalvariable")
        _parameters = block.get("parameters")
        _initialvalue = _parameters.get("initialvalue", "-726")
        assertion = "(and (= {0}_0 {2}) (= {0}_0 {1}_0))".format(
                        _internalstatevariable, _outSignalName, _initialvalue)
        return assertion
