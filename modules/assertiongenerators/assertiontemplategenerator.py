class AssertionTemplateGenerator:
    __constantDeclarationTemplate = "(declare-const #constant#_{0} () Real)"

    @staticmethod
    def createDeclarations(listofvariables):
        declarations = []
        for _var in listofvariables:
            declarations.append(
                    AssertionTemplateGenerator.__constantDeclarationTemplate.replace("#constant#", _var))
        return declarations

    @staticmethod
    def abs(blockForTransformation):
        result = {}
        listofvariables = []
        _input = blockForTransformation.get("inputs")[0]
        inputSignalName = _input.get("signalvariable")
        signalName = blockForTransformation.get("signalvariable")
        listofvariables.append(signalName)
        result["assertion"] = "(assert (ite (>= {0}_{{0}} 0.0) (= {1}_{{0}} {0}_{{0}}) (= {1}_{{0}} (- {0}_{{0}}))))".format(inputSignalName, signalName)
        result["delcarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def constant(blockForTransformation):
        result = {}
        listofvariables = []
        signalName = blockForTransformation.get("signalvariable")
        listofvariables.append(signalName)
        parameters = blockForTransformation.get("parameters")
        constantValue = parameters.get("value")
        result["assertion"] = "(assert (= {0}_{{0}} {1}))".format(signalName,
                                                                constantValue)
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def gain(blockForTransformation):
        result = {}
        listofvariables = []
        _input = blockForTransformation.get("inputs")[0]
        inputSignalName = _input.get("signalvariable")

        signalName = blockForTransformation.get("signalvariable")
        listofvariables.append(signalName)

        parameters = blockForTransformation.get("parameters")
        gain = parameters.get("gain")
        result["assertion"] = "(assert (= {0}_{{0}} (* {1}                      {2}))".format(signalName, inputSignalName, gain)
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def minmax(blockForTransformation):
        result = {}
        listofvariables = []
        _firstInput = blockForTransformation.get("inputs")[0]
        _secondInput = blockForTransformation.get("inputs")[1]
        _firstSignalName = _firstInput.get("signalvariable")
        _secondSignalName = _secondInput.get("signalvariable")

        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)

        _parameters = blockForTransformation.get("parameters")
        _mode = _parameters.get("mode")
        _operator = "<"
        if _mode.lower() == "max":
            _operator = ">"

        result["assertion"] = "(assert (ite ({0} {1}_{{0}} {2}_{{0}}) (= {3}_{{0}} {1}_{{0}}) (= {3}_{{0}} {1}_{{0}}) ))".format(_operator, _firstSignalName, _secondSignalName, _outSignalName)
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def product(blockForTransformation):
        result = {}
        listofvariables = []
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)
        _inputSignalNames = []
        for _input in _inputs:
            _signalName = _input.get("signalvariable")
            _inputSignalNames.append("{0}_{{0}}".format(_signalName))
        result["assertion"] = "(assert (= {0}_{{0}} (* {1})))".format(_outSignalName, " ".join(_inputSignalNames))
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def sum(blockForTransformation):
        result = {}
        listofvariables = []
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)
        _inputSignalNames = []
        for _input in _inputs:
            _signalName = _input.get("signalvariable")
            _inputSignalNames.append("{0}_{{0}}".format(_signalName))
        result["assertion"] = "(assert (= {0}_{{0}} (+ {1})))".format(_outSignalName, " ".join(_inputSignalNames))
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def relationaloperator(blockForTransformation):
        result = {}
        listofvariables = []
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)
        _parameters = blockForTransformation.get("parameters")
        _operator = _parameters.get("relationtype")

        _firstInput = blockForTransformation.get("inputs")[0]
        _secondInput = blockForTransformation.get("inputs")[1]

        _firstSignalName = _firstInput.get("signalvariable")
        _secondSignalName = _secondInput.get("signalvariable")

        result["assertion"] = "(assert (ite ({0} {1}_{{0}} {2}_{{0}}) (= {3}_{{0}} 1) (= {3}_{{0}} 0)))".format(_operator, _firstSignalName, _secondSignalName, _outSignalName)
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def saturate(blockForTransformation):
        result = {}
        listofvariables = []
        _parameters = blockForTransformation.get("parameters")
        _input = blockForTransformation.get("inputs")[0]
        _inputSignalName = _input.get("signalvariable")
        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)

        _lowerLimit = _parameters.get("lowerlimit")
        _upperLimit = _parameters.get("upperlimit")

        result["assertion"] = "(assert (ite (> {0}_{{0}} {2}) (= {1}_{{0}} {2}) (ite (< {0}_{{0}} {3}) (= {1}_{{0}} {3}) (= {0}_{{0}} {1}_{{0}}))))".format(_inputSignalName, _outSignalName, _upperLimit, _lowerLimit)
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def signum(blockForTransformation):
        result = {}
        listofvariables = []
        _input = blockForTransformation.get("inputs")[0]
        _inputSignalName = _input.get("signalvariable")
        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)

        result["assertion"] = "(assert (ite (= {0}_{{0}} 0) (= {1}_{{0}} 0) (ite (< {0}_{{0}} 0) (= {1}_{{0}} -1) (= 1 {1}_{{0}}))))".format(_inputSignalName, _outSignalName)
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def switch(blockForTransformation):
        result = {}
        listofvariables = []
        _parameters = blockForTransformation.get("parameters")
        _firstInput = blockForTransformation.get("inputs")[0]
        _controlInput = blockForTransformation.get("inputs")[1]
        _secondInput = blockForTransformation.get("inputs")[2]
        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)

        condition = _parameters.get("condition")
        condition = condition.split(" ")

        result["assertion"] = "(assert (ite ({0} {1}_{{0}} {2}) (= {3}_{{0}} {5}_{{0}}) (= {3}_{{0}} {5}_{{0}})))".format(condition[1], _controlInput.get("signalvariable"), condition[2], _outSignalName, _firstInput.get("signalvariable"), _secondInput.get("signalvariable"))
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def round(blockForTransformation):
        result = {}
        listofvariables = []
        _input = blockForTransformation.get("inputs")[0]
        _outSignalName = blockForTransformation.get("signalvariable")
        listofvariables.append(_outSignalName)
        result["assertion"] = """(assert (ite (> 0.5 (- {0}_{{0}} (to_int {0}_{{0}}))) (= {1}_{{0}} (to_int {0}_{{0}})) (= {0}_{{0}}
        (+ 1 (to_int {0}_{{0}})))))""".format(
                                            _input.get("signalvariable"), _outSignalName)
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def unitdelay(blockForTransformation):
        result = {}
        listofvariables = []
        _outSignalName = blockForTransformation.get("signalvariable")
        _stateVariable = _outSignalName.replace("signal", "internalstate")
        listofvariables.append(_outSignalName)
        listofvariables.append(_stateVariable)
        _input = blockForTransformation.get("inputs")[0]
        result["assertion"] = """(assert (and (= {0}_{{0}} {1}_{{1}}) (= {1}_{{0}} {2}_{{0}})))""".format(
                                        _outSignalName, _stateVariable, _input.get("signalvariable"))
        result["declarations"] = AssertionTemplateGenerator.createDeclarations(listofvariables)
        return result

    @staticmethod
    def rt(blockForTransformation):
        result = AssertionTemplateGenerator.unitdelay(blockForTransformation)
        return result

    @staticmethod
    def generateInitialConfiguration(blockForTransformation):
        _parameters = blockForTransformation.get("parameters")
        _outSignalName = blockForTransformation.get("signalvariable", "")
        _outSignalName = _outSignalName.replace("signal", "internalstate")
        _initalvalue = _parameters.get("initialvalue", "")
        _initialConditionAssertion = "no initial state"
        if not (_initalvalue == ""):
            _initialConditionAssertion = "(assert (= {0}_0 {1}))".format(_outSignalName,
            _initalvalue)
        return _initialConditionAssertion

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
