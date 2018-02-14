class AssertionTemplateGenerator:
    @staticmethod
    def abs(blockForTransformation):
        _input = blockForTransformation.get("inputs")[0]
        inputSignalName = _input.get("signalvariable")
        signalName = blockForTransformation.get("signalvariable")
        return "(assert (ite (>= {0}_{{0}} 0.0) (= {1}_{{0}} {0}_{{0}}) (= {1}_{{0}} (- {0}_{{0}}))))".format(inputSignalName, signalName)

    @staticmethod
    def constant(blockForTransformation):
        signalName = blockForTransformation.get("signalvariable")
        parameters = blockForTransformation.get("parameters")
        constantValue = parameters.get("value")
        return "(assert (= {0}_{{0}} {1}))".format(signalName, constantValue)

    @staticmethod
    def gain(blockForTransformation):
        _input = blockForTransformation.get("inputs")[0]
        inputSignalName = _input.get("signalvariable")
        signalName = blockForTransformation.get("signalvariable")
        parameters = blockForTransformation.get("parameters")
        gain = parameters.get("gain")
        return "(assert (= {0}_{{0}} (* {1} {2}))".format(signalName, inputSignalName, gain)

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

        return "(assert (ite ({0} {1}_{{0}} {2}_{{0}}) (= {3}_{{0}} {1}_{{0}}) (= {3}_{{0}} {1}_{{0}}) ))".format(_operator, _firstSignalName, _secondSignalName, _outSignalName)

    @staticmethod
    def product(blockForTransformation):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _inputSignalNames = []
        for _input in _inputs:
            _signalName = _input.get("signalvariable")
            _inputSignalNames.append("{0}_{{0}}".format(_signalName))

        return "(assert (= {0}_{{0}} (* {1})))".format(_outSignalName, " ".join(_inputSignalNames))

    @staticmethod
    def sum(blockForTransformation):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _inputSignalNames = []
        for _input in _inputs:
            _signalName = _input.get("signalvariable")
            _inputSignalNames.append("{0}_{{0}}".format(_signalName))

        return "(assert (= {0}_{{0}} (+ {1})))".format(_outSignalName, " ".join(_inputSignalNames))
