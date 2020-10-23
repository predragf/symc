import re


class AssertionGenerator:
    @staticmethod
    def constant(self, blockPackage):
        # signalname is the output signal name, constant value is the
        # value that needs to be written on the signal
        # (= signal_djshadkjhas_{0} 5)
        return "(= {0}_{{0}} {1})".format(signalName, constantValue)

    @staticmethod
    def sum(self, blockPackage):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _inputsString = AssertionGeneratorUtils.parseSumInputs(_inputs, blockForTransformation)
        return "(= {0}_{{0}} {1})".format(_outSignalName, _inputsString)

    @staticmethod
    def merge(self, blockPackage):
        pass

    @staticmethod
    def switch(self, blockPackage):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _inputsString = AssertionGeneratorUtils.parseSwitch(_inputs, blockForTransformation)
        return "(= {0}_{{0}} {1})".format(_outSignalName, _inputsString)

    @staticmethod
    def logic(self, blockPackage):
        _inputs = blockForTransformation.get("inputs")
        _outSignalName = blockForTransformation.get("signalvariable")
        _inputsString = AssertionGeneratorUtils.parseLogic(_inputs, blockForTransformation)
        return "(= {0}_{{0}} {1})".format(_outSignalName, _inputsString)

    @staticmethod
    def dataTypeConversion(self, blockPackage):
        pass

    @staticmethod
    def If(self, blockPackage):
        pass

    @staticmethod
    def generateBlockAssertion(blockPackage):
        # you need to implement this function
        #set([u'SubSystem', u'Outport', u'Constant', u'InportShadow', u'Sum', u'BusSelector', u'Inport', u'Merge', u'Switch', u'Terminator', u'Logic', None, u'BusCreator', u'DataTypeConversion', u'ActionPort', u'If'])
        # you need to check this
        blocktype = blockForTransformation.get("BlockType")
        # Sum
        assertion = ""
        try:
            assertiongenerationfunction = getattr(AssertionGenerator, blocktype)
            assertion = assertiongenerationfunction(blockPackage)
        except Exception as e:
            """for now we handle the exception. bad coding practice, but will be
            rewritten in future"""
            assertion = ""
        return assertion
