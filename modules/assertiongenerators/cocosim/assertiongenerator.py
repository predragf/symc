import re
from assertiongeneratorutils import *
import time
import modules.utils.utils as cUtils

class AssertionGenerator:
    @staticmethod
    def Constant(blockPackage):
        # signalname is the output signal name, constant value is the
        # value that needs to be written on the signal
        # (= signal_djshadkjhas_{0} 5)

        # Further, if the constant block is inside the 'compareToConstant'
        # block, the 'Value' needs to be traced to that block.
        block_handle  = blockPackage.get("Handle", '')
        _, output_signals = FindInputOutputSignals(blockPackage)
        maskedParentBlocks = blockPackage.get("maskedParentBlocks")
        signalName    = output_signals[0]#.get("SignalName")
        constantValue = blockPackage.get("Value")
        types         = ['uint8', 'uint16', 'uint32', 'int8', 'int16',
                         'int32', 'single', 'double', 'logical']

        for t in types:
            constantValue = constantValue.replace(t + '(', '(' + t + ' ')

        # Find masked parameter
        if not constantValue.isnumeric():
            constantValue = FindMaskedParameter(maskedParentBlocks, constantValue)

        return "(= {0}_{{0}} {1})".format(signalName, constantValue)

    @staticmethod
    def Sum(blockPackage):
        block_handle = blockPackage.get("Handle", '')
        operators = blockPackage.get("Inputs")
        input_signals, output_signals = FindInputOutputSignals(blockPackage)
        inputsString = AssertionGeneratorUtils.parseSumInputs(input_signals, operators)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def Product(blockPackage):
        block_handle = blockPackage.get("Handle", '')
        operators = blockPackage.get("Inputs")
        input_signals, output_signals = FindInputOutputSignals(blockPackage)
        inputsString = AssertionGeneratorUtils.parseProductInputs(input_signals, operators)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def merge(blockPackage):
        pass

    @staticmethod
    def Switch(blockPackage):
        criteria = blockPackage.get("Criteria", '').split()
        criteria_operator = criteria[1]
        _, output_signals = FindInputOutputSignals(blockPackage)
        inputsString = AssertionGeneratorUtils.parseSwitchInputs(
            blockPackage["inputSignals"], criteria)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def Logic(blockPackage):
        block_handle = blockPackage.get("Handle", '')
        operator = blockPackage.get("Operator")
        input_signals, output_signals = FindInputOutputSignals(blockPackage)
        outSignalName = output_signals[0]
        inputsString = AssertionGeneratorUtils.parseLogicInputs(
            blockPackage["inputSignals"], operator)
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def DataTypeConversion(blockPackage):
        return ""
        pass

    @staticmethod
    def SubSystem(blockPackage):
        return ""
        pass

    @staticmethod
    def Inport(blockPackage):
        return ""
        pass

    @staticmethod
    def InportShadow(blockPackage):
        return ""
        pass

    @staticmethod
    def ActionPort(blockPackage):
        return ""
        pass

    @staticmethod
    def Outport(blockPackage):
        return ""
        pass

    @staticmethod
    def Terminator(blockPackage):
        return ""
        pass

    @staticmethod
    def Merge(blockPackage):
        return ""
        pass

    @staticmethod
    def BusCreator(blockPackage):
        return ""
        pass

    @staticmethod
    def BusSelector(blockPackage):
        return ""
        pass

    @staticmethod
    def If(blockPackage):
        criteria = blockPackage.get("IfExpression", '').split()
        input_signals, output_signals = FindInputOutputSignals(blockPackage)
        result_string = AssertionGeneratorUtils.parseIfInputs(
            input_signals, output_signals, criteria)
        return "\n".join(result_string)

    @staticmethod
    def generateBlockAssertion(blockPackage):
        # you need to implement this function
        #set([u'SubSystem', u'Outport', u'Constant', u'InportShadow', u'Sum', u'BusSelector', u'Inport', u'Merge', u'Switch', u'Terminator', u'Logic', None, u'BusCreator', u'DataTypeConversion', u'ActionPort', u'If'])
        # you need to check this
        blocktype = blockPackage.get("BlockType")
        assertion = ""

        if blocktype == None:
            return assertion

        try:
            assertiongenerationfunction = getattr(AssertionGenerator, blocktype)
            assertion = assertiongenerationfunction(blockPackage)
        except Exception as e:
            """for now we handle the exception. bad coding practice, but will be
            rewritten in future"""
            assertion = ""
        return assertion

def FindInputOutputSignals(blockPackage):

    output_signal_names = []
    input_signal_names  = []

    input_signals  = blockPackage.get("inputSignals")
    output_signals = blockPackage.get("outputSignals")

    for input_signal in input_signals:
        input_signal_names.append(input_signal.get("SignalName", ""))

    for output_signal in output_signals:
        output_signal_names.append(output_signal.get("SignalName", ""))

    return input_signal_names, output_signal_names

def FindMaskedParameter(maskedParentBlocks, parameter):
    # Finds parameter value going through parent blocks recursively
    for k, maskedParentBlock in enumerate(maskedParentBlocks):
        if not (maskedParentBlock.get(parameter) is None):
            parameter = maskedParentBlock.get(parameter)
            if parameter.isnumeric():
                return parameter
            else:
                return FindMaskedParameter(maskedParentBlocks[k+1:], parameter)

    return parameter
