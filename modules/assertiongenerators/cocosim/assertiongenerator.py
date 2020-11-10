import re
from assertiongeneratorutils import *
import time
import modules.utils.utils as cUtils


class AssertionGenerator:
    @staticmethod
    def Constant(blockPackage, cTable):
        # signalname is the output signal name, constant value is the
        # value that needs to be written on the signal
        # (= signal_djshadkjhas_{0} 5)

        # Further, if the constant block is inside the 'compareToConstant'
        # block, the 'Value' needs to be traced to that block.
        block_handle  = blockPackage.get("Handle", '')
        #_, output_signals = FindInputOutputSignals(block_handle, cTable)
        outputSignals = blockPackage.get("outputSignals")
        signalName    = outputSignals[0].get("SignalName")
        constantValue = blockPackage.get("Value")
        types         = ['uint8', 'uint16', 'uint32', 'int8', 'int16',
                         'int32', 'single', 'double', 'logical']

        for t in types:
            constantValue = constantValue.replace(t + '(', '(' + t + ' ')

        # Find masked parameter
        if not constantValue.isnumeric():
            parentBlock = blockPackage.get("parentBlock")
            if cUtils.compareStringsIgnoreCase(parentBlock.get("Mask"), "on") and not parentBlock.get(constantValue) is None:
                constantValue = parentBlock.get(constantValue)

        return "(= {0}_{{0}} {1})".format(signalName, constantValue)

    @staticmethod
    def Sum(blockPackage, cTable):
        block_handle = blockPackage.get("Handle", '')
        operators = blockPackage.get("Inputs")
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        inputsString = AssertionGeneratorUtils.parseSumInputs(input_signals, operators)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def Product(blockPackage, cTable):
        block_handle = blockPackage.get("Handle", '')
        operators = blockPackage.get("Inputs")
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        inputsString = AssertionGeneratorUtils.parseProductInputs(input_signals, operators)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def merge(blockPackage, cTable):
        pass

    @staticmethod
    def Switch(blockPackage, cTable):
        block_handle = blockPackage.get("Handle", '')
        criteria = blockPackage.get("Criteria", '').split()
        criteria_operator = criteria[1]
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        inputsString = AssertionGeneratorUtils.parseSwitchInputs(
            blockPackage["inputSignals"], criteria)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def Logic(blockPackage, cTable):
        block_handle = blockPackage.get("Handle", '')
        operator = blockPackage.get("Operator")
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        outSignalName = output_signals[0]
        inputsString = AssertionGeneratorUtils.parseLogicInputs(
            blockPackage["inputSignals"], operator)
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def dataTypeConversion(blockPackage, cTable):
        pass

    @staticmethod
    def If(blockPackage, cTable):
        block_handle = blockPackage.get("Handle", '')
        criteria = blockPackage.get("IfExpression", '').split()
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        result_string = AssertionGeneratorUtils.parseIfInputs(
            input_signals, output_signals, criteria)
        return "\n".join(result_string)

    @staticmethod
    def generateBlockAssertion(blockPackage, cTable):
        # you need to implement this function
        #set([u'SubSystem', u'Outport', u'Constant', u'InportShadow', u'Sum', u'BusSelector', u'Inport', u'Merge', u'Switch', u'Terminator', u'Logic', None, u'BusCreator', u'DataTypeConversion', u'ActionPort', u'If'])
        # you need to check this
        blocktype = blockPackage.get("BlockType")
        # Sum
        assertion = ""
        try:
            assertiongenerationfunction = getattr(AssertionGenerator, blocktype)
            assertion = assertiongenerationfunction(blockPackage, cTable)
        except Exception as e:
            """for now we handle the exception. bad coding practice, but will be
            rewritten in future"""
            assertion = ""
        return assertion


def FindInputOutputSignals(block_handle, cTable):

    output_signals = []
    input_signals = []

    for entry in cTable:
        if block_handle == entry.get("SrcBlockHandle"):
            output_signals.append(entry.get("SignalName", ""))
        elif block_handle == entry.get('DstBlockHandle'):
            input_signals.append(entry.get("SignalName", ""))
    return input_signals, output_signals
