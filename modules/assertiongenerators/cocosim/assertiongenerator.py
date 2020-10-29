import re
from assertiongeneratorutils import *
import time

class AssertionGenerator:
    @staticmethod
    def Constant(blockPackage, cTable):
        # signalname is the output signal name, constant value is the
        # value that needs to be written on the signal
        # (= signal_djshadkjhas_{0} 5)

        # Further, if the constant block is inside the 'compareToConstant'
        # block, the 'Value' needs to be traced to that block.

        block_handle = blockPackage.get("Handle", '')
        _, output_signals = FindInputOutputSignals(block_handle, cTable)
        signalName = output_signals[0]
        constantValue = blockPackage.get("Value")

        return "(= {0}_{{0}} {1})".format(signalName, constantValue)

    @staticmethod
    def Sum(blockPackage, cTable):
        block_handle  = blockPackage.get("Handle", '')
        operators     = blockPackage.get("Inputs")
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        inputsString = AssertionGeneratorUtils.parseSumInputs(input_signals, operators)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def merge(blockPackage, cTable):
        pass

    @staticmethod
    def Switch(blockPackage, cTable):
        block_handle      = blockPackage.get("Handle", '')
        criteria          = blockPackage.get("Criteria", '').split()
        criteria_operator = criteria[1]
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        inputsString  = AssertionGeneratorUtils.parseSwitchInputs(input_signals, criteria)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def Logic(blockPackage, cTable):
        block_handle  = blockPackage.get("Handle", '')
        operator      = blockPackage.get("Operator")
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        outSignalName = output_signals[0]
        inputsString  = AssertionGeneratorUtils.parseLogicInputs(input_signals, operator)
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def dataTypeConversion(blockPackage, cTable):
        pass

    @staticmethod
    def If(blockPackage, cTable):
        block_handle = blockPackage.get("Handle", '')
        criteria     = blockPackage.get("IfExpression", '').split()
        input_signals, output_signals = FindInputOutputSignals(block_handle, cTable)
        result_string = AssertionGeneratorUtils.parseIfInputs(input_signals, output_signals, criteria)
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
            #print('blocktype', blocktype)
            assertiongenerationfunction = getattr(AssertionGenerator, blocktype)
            assertion = assertiongenerationfunction(blockPackage, cTable)
        except Exception as e:
            """for now we handle the exception. bad coding practice, but will be
            rewritten in future"""
            #print('exception', e)
            assertion = ""
        #print('assertion:', assertion)
        return assertion

def FindInputOutputSignals(block_handle, cTable):

    output_signals = []
    input_signals  = []

    for entry in cTable:
        if block_handle == entry.get("SrcBlockHandle"):
            output_signals.append(entry.get("SignalName", ""))
        elif block_handle == entry.get('DstBlockHandle'):
            input_signals.append(entry.get("SignalName", ""))

    return input_signals, output_signals