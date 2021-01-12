import re
from assertiongeneratorutils import *
import time
import modules.utils.utils as cUtils

class AssertionGenerator:
    @staticmethod
    def Constant(blockPackage):
        _, output_signals = FindInputOutputSignals(blockPackage)
        maskedParentBlocks = blockPackage.get("maskedParentBlocks")
        signalName    = output_signals[0]#.get("SignalName")
        constantValue = blockPackage.get("Value")
        types         = ['uint8', 'uint16', 'uint32', 'int8', 'int16',
                         'int32', 'single', 'double', 'logical', 'boolean']

        for t in types:
            constantValue = constantValue.replace(t + '(', '(' + t + ' ')

        # Find masked parameter
        if not constantValue.isnumeric():
            constantValue = FindMaskedParameter(maskedParentBlocks, constantValue)

        return "(= {0}_{{0}} {1})".format(signalName, constantValue)

    @staticmethod
    def Sum(blockPackage):
        operators = blockPackage.get("Inputs")
        input_signals, output_signals = FindInputOutputSignals(blockPackage)
        input_signal_types, output_signal_types = FindInputOutputSignalTypes(blockPackage)
        inputsString = AssertionGeneratorUtils.parseSumInputs(input_signals, input_signal_types, operators)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def Product(blockPackage):
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
        maskedParentBlocks = blockPackage.get("maskedParentBlocks")
        criteria = blockPackage.get("Criteria", '').split()
        if cUtils.compareStringsIgnoreCase(maskedParentBlocks[0].get("statusToPass"), "GOOD_B(ss_U08)"):
            criteria[1] = ">"
            criteria[2] = "240" # Flawless = 255, Good >= 240, Bad < 240
        _, output_signals = FindInputOutputSignals(blockPackage)
        inputsString = AssertionGeneratorUtils.parseSwitchInputs(
            blockPackage["inputSignals"], criteria)
        outSignalName = output_signals[0]
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def Logic(blockPackage):
        operator = blockPackage.get("Operator")
        input_signals, output_signals = FindInputOutputSignals(blockPackage)
        input_signal_types, output_signal_types = FindInputOutputSignalTypes(blockPackage)
        outSignalName = output_signals[0]
        inputsString = AssertionGeneratorUtils.parseLogicInputs(
            blockPackage["inputSignals"], input_signal_types, operator)
        return "(= {0}_{{0}} {1})".format(outSignalName, inputsString)

    @staticmethod
    def DiscreteIntegrator(blockPackage):
        _input_signals         = blockPackage.get("inputSignals")
        _external_signal       = [_input_signal for _input_signal in _input_signals if _input_signal["DstPort"] == 0][0]
        _input_signal_name     = _external_signal["SignalName"]
        _gain_value            = blockPackage.get("gainval", "None")
        _output_signal         = blockPackage.get("outputSignals")
        _output_signal         = _output_signal[0]
        _output_signal_name    = _output_signal.get("SignalName", "")
        _sample_time           = blockPackage.get("CompiledSampleTime")[0]

        _internalstatevariable = "{0}_{1}".format(blockPackage.get("Name"), int(blockPackage.get("Handle")))
        _out_equal_int         = "(= {0}_{{0}} {1}_{{0}})".format(_output_signal_name, _internalstatevariable)
        _gain_mult             = "(* {0}_{{1}} (* {1} {2}))".format(_input_signal_name, _gain_value, _sample_time)
        _add_increment         = "(+ {0} {1}_{{1}})".format(_gain_mult, _internalstatevariable)
        _increment             = "(= {0}_{{0}} {1})".format(_internalstatevariable, _add_increment)

        _upper_saturation  = blockPackage.get('UpperSaturationLimit')
        _lower_saturation  = blockPackage.get('LowerSaturationLimit')
        _reset_signal      = [_input_signal for _input_signal in _input_signals if _input_signal["DstPort"] == 1][0]
        _reset_signal_name = _reset_signal["SignalName"]
        _reset_signal_type = _reset_signal["SignalType"]
        _reset_signal_name = "{0}_{{0}}".format(_reset_signal_name)

        _inc_upp_leq = "(<= {0} {1})".format(_add_increment, _upper_saturation)
        _inc_upp_gt  = "(> {0} {1})".format(_add_increment, _upper_saturation)
        _inc_low_geq = "(>= {0} {1})".format(_add_increment, _lower_saturation)
        _inc_low_lt  = "(< {0} {1})".format(_add_increment, _lower_saturation)

        if cUtils.compareStringsIgnoreCase(_reset_signal_type, 'single'):
            _reset_signal_name = "not (= {0} 0)".format(_reset_signal_name)

        _reset_false = "(not ({0}))".format(_reset_signal_name)
        _reset_true  = "({0})".format(_reset_signal_name)


        _incremental_cond_ite  = "(ite (and {0} {1} {2}) {3} {4}_{{0}})".format(_inc_upp_leq, _inc_low_geq, _reset_false, _add_increment, _internalstatevariable)
        _incremental_condition = "(= {0}_{{0}} {1})".format(_internalstatevariable, _incremental_cond_ite)
        _upper_sat_cond_ite    = "(ite (and {0} {1}) {2} {3}_{{0}})".format(_inc_upp_gt, _reset_false, _upper_saturation, _internalstatevariable)
        _upper_sat_condition   = "(= {0}_{{0}} {1})".format(_internalstatevariable, _upper_sat_cond_ite)
        _lower_sat_cond_ite    = "(ite (and {0} {1}) {2} {3}_{{0}})".format(_inc_low_lt, _reset_false, _lower_saturation, _internalstatevariable)
        _lower_sat_condition   = "(= {0}_{{0}} {1})".format(_internalstatevariable, _lower_sat_cond_ite)
        _reset_cond_ite        = "(ite {0} {1} {2}_{{0}})".format(_reset_true, '0', _internalstatevariable)
        _reset_condition       = "(= {0}_{{0}} {1})".format(_internalstatevariable, _reset_cond_ite)

        return "{0}\n{1}\n{2}\n{3}\n{4}".format(_out_equal_int, _incremental_condition, _upper_sat_condition, _lower_sat_condition, _reset_condition)

    @staticmethod
    def UnitDelay(blockPackage):
        _input_signal = blockPackage.get("inputSignals")
        _input_signal = _input_signal[0]
        _input_signal_name = _input_signal["SignalName"]
        _output_signal = blockPackage.get("outputSignals")
        _output_signal = _output_signal[0]
        _output_signal_name = _output_signal.get("SignalName", "")
        return "(= {0}_{{0}} {1}_{{1}})".format(_output_signal_name, _input_signal_name)

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
        # Probably needs to be updated if a mux or bus signal is
        # propagated through the merge block.

        input_signals, output_signals = FindInputOutputSignals(blockPackage)
        if output_signals == []:
            return ""
        trigger_signals = FindTriggerSignals(blockPackage)
        inport_num = FindPortNumbers(blockPackage)
        result_string = GenerateMergeAssert(input_signals, output_signals, trigger_signals, inport_num)

        return "\n".join(result_string)

    @staticmethod
    def BusCreator(blockPackage):
        return ""

    @staticmethod
    def BusSelector(blockPackage):
        return ""

    @staticmethod
    def If(blockPackage):
        return ""

    @staticmethod
    def generateBlockAssertion(blockPackage):
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

def FindInputOutputSignalTypes(blockPackage):

    output_signal_types = []
    input_signal_types  = []

    input_signals  = blockPackage.get("inputSignals")
    output_signals = blockPackage.get("outputSignals")

    for input_signal in input_signals:
        input_signal_types.append(input_signal.get("SignalType", ""))

    for output_signal in output_signals:
        output_signal_types.append(output_signal.get("SignalType", ""))

    return input_signal_types, output_signal_types

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

def FindTriggerSignals(blockPackage):
    # Get predecessor blocks
    # Find triggeringSignal
    trigger_signals = []
    predecessorBlocks = blockPackage.get("predecessorBlocks", "")
    for preBlock in predecessorBlocks:
        trigger_signals.append(preBlock.get("calculated_sample_time_str", ""))

    return trigger_signals

def FindPortNumbers(blockPackage):

    inport_num  = []
    input_signals  = blockPackage.get("inputSignals")
    for input_signal in input_signals:
        inport_num.append(input_signal.get("DstPort", ""))
    return inport_num

def GenerateMergeAssert(input_signals, output_signal, trigger_signals, inport_num):
    assertion = []
    for k, input in enumerate(input_signals):
        trigger = trigger_signals[k]
        assertion.append('(= {0} (ite {1} {2} {0}))'.format(output_signal[0] + '_{0}', trigger, input + '_{0}'))

    return assertion
