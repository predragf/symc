from modules.assertiongenerators.cocosim.assertiongenerator import *
from modules.assertiongenerators.cocosim.assertiongeneratorutils import *
import random
import string
import modules.utils.utils as customUtils

class AssertionInstantiator:

    @staticmethod
    def isStateless(block):
        #to be updated
        blocksWithStates = ["UnitDelay", "rt", "integrator", "DiscreteIntegrator"]
        blocktype = block.get("BlockType")
        return not blocktype in blocksWithStates

    @staticmethod
    def instantiateAssertion(block, step, blockStepSize):
        assertionTemplate = ""
        if AssertionInstantiator.isStateless(block):
            if step == 0 or blockStepSize == 0 or step % blockStepSize == 0:
                assertionTemplate = AssertionGenerator.generateBlockAssertion(block)
            else:
                assertionTemplate = AssertionGeneratorUtils.generateVacousState(block)
        else:
            if step == 0:
                assertionTemplate = AssertionGeneratorUtils.generateInitialState(block)
            elif blockStepSize == 0 or step % blockStepSize == 0:
                assertionTemplate = AssertionGenerator.generateBlockAssertion(block)
            else:
                assertionTemplate = AssertionGeneratorUtils.generateVacousState(block)
        
        if not (block.get("calculated_sample_time_str") == None) and not (assertionTemplate == ''):
            trigger = block.get("calculated_sample_time_str")
            if step == 0:
                assertionVacousTemplate = AssertionGenerator.generateBlockAssertion(block)
            else:
                assertionVacousTemplate = AssertionGeneratorUtils.generateVacousState(block)
            assertionSignal = FindAssertionSignal(assertionTemplate)
            assertionTemplate_mod = ModifyAssertion(assertionTemplate)
            assertionVacousTemplate_mod = ModifyAssertion(assertionVacousTemplate)
            assertionTemplate = "(= {0} (ite {1} {2} {3}))".format(assertionSignal, trigger, assertionTemplate_mod, assertionVacousTemplate_mod)

        instantiatedAssertion = assertionTemplate.format(step, step - 1)
        instantiatedAssertion = instantiatedAssertion.split('\n')

        if instantiatedAssertion[0] == "":
            _assertion = ""
        else:
            _assertion = []
            for assertion in instantiatedAssertion:
                _assertion.append("(assert (! {0} :named {1}))".format(assertion,
                customUtils.generateRandomLetterSequence(12)))

        return _assertion

def FindAssertionSignal(template):
    template_split = template.split(' ')
    assertion_signal = template_split[1]
    return assertion_signal

def ModifyAssertion(template):
    template_split = template.split(' ')
    new_temp = ' '.join(template_split[2:])
    modifiedAssertion = new_temp[:-1]
    return modifiedAssertion
