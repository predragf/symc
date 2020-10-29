from modules.assertiongenerators.cocosim.assertiongenerator import *
from modules.assertiongenerators.cocosim.assertiongeneratorutils import *
import random
import string
import modules.utils.utils as customUtils

class AssertionInstantiator:

    @staticmethod
    def isStateless(block):
        #to be updated
        blocksWithStates = ["unitdelay", "rt", "integrator"]
        blocktype = block.get("blocktype")
        return not blocktype in blocksWithStates

    @staticmethod
    def instantiateAssertion(block, step, blockStepSize, cTable):
        assertionTemplate = ""
        if AssertionInstantiator.isStateless(block):
            if step == 0 or blockStepSize == 0 or step % blockStepSize == 0:
                assertionTemplate = AssertionGenerator.generateBlockAssertion(block, cTable)
            else:
                assertionTemplate = AssertionGeneratorUtils.generateVacousState(block, cTable)
        else:
            if step == 0:
                assertionTemplate = AssertionGeneratorUtils.generateInitialState(block, cTable)
            elif blockStepSize == 0 or step % blockStepSize == 0:
                assertionTemplate = AssertionGenerator.generateBlockAssertion(block, cTable)
            else:
                assertionTemplate = AssertionGeneratorUtils.generateVacousState(block, cTable)
        #instantiatedAssertion = assertionTemplate.format(step, step - 1)
        #_assertion = "(assert (! {0} :named {1}))".format(instantiatedAssertion,
        #customUtils.generateRandomLetterSequence(12))
        #if instantiatedAssertion == "":
        #    _assertion = ""
        _assertion = ""
        return _assertion
