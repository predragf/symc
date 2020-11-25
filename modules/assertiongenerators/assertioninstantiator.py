from modules.assertiongenerators.assertiontemplategenerator import *
from modules.assertiongenerators.assertiongeneratorutils import *
import random
import string
import modules.utils.utils as customUtils

class AssertionInstantiator:

    @staticmethod
    def isStateless(block):
        #to be updated
        blocksWithStates = ["UnitDelay", "rt", "integrator", "DiscreteIntegrator"]
        blocktype = block.get("blocktype")
        return not blocktype in blocksWithStates

    @staticmethod
    def instantiateAssertion(block, step, blockStepSize):
        assertionTemplate = ""
        if AssertionInstantiator.isStateless(block):
            if step == 0 or blockStepSize == 0 or step % blockStepSize == 0:
                assertionTemplate = AssertionTemplateGenerator.generateBlockAssertion(block)
            else:
                assertionTemplate = AssertionGeneratorUtils.generateVacousState(block)
        else:
            if step == 0:
                assertionTemplate = AssertionGeneratorUtils.generateInitialState(block)
            elif blockStepSize == 0 or step % blockStepSize == 0:
                assertionTemplate = AssertionTemplateGenerator.generateBlockAssertion(block)
            else:
                assertionTemplate = AssertionGeneratorUtils.generateVacousState(block)
        instantiatedAssertion = assertionTemplate.format(step, step - 1)
        _assertion = "(assert (! {0} :named {1}))".format(instantiatedAssertion,
        customUtils.generateRandomLetterSequence(12))
        if instantiatedAssertion == "":
            _assertion = ""
        return _assertion
