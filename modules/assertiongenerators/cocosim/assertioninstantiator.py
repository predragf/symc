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
