from modules.assertiongenerators.assertiontemplategenerator import *
from modules.assertiongenerators.assertiongeneratorutils import *

class AssertionInstantiator:

    @staticmethod
    def isStateless(block):
        #to be updated
        blocksWithStates = ["unitdelay", "rt", "integrator"]
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
        if(assertionTemplate == "string index out of range"):
            print(block.get("blockid"))           
        return assertionTemplate.format(step, step - 1)
