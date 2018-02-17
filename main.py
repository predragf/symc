import json
from z3 import *
from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelloader import *
from modules.modelchecker.statespace import *
from modules.modelchecker.statespacegenerator import *
from modules.routinegenerators.routinegenerator import *
from modules.assertiongenerators.assertiongenerator import *
from modules.utils.gcd import *
import time
import re
import logging
from modules.modelchecker.simc import *
from modules.modelchecker.statespacemanager import *
from modules.simulink.simulinkmodelmanager import *
from modules.utils.jsonmanager import *
from modules.assertiongenerators.assertiontemplategenerator import *
from types import FunctionType


def printlist(_list, keyname=""):
    if keyname != "":
        _list = sorted(_list, key=lambda k: k[keyname])
    print("The size of the list is: {0}".format(len(_list)))
    for itm in _list:
        print(itm)

def slistAsList(slistLocation):
    slistFile = open(slistLocation, "r");
    lines = []
    for line in slistFile:
        lines.append(line)
    return lines

def generateAssertionsForTheTestScenario():
    assumptions = ["(assert (= PI 3.14))", "(assert (= R 0.5))", "(assert (= SLIP_ABS_ON 0.1))"]
    for i in range(0, 1):
        #assumptions.append("(assert (not (> (* c5_{0} 0.9) c4_{0})))".format(str(i)))
        assumptions.append("(assert (and (> c1_{0} 0) (> c3_{0} 0) (> c2_{0} 0)))".format(i))
        assumptions.append("(assert (and (< c2_{0} 10) (not (= c13_{0} c1_{0}))))".format(i))
        #assumptions.append("(assert (= c12_{0} 0))".format(i))
    return assumptions

def testScenario(modelname):
    modelChecker = SiMC()
    assumptions = generateAssertionsForTheTestScenario()
    result = modelChecker.checkModel(modelname, 0.1, 20, [])
    print(result)

def isInFeedbackLoop(blockTransformationPackage):
    inloop = False
    execOrder = blockTransformationPackage.get("executionorder")
    try:
        execOrder = int(execOrder)
    except:
        return False
    for iconn in blockTransformationPackage.get("inputs"):
        sourceblk = iconn.get("sourceblock")
        sourceblkeo = sourceblk.get("executionorder")
        try:
            sourceblkeo = int(sourceblkeo)
            if(sourceblkeo > execOrder):
                inloop = True
                print("{0} ({1}): {2}({3})".format(blockTransformationPackage.get("blockid"), execOrder, sourceblk.get("blockid"), sourceblkeo))
        except:
            continue
    return inloop

def main():
    start = time.time()
    modelname = "./models/bbw-eo.json"
    sModel = loadModel(modelname)
    testingId = "bbw/rt4"
    testingpackage = sModel.packBlockForTransformation(testingId)
    allPacked = sModel.packAllBlocksForTransformation()
    SSGenerator = StateSpaceGenerator()
    sSpace = SSGenerator.generateStateSpace(sModel, 1, 200000)
    print(time.time() - start)
    #print(sSpace.getDeclarations())





main()
