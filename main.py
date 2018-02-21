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
from modules.assertiongenerators.assertiongeneratorutils import *
from modules.assertiongenerators.assertioninstantiator import *
from modules.simulationanalysis.symbolicfixedpoint import *


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
    result = modelChecker.checkModel(modelname, 1, 2, [])
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

def searchRatio(a, b, _min, _max):
    out = -3
    if _min == _max:
        out = _max + 1
    else:
        if _max > _min:
            mid = int((_min + _max ) / 2)
            if a < mid*b:
                out = searchRatio(a, b, _min, mid)
            else:
                if a > (mid + 1) * b:
                    out = searchRatio(a, b, mid + 1, _max)
                else:
                    if (a - mid) * b <= (mid + 1)*b - a:
                        out = mid
                    else:
                        out = mid + 1
        else:
            out = 20

    return out


def main():
    modelname = "./models/bbw-eo.json"

    describe_tactics()
    #testScenario(modelname)
    """
    print(searchRatio(17, 3, 0, 99))
    start = time.time()
    sModel = loadModel(modelname)
    testingId = "bbw/rt13"
    testingpackage = sModel.packBlockForTransformation(testingId)
    print(json.dumps(testingpackage, indent=2))
    #fChain = sModel.getForwardBlockDataDependencyChain(testingId)

    testingId = "bbw/vehicle_body_wheels/rr_wheel/sum"

    allPacked = sModel.packAllBlocksForTransformation()
    #print(sModel.simulinkModelJson["signalvariables"])
    SSGenerator = StateSpaceGenerator()
    sSpace = SSGenerator.generateStateSpace(sModel, 1, 2)
    sSpace.genenrateSMT2Script()
    #print(sModel.simulinkModelJson["internalstatevariables"])
    #print(sModel.simulinkModelJson["signalvariables"])
    """



main()
