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

def calculateBlockStepSize(simulationStepSize, blockStepSize):
    floating = blockStepSize / simulationStepSize
    return int(floating)

def printlist(_list, keyname=""):
    if keyname != "":
        _list = sorted(_list, key=lambda k: k[keyname])
    print("The size of the list is: {0}".format(len(_list)))
    for itm in _list:
        print(itm)

def extractVariables(assertion):
    _vars = set()
    smtKeywords = ["ite", "assert", "and", "or"]
    p = re.compile("[a-zA-Z0-9_]+")
    matches = p.findall(assertion)
    for m in matches:
        if m.lower() not in smtKeywords:
            _vars.add(m)
    return _vars

def testScenario():
    modelChecker = SiMC()
    assumptions = ["(assert (= PI 3.14))", "(assert (= R 0.5))", "(assert (= SLIP_ABS_ON 0.1))", "(assert (not (> (* c5_0 0.9) c4_0)))",  "(assert (and (> c3_0 0) (> c2_0 0)))", "(assert (> c1_0 0))", "(assert (= c12_0 0))"]
    start = time.time()
    result = modelChecker.checkModel("./data/wheel.json", 1, 10, assumptions)
    end = time.time()
    print("checking took {0} seconds".format(end - start))
    print(result)

def main():
    testScenario()

main()
