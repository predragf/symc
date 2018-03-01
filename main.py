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
from modules.modelchecker.symc import *
from modules.modelchecker.statespacemanager import *
from modules.simulink.simulinkmodelmanager import *
from modules.utils.jsonmanager import *
from modules.assertiongenerators.assertiontemplategenerator import *
from types import FunctionType
from modules.assertiongenerators.assertiongeneratorutils import *
from modules.assertiongenerators.assertioninstantiator import *
from modules.modelchecker.symbolicfixpoint import *
import modules.utils.utils as cUtils
import math


def printlist(_list, keyname=""):
    if keyname != "":
        _list = sorted(_list, key=lambda k: k[keyname])
    print("The size of the list is: {0}".format(len(_list)))
    for itm in _list:
        if type(itm) == list:
            printlist(itm)
        else:
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

def determineSatisfaction(result):
    print(result["verdict"])
    verdict = "violated"
    if result["verdict"] == unsat:
        verdict = "verified"
    return verdict

def check(modelname, _assumptions=[], reuseExistingModel=False):
    modelChecker = SyMC()
    assumptions = generateAssertionsForTheTestScenario()
    result = modelChecker.checkModel(modelname, 1, _assumptions, reuseExistingModel)
    print(determineSatisfaction(result))

def r3BBW(modelname):
    template = "(> signal_1_{0} 100)"
    constraint = ""
    for i in range(0, 40):
        constraint += template.format(i)
    final = "(assert (! (or {0}) :named {1}))".format(constraint, "r3")
    _assumptions = []
    _assumptions.append(final)
    check(modelname, _assumptions, True)

def r4BBW(modelname):
        template = "(and (> signal_82_{0} 0.2) (not (= signal_153_{0} 0)))"
        constraint = ""
        for i in range(0, 40):
            constraint += template.format(i)
        final = "(assert (! (or {0}) :named {1}))".format(constraint, "r4")
        _assumptions = [final]
        check(modelname, _assumptions, True)

def main():
    cUtils.clearScreen()
    modelname = "./models/bbw-eo.json"
    sModel = loadModel(modelname)
    r3BBW(modelname)
    r4BBW(modelname)


main()
