import json
#from z3 import *
from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelloader import *
from modules.modelchecker.statespace import *
from modules.modelchecker.statespacegenerator import *
from modules.routinegenerators.routinegenerator import *
from modules.assertiongenerators.assertiongenerator import *
from modules.utils.gcd import *
import time
import re

def calculateBlockStepSize(simulationStepSize, blockStepSize):
    floating = blockStepSize / simulationStepSize
    return int(floating)

def printlist(_list, keyname=""):
    if keyname != "":
        _list = sorted(_list, key=lambda k: k[keyname])
    print("The size of the list is: {0}".format(len(_list)))
    for itm in _list:
        print(itm)

def main():
    start = time.time()
    sModel = loadModel("./data/wheel.json")
    print(sModel.calculateFundamentalSampleTime())
    ssg = StateSpaceGenerator()
    stateSpace = ssg.generateStateSpace(sModel, 1, 1000000)
    end = time.time()
    requestedStates = stateSpace.getStates(0,120)
    printlist(requestedStates)
    print("the state space was generated in {0} seconds".format(end - start))


main()
