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

def calculateBlockStepSize(simulationStepSize, blockStepSize):
    floating = blockStepSize / simulationStepSize
    return int(floating)

def printlist(_list):
    for itm in _list:
        print(itm)

def main():
    start = time.time()
    sModel = loadModel("./data/vhe.json")
    ssg = StateSpaceGenerator()
    sbPackackage = sModel.packBlockForTransformation("b2")
    ag = AssertionGenerator()
    print(ag.gain(sbPackackage, 0))
    stateSpace = ssg.generateStateSpace(sModel, 1, 10000)
    end = time.time()
    requestedStates = stateSpace.getStates(0,120)
    printlist(requestedStates)
    print("the state space was generated in {0} seconds".format(end - start))
    #ss = ssg.generateStateSpace(sModel, 0.01, 10000)
    #print(ss.getStates(25,5))

main()
