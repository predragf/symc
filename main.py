import json
#from z3 import *
from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelloader import *
from modules.modelchecker.statespace import *
from modules.modelchecker.statespacegenerator import *
from modules.routinegenerators.routinegenerator import *
from modules.assertiongenerators.assertiongenerator import *
import time

def calculateBlockStepSize(simulationStepSize, blockStepSize):
    floating = blockStepSize / simulationStepSize
    return int(floating)

def main():
    start = time.time()
    sModel = loadModel("blocks.json")
    ssg = StateSpaceGenerator()

    stateSpace = ssg.generateStateSpace(sModel, 0.01, 10000)
    end = time.time()
    print(stateSpace.getStates(0, 25))
    print("the state space was generated in {0} seconds".format(end - start))
    #ss = ssg.generateStateSpace(sModel, 0.01, 10000)
    #print(ss.getStates(25,5))

main()
