import json
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
    sModel = loadModel("blocks.json")
#    print(sModel.getAllInputs())
#    print(sModel.getAllOutputs())
#    print(sModel.getAllBlocks())
#    print(sModel.getAllConnections())
    ssg = StateSpaceGenerator()

    package = sModel.packBlockForTransformation("b3")

    rg = RoutineGenerator()
    ag = AssertionGenerator()


    print(ag.add(package,0))

    #ss = ssg.generateStateSpace(sModel, 0.01, 10000)
    #print(ss.getStates(25,5))

main()
