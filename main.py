from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelmanager import *
#from modules.modelchecker.symc import *
from modules.simulink.cocosim.symc import *
import modules.utils.utils as cUtils
from modules.utils.gcd import *
from modules.modelchecker.ct import *
from modules.simulink.cocosim.cocosimmodel import *
from modules.simulink.cocosim.cocosimmodelmanager import *
import z3
import json
from modules.modelchecker.simulink.parsedsimulinkline import *
from modules.modelchecker.simulink.parsedsimulinkblock import *
from modules.modelchecker.simulink.parsedsimulinkmodel import *

simulationSize = 100

def printlist(_list, keyname=""):
    if keyname != "":
        _list = sorted(_list, key=lambda k: k[keyname])
    print("The size of the list is: {0}".format(len(_list)))
    for itm in _list:
        if type(itm) == list:
            printlist(itm)
        else:
            print(itm)

def generateAssertionsFromProperty(property):
    assertions = []
    signalPattern = r'signal_\d+'
    usedSignals = re.findall(signalPattern, property)
    for i in range(0, 100):
        assertion = property
        for us in usedSignals:
            assertion = assertion.replace(us, "{0}_{1}".format(us, i))
        assertions.append(assertion)
    return assertions

def determineSatisfaction(result):
    verdict = "violated"
    if result["verdict"] == unsat:
        verdict = "verified"
    return verdict

def createMCConfig():
    _configuration = dict()
    _configuration["useTactics"] = False
    _configuration["reuseExistingModel"] = False
    _configuration["saveStateSpace"] = True
    _configuration["noncomputationalblocks"] = ["SubSystem",
                                                "goto", "from", "Inport", "Outport", "TriggerPort", "Mux", "Demux", "Terminator", "Scope", "none"]
    return _configuration

def check(modelname, slistPath, modelChecker, propertyName="", _property=""):
    result = modelChecker.checkModel(modelname, slistPath, 1, _property)
    mcResult = determineSatisfaction(result)
    print("Property status: {0}".format(mcResult))
    if mcResult == "violated":
        m = result["model"]
        modelFileRelative = "./models/counterexamples/{}.txt".format(propertyName)
        modelAsList = sorted([(d, m[d]) for d in m], key=lambda
                             x: str(x[0]))
        violationModelString = str(modelAsList)
        signalsOfInterest = []
        for itm in modelAsList:
            if(str(itm[0]).startswith("signal_82_") or
                    str(itm[0]).startswith("signal_153_")):
                signalsOfInterest.append(itm)
        errorFile = openFile(modelFileRelative, "w")
        try:
            errorFile.write(violationModelString)
        except e:
            print(e)
        finally:
            if errorFile.closed is False:
                errorFile.close()
            print(signalsOfInterest)

def r3BBW(modelname, modelChecker):
    """
    The value of the brake pedal position shall not exceed its maximal
    value of 100
    """
    template = "(> signal_1_{0} 100)"
    constraint = ""
    for i in range(0, simulationSize):
        constraint += template.format(i)
    final = "(assert (! (or {0}) :named {1}))".format(constraint, "r3")
    _assumptions = []
    _assumptions.append(final)
    check(modelname, modelChecker, "r4bbw", _assumptions)

def r4BBW(modelname, modelChecker):
    """
    If the slip rate exceeds 0.2, then the applied brake torque shall be set
    to 0.
    """
    template = "(and (> signal_82_{0} 0.2) (not (= signal_153_{0} 0)))"
    property = "(and (> signal_82 0.2) (not (= signal_153 0)))"
    constraint = ""
    for i in range(0, simulationSize):
        constraint += template.format(i)
    final = "(assert (! (or {0}) :named {1}))".format(constraint, "r4")
    _assumptions = [final]
    check(modelname, modelChecker, "r4bbw", property)

def verifyModel(modelname, size):
    modelChecker = SyMC(createMCConfig())
    # r3BBW(modelname, modelChecker)
    r4BBW(modelname, modelChecker)

def main():
    cUtils.clearScreen()
    modelPath = './models/bbw/bbw.json' #"./models/bbw_cocosim_adjusted.json"
    slistPath = "./models/slist-bbw.txt"
    # sModel = loadModel(modelname)

    #cocoSimMoldel = CoCoSimModelManager.loadModel(modelPath, slistPath, createMCConfig())
    #rt14 = "2489.000244140625"
    #blk = cocoSimMoldel.getBlockById(rt14)
	
    modelChecker = SyMC(createMCConfig())
    check(modelPath, slistPath, modelChecker)
	
    # print(blk)
    # print(gcdList([5,3,2]))
    # print(len(sModel.getAllConnections()))
    # print(sModel.getSignalVariables())
    # verifyModel(modelname, 100)

    print("done")

main()
