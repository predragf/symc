from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelmanager import *
from modules.simulink.cocosim.symc import *
import modules.utils.utils as cUtils
from modules.utils.gcd import *
from modules.modelchecker.ct import *
from modules.simulink.cocosim.cocosimmodel import *
import modules.simulink.cocosim.cocosimmodelmanager as CoCoSimModelManager
import modules.simulink.cocosim.slistparser as SLP
from modules.simulink.cocosim.stateflow.stateflowmodel import *
import z3
import json
import datetime
import time
import re
##
from modules.modelchecker.statespacegenerator import *
##
import modules.simulink.slistmanager as SLM

from modules.simulink.cocosim.cocosimstatespacegenerator import StateSpaceGenerator


simulationSize = 100


class Testing:
    @staticmethod
    def If():
        print "I am the if"


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
                                                "goto", "from", "Inport", "Outport", "TriggerPort", "Mux", "Demux", "Terminator", "Scope", "BusSelector", "BusCreator", "none"]
    _configuration["sample_times"] = {}
    return _configuration


def check(modelname, slistPath, modelChecker, propertyName="", _property=""):
    print 'check'
    totalSteps = 10
    result = modelChecker.checkModel(modelname, slistPath, 1, totalSteps, _property)
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
    template = "(> signal_1 100)"
    constraint = ""
    for i in range(0, simulationSize):
        constraint += template.format(i)
    final = "(assert (! (or {0}) :named {1}))".format(constraint, "r3")
    _assumptions = []
    _assumptions.append(final)
    check(modelname, modelChecker, "r4bbw", _assumptions)


def r4BBW(modelname, slistPath, modelChecker):
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
    check(modelname, slistPath, modelChecker, "r4bbw", property)


def verifyModel(modelname, slistPath, size):
    modelChecker = SyMC(createMCConfig())
    # r3BBW(modelname, modelChecker)
    r4BBW(modelname, slistPath, modelChecker)


def main():
    cUtils.clearScreen()
    modelPath = "./models/bbw_cocosim_adjusted.json"  # './models/bbw/bbw.json' #
    SFmodelPath = "./models/bbw/stateflow.json"
    BBWmodelPath = './models/bbw/bbw.json'  # "./models/bbw_cocosim_adjusted.json"
    slistPath = "./models/slist-bbw.txt"
    slistPath = "./models/slist-bbw.txt"

    fuelPath = "/Users/predrag/Documents/fuel/fuel_IR.json"
    fuelSList = "/Users/predrag/Documents/fuel/slist_flat.txt"
    fuelSListOrg = "/Users/predrag/Documents/fuel/slist.txt"

    #fuelPath = "C:/Models/Fuel/fuel_IR.json"
    #fuelSList = "C:/Models/Fuel/slist_flat.txt"
    #fuelSListOrg = "C:/Models/Fuel/slist.txt"

    #slist = SLM.SListManager.loadSList(fuelSList)
    # for line in slist:
    #    print line
    #verifyModel(fuelPath, fuelSList, 1)
    _config = createMCConfig()
    modelChecker = SyMC(createMCConfig())
    modelChecker.checkModel(fuelPath, fuelSList, 10, "")
    CSM = CoCoSimModelManager.loadModel(fuelPath, fuelSList, _config)
    #cTable = CSM.getConnectionTable()
    # for b in cTable:
    #    print(b)
    # time.sleep(10)
    SSG = StateSpaceGenerator()
    statespace = SSG.generateStateSpace(CSM, 1000)
    try:
        parsedSMTScript = z3.parse_smt2_string(statespace.getSMTScript())
        goal = Goal()
        goal.add(parsedSMTScript)
        solver = Solver()
        solver.set("mbqi", True)
        solver.set("unsat-core", True)
        solver.set("mbqi.max_iterations", 100)
        tactic = Then("smt", "elim-term-ite", "elim-and")
        parsedAssertions = tactic(goal).as_expr()
        solver.add(parsedAssertions)
        print solver.check()

    except Exception as e:
        print e
    # for b in CSM.getBlocksForTransformation():
    #    try:
    #        iffunction = getattr(Testing, b.get("BlockType", ""))
    #        iffunction()
    #    except Exception as e:
    #        pass

    #print(json.dumps(sf.generateAllTransitions(), indent=4, sort_keys=False))

    print "done"


main()
