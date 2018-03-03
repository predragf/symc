from modules.simulink.simulinkmodel import *
from modules.simulink.simulinkmodelloader import *
from modules.modelchecker.symc import *
import modules.utils.utils as cUtils

def printlist(_list, keyname=""):
    if keyname != "":
        _list = sorted(_list, key=lambda k: k[keyname])
    print("The size of the list is: {0}".format(len(_list)))
    for itm in _list:
        if type(itm) == list:
            printlist(itm)
        else:
            print(itm)

def determineSatisfaction(result):
    verdict = "violated"
    if result["verdict"] == unsat:
        verdict = "verified"
    return verdict

def createMCConfig():
    _configuration = dict()
    _configuration["useTactics"] = False
    _configuration["reuseExistingModel"] = True
    _configuration["saveStateSpace"] = True
    return _configuration

def check(modelname, modelChecker, _assumptions=[]):
    result = modelChecker.checkModel(modelname, 1, _assumptions)
    print(determineSatisfaction(result))

def r3BBW(modelname, modelChecker):
    """
    R3: The value of the brake pedal position shall not exceed its maximal
    value of 100
    """
    template = "(> signal_1_{0} 100)"
    constraint = ""
    for i in range(0, 200):
        constraint += template.format(i)
    final = "(assert (! (or {0}) :named {1}))".format(constraint, "r3")
    _assumptions = []
    _assumptions.append(final)
    check(modelname, modelChecker, _assumptions)

def r4BBW(modelname, modelChecker):
    """
    If the slip rate exceeds 0.2, then the applied brake torque shall be set
    to 0.
    """
    template = "(and (> signal_82_{0} 0.2) (not (= signal_153_{0} 0)))"
    constraint = ""
    for i in range(0, 200):
        constraint += template.format(i)
    final = "(assert (! (or {0}) :named {1}))".format(constraint, "r4")
    _assumptions = [final]
    check(modelname, modelChecker, _assumptions)

def verifyModel(modelname):
    modelChecker = SyMC(createMCConfig())
    r3BBW(modelname, modelChecker)
    r4BBW(modelname, modelChecker)

def main():
    cUtils.clearScreen()
    modelname = "./models/bbw-eo.json"
    verifyModel(modelname)

main()
