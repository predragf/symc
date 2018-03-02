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

def check(modelname, _assumptions=[], reuseExistingModel=False):
    modelChecker = SyMC()
    result = modelChecker.checkModel(modelname, 1, _assumptions, reuseExistingModel)
    print(determineSatisfaction(result))

def r3BBW(modelname):
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
    check(modelname, _assumptions, True)

def r4BBW(modelname):
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
    check(modelname, _assumptions, True)

def block(ts, _initial, _function):
    block = {}
    block["ts"] = ts
    block["initial"] = _initial
    block["f"] = _function
    return block



def buildTransitionTable(steps):
    b1 = block(3, "k1", "f1(S0, #same# #2#)")
    b1 = block(3, "k1", "f2(S0, #S1# #S2#)")
    blocks = [b1, b2]


def main():
    cUtils.clearScreen()
    modelname = "./models/bbw-eo.json"
    sModel = loadModel(modelname)
    r3BBW(modelname)
    r4BBW(modelname)

main()
