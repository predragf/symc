import string
import random
import os
import platform

def generateRandomLetterSequence(sequenceLength):
    return ''.join(random.choice(string.ascii_uppercase) for _ in range(sequenceLength))

def sortJsonList(jsonList, sortKey=""):
    sortedList = jsonList
    if sortKey != "":
        sortedList = sorted(jsonList, key=lambda k: k[sortKey])
    return sortedList

def to_int(asString):
    number = -1
    try:
        number = int(asString)
    except Exception:
        pass
    return number

def clearScreen():
    _platform = platform.system().lower()
    print(_platform)
    _command = 'clear'
    if _platform == 'windows':
        _command = 'cls'
    os.system(_command)
