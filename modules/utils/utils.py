import string
import random
import os
import platform


def generateRandomLetterSequence(sequenceLength):
    return ''.join(random.choice(string.ascii_uppercase) for _ in
                   range(sequenceLength))


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


def openFile(absoluteFileName, operation="r"):
    """
        This fuction makes sure that if the directory where
        the file is to be created exists. If the directory does
        not exist, it will crate it.
    """
    # just in case make sure that it is an absultute path
    absoluteFileName = os.path.abspath(absoluteFileName)
    _directory = os.path.dirname(absoluteFileName)
    if os.path.exists(_directory) is False:
        os.mkdir(_directory)
    return open(absoluteFileName, operation)


def clearScreen():
    _platform = platform.system().lower()
    print(_platform)
    _command = 'clear'
    if _platform == 'windows':
        _command = 'cls'
    os.system(_command)


def stringify(_input):
    if not isinstance(_input, basestring):
        _input = repr(_input)
    return _input


def compareStringsIgnoreCase(_first, _second):
    return _first is not None and _second is not None and stringify(_first).lower().strip() == stringify(_second).lower().strip()
