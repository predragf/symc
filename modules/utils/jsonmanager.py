import json


def openAndLoadJson(pathToJsonFile):
    jsonObject = {}
    try:
        _file = open(pathToJsonFile, "r")
        jsonObjectString = _file.read()
        jsonObject = json.loads(jsonObjectString)
    except:
        print("{0} could not be loaded.".format(pathToJsonFile))
    return jsonObject


def saveJsonToFile(jsonObject, pathToFile):
    try:
        with open(pathToFile, 'w') as jsonFile:
            jsonString = json.dumps(jsonObject, indent=2)
            jsonFile.write(jsonString)
    except:
        print("{0} not saved.".format(pathToFile))
