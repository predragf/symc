import modules.utils.utils as cUtils
import json  # I need this only for preety printing


class StateflowModel:

    def __init__(self, jsonChart):
        self.jsonChart = jsonChart
        self.allTransitions = None
        self.transitionHashTable = self.__hasAllTransitions()

    def __getContent(self):
        return self.jsonChart.get("StateflowContent", {})

    def __getSFStateById(self, stateId):
        result = {}
        for state in self.__getAllSFStates():
            if cUtils.compareStringsIgnoreCase(stateId, state.get("Id", "")):
                result = state
                break
        return result

    def __getSFJunctionById(self, junctionId):
        result = {}
        for junction in self.__getAllSFJunctions():
            if cUtils.compareStringsIgnoreCase(junctionId, junction.get("Id", "")):
                result = junction
                break
        return result

    def __getNodeById(self, nodeId):
        # we first check if it is a state
        result = self.__getSFStateById(nodeId)
        # a valid state would be a dictionary with at least on key
        if len(result.keys()) == 0:
            result = self.__getSFJunctionById(nodeId)
        return result

    def __getAllSFStates(self):
        content = self.__getContent()
        return cUtils.toList(content.get("States", []))

    def __getAllSFJunctions(self):
        content = self.__getContent()
        return cUtils.toList(content.get("Junctions", []))

    def __getNodeOuterTransitions(self, node):
        return cUtils.toList(node.get("OuterTransitions", []))

    def __getNodeInternalTransitions(self, node):
        return cUtils.toList(node.get("InnerTransitions", []))

    def __hasListOfTransitions(self, sourceNode, _listOfTransitions):
        hashTable = {}
        for transition in _listOfTransitions:
            destination = transition.get("Destination", {})
            transitionData = {
                "sourceId": sourceNode.get("Id", ""),
                "destinationId": destination.get("Id", ""),
                "event": transition.get("Event", ""),
                "condition": transition.get("Condition", ""),
                "conditionAction": transition.get("ConditionAction", ""),
                "transitionAction": transition.get("TransitionAction", ""),
            }
            hashTable[transition.get("Id", "")] = transitionData
        return hashTable

    def __hasAllTransitions(self):
        hashTable = {}
        allStates = self.__getAllSFStates()
        allJunctions = self.__getAllSFJunctions()
        for state in allStates:
            stateTransitions = self.__getNodeInternalTransitions(state)
            stateTransitions.extend(self.__getNodeOuterTransitions(state))
            hashTable.update(self.__hasListOfTransitions(state, stateTransitions))
        for junction in allJunctions:
            hashTable.update(self.__hasListOfTransitions(
                junction, self.__getNodeOuterTransitions(junction)))
        return hashTable

    def __processTransition(self, _transitionForProcessing, _processedTransitions):
        allTransitions = []
        _processedTransitionsString = ""
        if len(_processedTransitions) > 0:
            _processedTransitionsString = '{1}{0}'.format(
                ";!".join(str(itm) for itm in _processedTransitions), "!")
        destination = _transitionForProcessing.get("Destination", {})
        newNodeForProcessingId = destination.get("Id", "")
        if cUtils.compareStringsIgnoreCase(destination.get("Type", ""), "Junction"):
            newNodeForProcessing = self.__getNodeById(newNodeForProcessingId)
            returnedTransitions = self.__generateNodeTransitions(newNodeForProcessing)
            for returnedTransition in returnedTransitions:
                merged = "{0};{1}".format(
                    _transitionForProcessing.get("Id", ""), returnedTransition)
                allTransitions.append("{0};{1}".format(_processedTransitionsString, merged)) if len(
                    _processedTransitionsString) > 0 else allTransitions.append(merged)
        allTransitions.append(
            "{0};{1}".format(_processedTransitionsString, _transitionForProcessing.get("Id", ""))) if len(_processedTransitions) > 0 else allTransitions.append(_transitionForProcessing.get("Id", ""))
        return allTransitions

    def __processTransitions(self, _transitionsForProcessing, _processedTransitions=[]):
        allTransitions = []
        for transition in _transitionsForProcessing:
            allTransitions.extend(self.__processTransition(transition, _processedTransitions))
            _processedTransitions.append(transition.get("Id", ""))
        return allTransitions, _processedTransitions

    def __generateNodeTransitions(self, node={}):
        allPossibleStateTransitions = []
        traversedTransitions = []
        outerTrnsitions = sorted(self.__getNodeOuterTransitions(node),
                                 key=lambda k: k['ExecutionOrder'])
        allTransitions, traversedTransitions = self.__processTransitions(
            outerTrnsitions, traversedTransitions)
        allPossibleStateTransitions.extend(allTransitions)
        innerTransitions = sorted(self.__getNodeInternalTransitions(node),
                                  key=lambda k: k['ExecutionOrder'])
        allTransitions, traversedTransitions = self.__processTransitions(
            innerTransitions, traversedTransitions)
        allPossibleStateTransitions.extend(allTransitions)
        return allPossibleStateTransitions

    def getJSON(self):
        return self.jsonChart

    def __generateAllTransitions(self):
        allstates = self.__getAllSFStates()
        alltransitions = []
        for state in allstates:
            alltransitions.extend(self.__generateNodeTransitions(state))
        return alltransitions

    def getAllTransitions(self):
        if self.allTransitions is None:
            self.allTransitions = self.__generateAllTransitions()
        return self.allTransitions

    def __generateTransitionRelationForState(self, state):
        return {
            "stateId": state.get("Id", ""),
            "transitions": self.__generateNodeTransitions(state)
        }

    def generateTransitionRelation(self):
        transitionRelation = []
        allStates = self.__getAllSFStates()
        for state in allStates:
            transitionRelation.append(self.__generateTransitionRelationForState(state))
        return transitionRelation

    def getTransitionHashTable(self):
        return self.transitionHashTable

    def __packStateForTransformation(self, state):
        pass

    def packForTransformation(self):
        # what information do I need for transforming each block?
        # if my source state is active, I will perform a set of actions and make a new (or the same) state active
        # the main problem is how to encode one simulation step
        # [s1, s1.1, s1.1.1, s1.1.2, s1.2, s1.2.1, s1.2.2]
        pass

    def test(self):
        print(json.dumps(self.getTransitionHashTable(), indent=4))
