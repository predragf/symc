import modules.utils.utils as cUtils
import json  # I need this only for preety printing


class StateflowModel:

    def __init__(self, jsonChart):
        self.jsonChart = jsonChart
        self.allTransitions = None

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

    def __exploreJunctionTransitionsDFS(self, junction):
        result = []
        outerTrnsitions = sorted(junction.get("OuterTransitions", []),
                                 key=lambda k: k['ExecutionOrder'])
        # in case of a terminal junction (junction with no outer transitions)
        if len(outerTrnsitions) < 1:
            return result
        processed = []
        # reaching this point means that junction has outer transitions, meaning
        # that it is not a terminal junction
        for ot in outerTrnsitions:
            destination = ot.get("Destination", {})
            destinationType = destination.get("Type")
            processedString = ""
            if len(processed) > 0:
                processedString = '{0}'.format(
                    "".join("!{0};".format(str(itm)) for itm in processed))
            if cUtils.compareStringsIgnoreCase(destinationType, "junction"):
                resultConnections = self.__exploreJunctionTransitionsDFS(self.__getNodeById(
                    destination.get("Id")))
                # if the successor node is terminal junction, we must put the current
                # outgoing transition in the list of results for the backtracing algotithm
                if len(resultConnections) < 1:
                    result.append("{0}{1};".format(processedString, ot.get("Id")))
                else:
                    for rc in resultConnections:
                        result.append("{0}{1};{2}".format(processedString, ot.get("Id"), rc))
            elif cUtils.compareStringsIgnoreCase(destinationType, "state"):
                result.append("{0}{1};".format(processedString, ot.get("Id")))
            # put the current transition in the list of processed transitions
            processed.append(ot.get("Id", ""))
            # the final finalProcessedString represents a non-firing of all the
            # junction transitions captuting the case when no full transition can be
            # completed
        if len(processed) > 0:
            finalProcessedString = '{0}'.format(
                "".join("!{0};".format(str(itm)) for itm in processed))
            result.append(finalProcessedString)

        return result

    def __processTransition(self, _transitionForProcessing, _processedTransitions):
        allTransitions = []
        _processedTransitionsString = ""
        if len(_processedTransitions) > 0:
            _processedTransitionsString = '{0};'.format(
                "".join("!{0}".format(str(itm)) for itm in _processedTransitions))
        destination = _transitionForProcessing.get("Destination", {})
        newNodeForProcessingId = "{0}".format(destination.get("Id", ""))
        if cUtils.compareStringsIgnoreCase(destination.get("Type", ""), "junction"):
            junctionTransitions = self.__exploreJunctionTransitionsDFS(
                self.__getNodeById(newNodeForProcessingId))
            for jt in junctionTransitions:
                allTransitions.append("{0}{1};{2}".format(
                    _processedTransitionsString, _transitionForProcessing.get("Id", ""), jt))
        elif cUtils.compareStringsIgnoreCase(destination.get("Type", ""), "state"):
            allTransitions.append("{0}{1}".format(_processedTransitionsString, _transitionForProcessing.get("Id", ""))) if len(
                _processedTransitions) > 0 else allTransitions.append("{0}".format(_transitionForProcessing.get("Id", "")))
        return allTransitions

    def __processTransitions(self, _transitionsForProcessing, _processedTransitions):
        allTransitions = []
        _newPT = _processedTransitions[:]
        for transition in _transitionsForProcessing:
            allTransitions.extend(self.__processTransition(transition, _newPT))
            _newPT.append(transition.get("Id", ""))
        return allTransitions, _newPT

    def __generateNodeTransitions(self, node):
        allPossibleStateTransitions = []
        traversedTransitions = []
        allOuterTransitions = []
        allInnerTransitions = []
        allDefaultTransitions = []

        outerTrnsitions = sorted(node.get("OuterTransitions", []),
                                 key=lambda k: k['ExecutionOrder'])
        allTransitions, traversedTransitions = self.__processTransitions(
            outerTrnsitions, traversedTransitions)
        allPossibleStateTransitions.extend(allTransitions)
        allOuterTransitions = allTransitions[:]

        # add negation of all outgoing transitions as a duration action condition
        durationActionCondition = '{0}'.format(
            "".join("!{0}".format(str(itm)) for itm in traversedTransitions)) if len(traversedTransitions) > 0 else ""
        if not cUtils.compareStringsIgnoreCase("", durationActionCondition):
            allPossibleStateTransitions.append(durationActionCondition)
            allOuterTransitions.append(durationActionCondition)

        innerTransitions = sorted(node.get("InnerTransitions", []),
                                  key=lambda k: k['ExecutionOrder'])
        allTransitions, traversedTransitions = self.__processTransitions(
            innerTransitions, traversedTransitions)
        allPossibleStateTransitions.extend(allTransitions)
        allInnerTransitions = allTransitions[:]

        composition = node.get("Composition", {})
        defaultTransitions = composition.get("DefaultTransitions", [])
        allDefaultTransitions, traversedTransitions = self.__processTransitions(
            defaultTransitions, [])
        allPossibleStateTransitions.extend(allDefaultTransitions)

        return allOuterTransitions, allInnerTransitions, allDefaultTransitions

    def getJSON(self):
        return self.jsonChart

    def __generateAllNodeTransitions(self, state):
        outer, inner, default = self.__generateNodeTransitions(state)
        return {
            "stateId": state.get("Id", ""),
            "OuterTransitions":  outer,
            "InnerTransitions": inner,
            "DefaultTransitions": default
        }

    def generateAllTransitions(self):
        # this function generates all the possible stateflow transitions for a
        # stateflow diagram
        if self.allTransitions is None:
            transitionRelation = []
            allStates = self.__getAllSFStates()
            for state in allStates:
                transitionRelation.append(self.__generateAllNodeTransitions(state))
            self.allTransitions = transitionRelation

        return self.allTransitions

    def __generateTransitionRelationForState(self, state):
        # it is still not clear to me whether the transition relation shall be
        # a list or dictionary
        transitionRelation = []
        # basically here one needs to create the set of constraints that characterize the
        # transition relation of the

        return transitionRelation

    def generateTransitionRelation(self):
        # it is still not clear to me whether the transition relation shall be
        # a list or dictionary
        transitionRelation = []
        for stateTransitions in self.generateAllTransitions():
            transitionRelation.extend(self.__generateTransitionRelationForState(stateTransitions))

    def __isSubStateOf(self, childStateId, parentStateId):
        isSubstateOf = False
        parentState = self.__getSFStateById(parentStateId)
        parentComposition = parentState.get("Composition", None)
        if parentComposition is not None:
            if childStateId in parentComposition.get("States", []):
                isSubstateOf = True
            else:
                for substate in parentState.get("States", []):
                    isSubstateOf = self.__isSubStateOf(childStateId, substate)
                    if isSubstateOf:
                        break
        return isSubstateOf

    def __packStateForTransformation(self, state):
        pass

    def packForTransformation(self):
        # what information do I need for transforming each block?
        # if my source state is active, I will perform a set of actions and make a new (or the same) state active
        # the main problem is how to encode one simulation step
        # [s1, s1.1, s1.1.1, s1.1.2, s1.2, s1.2.1, s1.2.2]
        pass

    def test(self):
        print self.__getAllSFStates()
