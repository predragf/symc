import modules.utils.utils as cUtils
import json  # I need this only for preety printing
import copy


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
        # basically here one needs to create the set of constraints that characterize the
        # transition relation of the
        # print('State:', state)
        transitionRelation = []
        transitions  = state.get('OuterTransitions')
        state_id     = state.get('stateId')
        stateSFS     = self.__getSFStateById(state_id)
        state_name   = stateSFS.get('Name')
        state_action = stateSFS.get('Actions')
        state_exit   = state_action.get('Exit')
        outer_trans  = stateSFS.get('OuterTransitions')
        all_states   = self.__getAllSFStates()
        
        all_states_list = []
        for state in all_states:
            all_states_list.append(state.get('Name'))
        
        trans_ids = []

        if len(outer_trans) < 1:
            return ''
        
        outer_trans = outer_trans
        for trans in transitions:
            trans = trans.replace("!",";!")
            trans_ids = trans.split(';')
            
            transition_action = []
            transition_enable = []
            for trans_tmp in trans_ids:
                if trans_tmp == '': 
                    continue

                for outer in outer_trans:
                    if trans_tmp[0] == '!':
                        trans_compare_id = trans_tmp[1:]
                    else:
                        trans_compare_id = trans_tmp

                    if int(outer['Id']) == int(trans_compare_id):
                        outer_tmp = copy.deepcopy(outer)
                        break
                
                if trans_tmp[0] == '!':
                    transition_enable.append('disable')
                else:
                    transition_enable.append('enable')
                transition_action.append(outer['TransitionAction'][0])

            dest_state        = outer_tmp['Destination']
            dest_state_id     = dest_state['Id']
            dest_state_SFS    = self.__getSFStateById(dest_state_id)
            dest_state_name   = dest_state_SFS.get('Name')
            dest_state_action = dest_state_SFS.get('Actions')
            dest_state_entry  = dest_state_action.get('Entry')

            transitionRelation.append(self.__generateTransitionRelationForTransition(transition_action, state_name, dest_state_name, dest_state_entry, all_states_list, transition_enable))

        return transitionRelation

    def __generateTransitionRelationForTransition(self, transition_string, state_name, dest_state_name, dest_state_entry, all_states_list, transition_enable):
        # Generate a transition relation from state
        
        if len(transition_string) > 1:
            transition_action_append = ' (and'
        else:
            transition_action_append = ''

        for k in range(len(transition_string)):
            transition_action_string = self.__PrepareActionString(transition_string[k])
            if transition_enable[k] == 'disable':
                transition_action_string = '~(' + transition_action_string + ')'
            transition_action_prefix = self.__InfixToPrefix(transition_action_string)
            transition_action_append = transition_action_append + ' ' + self.__AppendCurrentOrNext(transition_action_prefix, '_current') 
        
        if len(transition_string) > 1:            
            transition_action_append = transition_action_append + ')'
            

        assert_text = '(assert (implies ((and ' + state_name + '_current' + transition_action_append + ')'
        dest_state_entry   = self.__PrepareActionString(dest_state_entry[0])
        dest_state_string  = self.__InfixToPrefix('(' + dest_state_entry + ')')
        dest_state_append  = self.__AppendCurrentOrNext(dest_state_string, '_next')
        state_string       = '(= true ' + dest_state_name + '_next)'
        other_state_string = self.__StateInfixString(all_states_list, dest_state_name)

        transition_string = assert_text + ' (and ' + dest_state_append + ' ' + state_string + ' ' + other_state_string[:-1] + ')))'
        print(transition_string) 
        return transition_string

    def __AppendCurrentOrNext(self, string, appending_string):
        non_variables = ['+', '-', '/', '*', '!=', '=', '>=', '<=', 'and', 'or', '(', ')', 'false', 'true', 'not']
        
        split_string = string.split(' ')

        appended_string = ''
        for string_tmp in split_string:

            try:
                numLeftParanthesis = string_tmp.count('(')
                numRightParanthesis = string_tmp.count(')')
                if numRightParanthesis == 0:
                    float(string_tmp[numLeftParanthesis:])
                else:
                    float(string_tmp[numLeftParanthesis:-numRightParanthesis])
            except:
                if not (string_tmp in non_variables):
                    if string_tmp[0] == "(":
                        if not (string_tmp[numLeftParanthesis:] in non_variables):
                            string_tmp = string_tmp + appending_string

                    elif string_tmp[-1] == ')':
                        if not (string_tmp[:-numRightParanthesis] in non_variables):
                            string_tmp = string_tmp[:-numRightParanthesis] + appending_string + ')' * numRightParanthesis
                    else:
                        string_tmp = string_tmp + appending_string
            if appended_string == '':
                appended_string = string_tmp
            else:
                appended_string = appended_string + ' ' + string_tmp

        return appended_string

    def __StateInfixString(self, all_states_list, dest_state_name):
        
        state_string = ''
        for k in all_states_list:
            if k != dest_state_name:
                state_string = state_string + self.__InfixToPrefix('(' + k + '_next=false)') + ' '
        
        return state_string

    def __PrepareActionString(self, action_string):
        
        action_string = action_string.replace("\n", '')
        action_string = action_string.replace(';',  '')

        #Remove comments
        while action_string.find('/*') != -1 and action_string.find('*/') != -1:
            left = action_string.find('/*')
            right = action_string.find('*/')
            action_string = action_string[:left] + action_string[right:]

        left_bracket  = action_string.find('[')
        right_bracket = action_string.find(']')

        if left_bracket == -1 or right_bracket == -1:
            left_bracket = 0
        else:
            action_string = action_string[left_bracket + 1:right_bracket]
        
        return action_string

    def __InfixToPrefix(self, transitionAction):
        # Convert infix notation to prefix notation

        trans_act_no_space = transitionAction.replace(' ', '')
        
        left_paranthesis, right_paranthesis = self.__CheckParanthesis(trans_act_no_space)

        num_paranthesis      = len(left_paranthesis)
        current_string       = copy.deepcopy(trans_act_no_space)
        string_concatenated  = copy.deepcopy(trans_act_no_space)
        paranthesis_objects  = [None] * num_paranthesis
        
        for m in range(num_paranthesis):
            string_paranthesis     = string_concatenated[left_paranthesis[-1] + 1: right_paranthesis[-1]]
            paranthesis_objects[m] = self.__ParseInfixToPrefix(string_paranthesis, 0)
            string_concatenated = current_string[0:left_paranthesis[-1]] + 'id:' + str(m) + current_string[right_paranthesis[-1] + 1:]
            current_string      = copy.deepcopy(string_concatenated)
            left_paranthesis, right_paranthesis = self.__CheckParanthesis(string_concatenated)

        current_string_complete = self.__ParseInfixToPrefix(current_string, 1)

        for k in range(num_paranthesis, 0, -1):
            tmp_id_str = 'id:' + str(k-1) 
            current_string_complete = current_string_complete.replace(tmp_id_str, paranthesis_objects[k-1])
        
        current_string_complete = self.__ParseInfixToPrefixUnary(current_string_complete)

        return current_string_complete

    def __CheckParanthesis(self, string):
        # Computes the left and right paranthesis positions
        # from an input string

        left_paranthesis  = []
        right_paranthesis = []

        for k in range(len(string)):

             if string[k] == '(':
                 left_paranthesis.append(k)
                 right_paranthesis.append(-1)
             elif string[k] == ')':
                 for m in range(len(left_paranthesis), 0, -1):
                     if right_paranthesis[m-1] == -1:
                         right_paranthesis[m-1] = k
                         break

        return left_paranthesis, right_paranthesis

    def __ParseInfixToPrefixUnary(self, string):
        
        new_string = string.replace('~', 'not ')

        return new_string

    def __ParseInfixToPrefix(self, string, priority):

        operators   = ["==", "~=", ">=", "<=", "&&",  "||", '=', '+', '-', '*', '/']
        c_operators = ['=',  "!=", ">=", "<=", "and", "or", '=', '+', '-', '*', '/']

        if priority >= len(operators):
            return string

        current_string = string.split(operators[priority])
        prefix_string = current_string[-1]

        for k in current_string:
            if k == '':
                current_string.remove('')

        if len(current_string) == 1:
            return self.__ParseInfixToPrefix(current_string[0], priority + 1)
            
        else:
            for k in range(len(current_string), 1, -1):
                if k == len(current_string) - 1:
                    prefix_string = '(' + c_operators[priority] + ' ' + self.__ParseInfixToPrefix(current_string[k - 2], priority + 1) + ' ' + self.__ParseInfixToPrefix(prefix_string, priority + 1) + ')'
                else:
                    prefix_string = '(' + c_operators[priority] + ' ' + self.__ParseInfixToPrefix(current_string[k - 2], priority + 1) + ' ' + prefix_string + ')'

        return prefix_string

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
