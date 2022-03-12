from typing import Dict, List

class StateEt1:
	def __init__(self, state_name):
		self.name = state_name


Conf = (StateEt1, str)


class DFAEt1:
	def __init__(self, str_input):
		self.alphabet: List[str] = list()
		self.token: str
		self.initialStateEt1: StateEt1 = StateEt1(str)
		self.delta: Dict[StateEt1, Dict[str, StateEt1]] = dict()
		self.sinkStates: List[StateEt1] = list()
		self.finalStates: List[StateEt1] = list()

		lines = str_input.split("\n")
		i = 0
		while i < len(lines[0]):
			if (lines[0][i] == '\\' and i + 1 < len(lines[0]) and lines[0][i + 1] == 'n'):
				self.alphabet.append('\n')
				i += 1
			else:
				self.alphabet.append(lines[0][i])
			i += 1
		
		self.token = lines[1]
		
		self.initialState = StateEt1(lines[2])
		
		transitions = lines[3:len(lines) - 1]
		
		self.delta = {}
		for transition in transitions:
			state_char_state = transition.split(",")

			aux_dict = {}
			if len(state_char_state[1]) == 4 and state_char_state[1][1] == '\\' and state_char_state[1][2] == 'n':
				aux_dict['\n'] = StateEt1(state_char_state[2]) 
			else:
				aux_dict[state_char_state[1][1]] = StateEt1(state_char_state[2])
			self.delta[StateEt1(state_char_state[0])] = aux_dict
		
		for el in lines[len(lines) - 1].split(" "):
			if el not in self.finalStates:
				self.finalStates.append(StateEt1(el))

		self.computeSinkStates()

	def computeSinkStates(self):
		invertedDelta = {}
		DFAstates = []
		for curr_state, new_dict in self.delta.items():
			for char, next_state in new_dict.items():
				aux_dict = {}
				aux_dict[char] = StateEt1(curr_state.name)
				invertedDelta[StateEt1(next_state.name)] = aux_dict
				
				if curr_state.name not in DFAstates:
					DFAstates.append(curr_state.name)
				if next_state.name not in DFAstates:
					DFAstates.append(next_state.name)
		for finalState in self.finalStates:
			queue = []
			queue.append(finalState.name)
			while len(queue) > 0:
				poppedState = queue.pop(0)
				index = 0
				bec = 0
				for DFAstate in DFAstates:
					if DFAstate == poppedState:
						bec = 1
						break
					index += 1
				if bec == 1:
					DFAstates.pop(index)
				for curr_state, new_dict in invertedDelta.items():
					for char, next_state in new_dict.items():
						if curr_state.name == poppedState and next_state.name in DFAstates:
							queue.append(next_state.name)
		self.sinkStates = DFAstates
		# print("DFAstatesRemaining:" + str(DFAstates))

	def step(self, conf: Conf) -> Conf:
		(state, word) = conf
		for curr_state, new_dict in self.delta.items():
			for char, next_state in new_dict.items():
				if curr_state.name == state.name and word[0] == char:
					if next_state.name in self.sinkStates:
						return (StateEt1("sink"), word[0:])
					else:
						return next_state, word[1:]
		return (StateEt1("sink"), word[0:])

	def max_prefix_len(self, word: str) -> (int, int):
		(state, word) = (self.initialState, word)
		prefix_len = 0
		pos = 0
		err = 1
		while 1:
			if word == "":
				pos += 1
				break
			(state, word) = self.step((state, word))
			pos += 1
			if state.name == "sink":
				if err == 1:
					prefix_len = pos
				break
			
			for final_state in self.finalStates:
				if final_state.name == state.name:
					err = 0
					prefix_len = pos
		return (prefix_len, err)


def runlexer(lexer, finput, foutput):
	writeToFile = open(foutput, 'w')
	
	file_in = open(lexer, 'r')
	dfa_str = file_in.read()
	dfa_codif = dfa_str.split("\n\n")
	
	dfas = []
	for el in dfa_codif:
		dfas.append(DFAEt1(el))
	my_word_copy = (open(finput, 'r')).read()
	my_word = my_word_copy
	output = ""
	error = 0
	parsed_ch = 0
	while 1:
		if my_word == "":
			parsed_ch += 1
			break
		max_index = 0
		max_index_err = 0
		best_dfa = -1
		# print(my_word)
		error = 1
		for i in range(0, len(dfas)):
			(index, errRecv) = dfas[i].max_prefix_len(my_word)
			# print('{' + str(index) + ' ' + str(errRecv) + '}', end=' ')
			if index > max_index and errRecv == 0:
				error = 0
				max_index = index
				best_dfa = i
			elif index > max_index_err and errRecv == 1 and error == 1:
				max_index_err = index
				best_dfa = i
		# print()
		# print("===============")
		if error == 0:
			parsed_ch += max_index
		if error == 1:
			parsed_ch += max_index_err
			# print("ERROR:" + my_word)
			break
		result = dfas[best_dfa].token
		result += ' '
		for i in range(0, max_index):
			if my_word[i] == '\n':
				result += '\\'
				result += 'n'
			else:
				result += my_word[i]
		output += result
		output += '\n'
		my_word = my_word[max_index:]
	if error == 0:
		print(output[0:(len(output) - 1)], file=writeToFile)
	else:
		print("No viable alternative at character " + str(parsed_ch - 1) + ", line 0", file=writeToFile, end='')
	writeToFile.close()