from Lexer import *

instNumberEt3 = 0
alphabetChs = "abcdefghijklmnopqrstuvwxyz"
digitChs = "0123456789"
operatorsList = ['+', '*', '.', '|', '(', ')']
operatorsPrecedence= {}
unaryOps = ['*', '+']
binaryOps = ['|','.']

# ////////////////////////////////////////////////////////////////////////////////////////
# Etapa 2

#------------------------------------------------------------------------------------------------#
# CLASSES

class Token:
	# superclasa tuturor operatiilor (inclusiv a variabilelor)
	def __init__(self, instNumber):
		self.instNumber = instNumber

class UnaryOp(Token):
	# clasa specifica operatorilor UNARI
	def __init__(self, instNumber, opName, newRegex):
		super().__init__(instNumber)
		self.operand = newRegex
		self.operandName = opName

	def __str__(self):
		return self.operandName + "(" + str(self.operand) + ")"


class BinaryOp(Token):
	# clasa specifica operatorilor BINARI
	def __init__(self, instNumber, opName, newRegexFst, newRegexSnd):
		super().__init__(instNumber)
		self.operandFst = newRegexFst
		self.operandSnd = newRegexSnd
		self.operandName = opName

	def __str__(self):
		return self.operandName + "(" + str(self.operandFst) + ", " + str(self.operandSnd) + ")"

class Variable(Token):
	# clasa de baza (se retin detalii despre o variabila)
	def __init__(self, instNumber, opName):
		super().__init__(instNumber)
		self.operandName = opName

	def __str__(self):
		return self.operandName

class State:
	# clasa care contine detalii despre o Stare din automat
	def __init__(self, name, instNumber):
		self.stateName = name
		self.instNumber = instNumber

class NFA:
	# clasa ce contine detalii despre un automat finit NEDETERMINIST
	def __init__(self):
		# @ == epsilon
		self.statesNumber = None
		self.alphabet = []
		self.initialState = None
		self.delta = {}
		self.finalState = None

class DFA:
	# clasa ce contine detalii despre un automat finit DETERMINIST
	def __init__(self):
		self.alphabet = []
		self.states = []
		self.initialState = None
		self.delta = {}
		self.finalStates = []		

#------------------------------------------------------------------------------------------------#
# FUNCTIONS

def reduceStack(newRegex, regexStack):
	# Am ajuns la parsarea unei variabile, deci trebuie
	# completate lexemele pentru tokenii anterior scrisi pe stiva
	if regexStack:
		poppedEl = regexStack.pop()
		if isinstance(poppedEl, UnaryOp):
			# Daca avem un operator unar, i se completeaza lexemul
			# devenind astfel un lexem intreg 
			# Avand lexemul intreg, trebuie sa reducem din nou stiva
			poppedEl.operand = newRegex
			reduceStack(poppedEl, regexStack)
		elif isinstance(poppedEl, BinaryOp):
			if (poppedEl.operandFst == None):
				# in cazul unui operator binar, i se completeaza primul
				# camp, dar acesta nu devine lexem complet
				# deci trebuie reintrodus pe stiva
				poppedEl.operandFst = newRegex
				regexStack.append(poppedEl)
			elif (poppedEl.operandSnd == None):
				# in acest caz, ambii operanzi sunt definiti 
				# deci lexemul scos de pe stiva a devenit complet
				# si se realizeaza o noua reducere de stiva
				poppedEl.operandSnd = newRegex
				reduceStack(poppedEl, regexStack)
	else:
		# in cazul in care stiva e goala, stim ca elementul scos
		# reprezinta intreaga expresie parsata intr-un arbore
		regexStack.append(newRegex)

def createTransition(newNFA, currStateName, currCharacter, nextStateName, instNumberPtr):
	# se creeaza o noua tranzitie in automatul de stari newNFA
	# structura utilizata fiind un dictionar de tipul {cheie, dictionar}
	# cheia fiind Starea_Curenta, iar in subdictionar cheia este un ElementDinAlfabet
	# iar valoarea Starea_Urmatoare
	instNumber = instNumberPtr.pop()
	aux_dict = {}
	aux_dict[currCharacter] = State(nextStateName, instNumber)
	instNumber += 1
	newNFA.delta[State(currStateName, instNumber)] = aux_dict
	instNumber += 1
	instNumberPtr.append(instNumber)

def appendTransitions(newNFA, oldNFA):
	# tranzitiile dintr-un AFN sunt adaugate la un AFN mai nou
	# este foarte util faptul ca instantele de tip State
	# care au acelasi continut difera prin numarul de instanta
	# Astfel, putem avea in dictionar mai multe valori pentru aceeasi cheie
	for currState, newDict in oldNFA.delta.items():
		for char, nextState in newDict.items():	
			aux_dict = {}
			aux_dict[char] = nextState
			newNFA.delta[currState] = aux_dict

def processVariable(parseTree, stateNumberPtr, instNumberPtr):
	stateNumber = stateNumberPtr.pop()
	instNumber = instNumberPtr.pop()

	# Se creeaza un AFN cu alfabetul format doar din caracterul
	# descris de instanta clasei Variable
	newNFA = NFA()
	newNFA.alphabet.append(parseTree.operandName)
	# Se creeaza 2 noi stari, unice ca nume la nivel de program
	newNFA.initialState = State(stateNumber, instNumber)
	stateNumber += 1
	instNumber += 1
	newNFA.finalState = State(stateNumber, instNumber)
	stateNumber += 1
	instNumber += 1
	instNumberPtr.append(instNumber)
	# Se introduce o tranzitie de la starea initiala la starea finala
	# prin caracterul descris
	createTransition(newNFA, newNFA.initialState.stateName, 
		parseTree.operandName, newNFA.finalState.stateName, 
		instNumberPtr)

	stateNumberPtr.append(stateNumber)

	return newNFA

def processStarOp(subNFA, newNFA, stateNumberPtr, instNumberPtr):
	stateNumber = stateNumberPtr.pop()
	instNumber = instNumberPtr.pop()
	# Se creeaza 2 noi stari
	newNFA.initialState = State(stateNumber, instNumber)
	stateNumber += 1
	instNumber += 1
	newNFA.finalState = State(stateNumber, instNumber)
	stateNumber += 1
	instNumber += 1
	instNumberPtr.append(instNumber)
	# Se pun 4 tranzitii cu epsilon asa cum au fost descrise in algoritmul de la curs pentru Kleene Star
	createTransition(newNFA, newNFA.initialState.stateName, "@", subNFA.initialState.stateName, instNumberPtr)
	createTransition(newNFA, subNFA.finalState.stateName, "@", newNFA.finalState.stateName, instNumberPtr)
	createTransition(newNFA, newNFA.initialState.stateName, "@", newNFA.finalState.stateName, instNumberPtr)
	createTransition(newNFA, subNFA.finalState.stateName, "@", subNFA.initialState.stateName, instNumberPtr)
	# Din vechiul NFA se preiau toate tranzitiile in noul NFA
	appendTransitions(newNFA, subNFA)

	stateNumberPtr.append(stateNumber)

def processConcatOp(NFAFst, NFASnd, newNFA, instNumberPtr):
	instNumber = instNumberPtr.pop()
	# Crearea a 2 noi stari
	newNFA.initialState = State(NFAFst.initialState.stateName, instNumber)
	instNumber += 1
	newNFA.finalState = State(NFASnd.finalState.stateName, instNumber)
	instNumber += 1
	instNumberPtr.append(instNumber)
	# Adaugarea unei tranzitii intre cele 2 subNFA-uri
	createTransition(newNFA, NFAFst.finalState.stateName, "@", NFASnd.initialState.stateName, instNumberPtr)
	# Preluarea tranzitiilor din ambele subNFA-uri in noul NFA
	appendTransitions(newNFA, NFAFst)
	appendTransitions(newNFA, NFASnd)

def processUnionOp(NFAFst, NFASnd, newNFA, stateNumberPtr, instNumberPtr):
	stateNumber = stateNumberPtr.pop()
	instNumber = instNumberPtr.pop()
	# Crearea a 2 noi stari
	newNFA.initialState = State(stateNumber, instNumber)
	stateNumber += 1
	instNumber += 1
	newNFA.finalState = State(stateNumber, instNumber)
	stateNumber += 1
	instNumber += 1
	instNumberPtr.append(instNumber)
	# Adaugarea de tranzitii cu epsilon, conform algoritmului de la curs pentru Reuniune
	createTransition(newNFA, newNFA.initialState.stateName, "@", NFAFst.initialState.stateName, instNumberPtr)
	createTransition(newNFA, newNFA.initialState.stateName, "@", NFASnd.initialState.stateName, instNumberPtr)
	createTransition(newNFA, NFAFst.finalState.stateName, "@", newNFA.finalState.stateName, instNumberPtr)
	createTransition(newNFA, NFASnd.finalState.stateName, "@", newNFA.finalState.stateName, instNumberPtr)
	# Preluarea tranzitiilor din ambele subNFA-uri in noul NFA
	appendTransitions(newNFA, NFAFst)
	appendTransitions(newNFA, NFASnd)
	stateNumberPtr.append(stateNumber)

def refactorStates(thisNFA, auxStateNumber, instNumberPtr):
	# Functie utila pentru operatia de PLUS
	# Inainte de a concatena e cu e* este necesar sa aplicam +x pentru toate
	# starile din automatul e*, intrucat algoritmul pentru e* realizat aici
	# adauga 2 stari si doar copiaza toate tranzitiile din NFA-ul pentru 
	# ceea ce nu este corect intrucat toate tranzitiile pentru automatul ee* ar fi duplicate
	# de aceea, este necesar ca penntru fiecare stare din automatul e* rangul sau sa fie
	# crescut cu +x pentru a asigura unicitatea numelor starilor
	# In acest caz, este suficient sa incrementam cu numarul de stari din automatul e
	# Ex: e are 100 de stari (de la 0 la 99)
	# e* va fi de forma: stare100 + automat e + stare 101
	# dupa transformate e* va fi: stare200 + automat e(stari de la 100 la 199) + stare 201 
	newDeltaFunc = {}
	instNumber = instNumberPtr.pop()

	thisNFA.initialState = State(int(thisNFA.initialState.stateName) + auxStateNumber, instNumber) 
	instNumber += 1
	thisNFA.finalState = State(int(thisNFA.finalState.stateName) + auxStateNumber, instNumber)
	instNumber += 1

	for currState, newDict in thisNFA.delta.items():
		for char, nextState in newDict.items():	
			aux_dict = {}
			aux_dict[char] = State(int(nextState.stateName) + auxStateNumber, instNumber)
			instNumber += 1
			newDeltaFunc[State(int(currState.stateName) + auxStateNumber, instNumber)] = aux_dict
			instNumber += 1
	thisNFA.delta = newDeltaFunc
	instNumberPtr.append(instNumber)

def traverseTree(parseTree, stateNumberPtr, instNumberPtr):
	if isinstance(parseTree, Variable):
		# am ajuns la nivel de variabila (caz de baza)
		newNFA = processVariable(parseTree, stateNumberPtr, instNumberPtr)
		return newNFA
	else:
		if isinstance(parseTree, UnaryOp):
			subNFA = traverseTree(parseTree.operand, stateNumberPtr, instNumberPtr)
			# am procesat NFA-ul de jos, deci trebuie realizat un nou layer
			newNFA = NFA()
			for alphabetEl in subNFA.alphabet:
				newNFA.alphabet.append(alphabetEl)
			if parseTree.operandName == "STAR":
				processStarOp(subNFA, newNFA, stateNumberPtr, instNumberPtr)
			elif parseTree.operandName == "PLUS":
				# PLUS <=> CONCAT(subNFA, subNFA*)
				NFASnd = NFA()
				# numarul de stari din subNFA
				auxStateNumber = stateNumberPtr[0]
				processStarOp(subNFA, NFASnd, stateNumberPtr, instNumberPtr)
				# Pt fiecare indice al fiecarei stari (tranzitii + st.init + st.finala) 
				# aplicam o functie de tipul +(nrStariSubNFA)
				refactorStates(NFASnd, auxStateNumber, instNumberPtr)
				newStateNumber = stateNumberPtr.pop() + auxStateNumber
				stateNumberPtr.append(newStateNumber)
				processConcatOp(subNFA, NFASnd, newNFA, instNumberPtr)

			return newNFA
		elif isinstance(parseTree, BinaryOp):
			NFAFst = traverseTree(parseTree.operandFst, stateNumberPtr, instNumberPtr)
			NFASnd = traverseTree(parseTree.operandSnd, stateNumberPtr, instNumberPtr)
			# Din 2 subNFA-uri trebuie realizat un nou NFA prin operatii binare specifice 
			newNFA = NFA()
			# Realizarea reuniunii alfabetelor
			for alphabetEl in NFAFst.alphabet:
				if alphabetEl not in newNFA.alphabet:
					newNFA.alphabet.append(alphabetEl)
			for alphabetEl in NFASnd.alphabet:
				if alphabetEl not in newNFA.alphabet:
					newNFA.alphabet.append(alphabetEl)
			if parseTree.operandName == "CONCAT":
				processConcatOp(NFAFst, NFASnd, newNFA, instNumberPtr)
			elif parseTree.operandName == "UNION":
				processUnionOp(NFAFst, NFASnd, newNFA, stateNumberPtr, instNumberPtr)
			return newNFA

def sameStateChecker(FstState, SndState):
	# Verificarea conform careia o stare de tipul
	# [x1, x2, ..., x_n] este sau nu diferita de o stare [y1, y2, ..., y_n]
	# SE PRESUPUNE CA x1 <= x2 <= ... <= x_n si y1 <= y2 <= ... <= y_n
	if len(FstState) != len(SndState):
		return False
	else:
		for i in range(0, len(FstState)):
			if FstState[i] != SndState[i]:
				return False
		return True

def ReuniteStates(FstState, SndState):
	# Operatia de reuniune a doua multimi
	# [x1 .. xn] U [y1 .. yn]
	newState = []
	for el1 in FstState:
		if el1 not in newState:
			newState.append(el1)
	for el2 in SndState:
		if el2 not in newState:
			newState.append(el2)
	return newState

def calculateEClosures(finalNFA):
	# Calculul inchiderilor prin epsilon
	# In principiu, algoritm de parcurgere a unui graf in latime(BFS)
	EClosures = []
	for i in range(0, finalNFA.statesNumber):
		EClosures.append([i])
		start = 0
		end = len(EClosures[i])
		while start != end:
			for currState, newDict in finalNFA.delta.items():
				for char, nextState in newDict.items():	
					if currState.stateName == EClosures[i][start] and char == "@" and nextState.stateName not in EClosures[i]:
						EClosures[i].append(nextState.stateName)
						end += 1
			start += 1
	return EClosures

def createDFATransitions(theDFA, finalNFA, EClosures, instNumber):
	start = 0
	end = len(theDFA.states)
	# Se realizeaza din nou algortimul pentru parcurgere in latime
	# a unui graf, coada fiind lista de stari a automatului DFA
	while start != end:
		# Se preia o stare din lista de stari a DFA-ului
		statesSet = theDFA.states[start]
		for elAlphabet in theDFA.alphabet:
			# crearea unei noi stari a DFA-ului prin reuniunea mai multor stari din NFA
			dfaNextState = []
			# pentru fiecare stare din statesSet a DFA-ului se verifica, pe un caracter, 
			# caile pe care se poate din acea stare ajutandu-ne de tranzitiile din NFA
			# [x1, x2, ..., xn]
			# xi ---- caract. 'c' ----> yj
			# daca y_j nu este in dfaNextState (care la randul sau e o lista)
			# atunci aceasta stare se adauga in lista dfaNextState
			for state in statesSet:
				for currState, newDict in finalNFA.delta.items():
					for char, nextState in newDict.items():
						if currState.stateName == state and char == elAlphabet:
							dfaNextState = ReuniteStates(dfaNextState, EClosures[nextState.stateName])
			# boolean utilizat pentru a verifica daca o anumita
			# stare nou creata este deja introdusa in lista de stari a DFA-ului
			stateAlreadyAppended = 0
			dfaNextState.sort()
			for el in theDFA.states:
				if sameStateChecker(dfaNextState[:], el[:]) == True:
					stateAlreadyAppended = 1
					break
			# Introducerea unei noi tranzitii in NFA
			# [] reprezinta starea de sink
			aux_dict = {}
			aux_dict[elAlphabet] = State(dfaNextState[:], instNumber)
			instNumber += 1
			theDFA.delta[State(statesSet[:], instNumber)] = aux_dict
			instNumber += 1
			# introducerea in lista de stari a DFA-ului starea noua(daca e cazul)
			if dfaNextState != [] and stateAlreadyAppended == 0:
				theDFA.states.append(dfaNextState[:])
				end += 1
				
		start += 1

def NFAtoDFA(finalNFA):
	# Inchiderile cu epsilon
	theDFA = DFA()
	EClosures = calculateEClosures(finalNFA)
	instNumber = 0
	# Copierea alfabetului
	theDFA.alphabet = finalNFA.alphabet[:]
	theDFA.alphabet.sort()
	# Starea initiala reprezinta E(stareInitialaNFA)
	theDFA.initialState = EClosures[finalNFA.initialState.stateName]
	theDFA.initialState.sort()
	# Starile DFA-ului vor fi liste SORTATE de stari(reprezentate ca numere)
	# [[s_11,s_12...s_1n], [s_21,s_22,...s_2m] ... [s_p1,s_p2,s_pz]]
	theDFA.states.append(theDFA.initialState[:])
	# crearea noilor stari si a tranzitiilor in noul DFA
	createDFATransitions(theDFA, finalNFA, EClosures, instNumber)
	# crearea sink-state-ului
	for elAlphabet in theDFA.alphabet:
		aux_dict = {}
		aux_dict[elAlphabet] = State([], instNumber)
		instNumber += 1
		theDFA.delta[State([], instNumber)] = aux_dict
		instNumber += 1
	# Calculate final states
	for state in theDFA.states:
		if finalNFA.finalState.stateName in state:
			theDFA.finalStates.append(state) 
	return theDFA

def createDFAstr(theDFA, tokenName):
	finalResult = ""
	alphabetFormat = ""
	# Scrierea alfabetului DFA-ului conform conventiei din ref-uri
	for elAlphabet in theDFA.alphabet:
		alphabetFormat += elAlphabet
	finalResult += alphabetFormat
	finalResult += '\n'
	finalResult += tokenName
	finalResult += '\n'
	# Se realizeaza o mapare a starilor DFA-ului
	# [s11, s12, ... , s1n1] -> 0
	# [s21, s22, ... , s2n2] -> 1
	# ...
	# [sm1, sm2, ... , s_mn_m] -> m - 1
	# m - numar stari din DFA
	# sink-state [] -> m
	# pentru a respecta conventia de afisare
	DFAStateIndex = 0
	mapStatesIndices = {}
	for state in theDFA.states:
		mapStatesIndices[str(state)] = DFAStateIndex
		DFAStateIndex += 1
	mapStatesIndices[str([])] = DFAStateIndex
	finalResult += str(mapStatesIndices[str(theDFA.initialState)])
	finalResult += '\n'
	# Scrierea, in fisierul de iesire, a tranzitiilor DFA-ului conform conventiei
	for currState, newDict in theDFA.delta.items():
		for char, nextState in newDict.items():
			finalResult += (str(mapStatesIndices[str(currState.stateName)]) + ',\''
							+ char + '\','
							+ str(mapStatesIndices[str(nextState.stateName)]))
			finalResult += '\n'
	finalStatesFormat = ""
	cnt = 1
	for finalState in theDFA.finalStates:
		finalStatesFormat += str(mapStatesIndices[str(finalState)])
		if cnt != len(theDFA.finalStates):
			finalStatesFormat += ' '
		cnt += 1
	finalResult += finalStatesFormat
	finalResult += '\n'
	return finalResult

#------------------------------------------------------------------------------------------------#

# ////////////////////////////////////////////////////////////////////////////////////////
# Etapa 3
class TokenEt3:
	# clasa in care se retin detalii despre token si regex
	def __init__(self, instNumberEt3, tokenName, associatedRegex):
		self.instNumber = instNumberEt3
		self.name = tokenName
		self.regex = associatedRegex
		self.prenexFormOfRegex = []
		self.simplifyRegex()

	def simplifyRegex(self):
		rebulitRegex = ""
		# print(self.regex)
		i = 0
		while i < len(self.regex):
			if self.regex[i] == ' ':
				i += 1
			elif self.regex[i] == '[':
				rebulitRegex += '('
				if self.regex[i] == 'a':
					for alphabetCh in alphabetChs:
						rebulitRegex += '\''
						rebulitRegex += alphabetCh
						rebulitRegex += '\''
						if alphabetCh != 'z':
							rebulitRegex += '|'
				elif self.regex[i] == '0':
					for digitCh in digitChs:
						rebulitRegex += '\''
						rebulitRegex += digitCh
						rebulitRegex += '\''
						if digitCh != '9':
							rebulitRegex += '|'

				rebulitRegex += ')'
				i += len("[a-z]+")
			elif self.regex[i] == '\'':
				rebulitRegex += '\''
				if self.regex[i + 1] == '\\':
					if self.regex[i + 2] == 'n':
						rebulitRegex += '\n'
					elif self.regex[i + 2] == 't':
						rebulitRegex += 't'
					elif self.regex[i + 2] == '\'':
						rebulitRegex += '\''
					elif self.regex[i + 2] == '\\':
						rebulitRegex += '\\'
					i += len("\'\\n\'")
				else:
					rebulitRegex += self.regex[i + 1]
					i += len("\'!\'")
				rebulitRegex += '\''
				if i < len(self.regex) and self.regex[i] not in operatorsList:
					rebulitRegex += '.'
				elif i < len(self.regex) and self.regex[i] == '(':
					rebulitRegex += '.'
			else:
				if self.regex[i] not in operatorsList and i < len(self.regex) - 1 and self.regex[i + 1] not in operatorsList:
					rebulitRegex += '\''
					rebulitRegex += self.regex[i]
					rebulitRegex += '\''
					rebulitRegex += '.'
				elif self.regex[i] not in operatorsList and i < len(self.regex) - 1 and self.regex[i + 1] == '(':
					rebulitRegex += '\''
					rebulitRegex += self.regex[i]
					rebulitRegex += '\''
					rebulitRegex += '.'
				elif self.regex[i] not in operatorsList:
					rebulitRegex += '\''
					rebulitRegex += self.regex[i]
					rebulitRegex += '\''
				else:
					rebulitRegex += self.regex[i]
					if self.regex[i] != '(' and self.regex[i] != '|' and i < len(self.regex) - 1 and (self.regex[i + 1] not in operatorsList or self.regex[i + 1] == '('):
						rebulitRegex += '.'
				i += 1
		# print(rebulitRegex)
		self.regex = rebulitRegex
	
	def transfToPrenex(self):
		stack = []
		prenexStack = []

		# print("transfToPrenex " + self.name + ':' + self.regex)
		index = len(self.regex) - 1

		while index > -1:
			character = self.regex[index]
			if character == '\'':
				character = self.regex[index - 1]
				index -= 2
				prenexStack.append('\'' + character + '\'')
				while len(stack) > 0 and stack[-1] in unaryOps:
					poppedCh = stack.pop()
					prenexStack.append(poppedCh)
			elif character == ')':
				stack.append(character)
			elif character == '(':
				poppedCh = stack.pop()
				prenexStack.append(poppedCh)
				while poppedCh != ')':
					poppedCh = stack.pop()
					prenexStack.append(poppedCh)
				prenexStack.pop()
				while len(stack) > 0 and (stack[-1] in unaryOps):
					poppedCh = stack.pop()
					prenexStack.append(poppedCh)
			elif character in operatorsList:
				if (len(stack) > 0 and (stack[-1] == ')' or operatorsPrecedence[character] >= operatorsPrecedence[stack[-1]])) or (len(stack) == 0):
					stack.append(character)
				else:
					stack.append(character)
					poppedCh = stack.pop()
					prenexStack.append(poppedCh)
					while len(stack) > 0 and stack[-1] != ')' and operatorsPrecedence[poppedCh] < operatorsPrecedence[stack[-1]]:
						poppedCh = stack.pop()
						prenexStack.append(poppedCh)
			index -= 1
		while len(stack) != 0:
			prenexStack.append(stack.pop())
		regexPrenexForm = []
		while len(prenexStack) != 0:
			mystr = prenexStack.pop()
			if mystr[0] == '\'':
				if mystr[1] == '\n':
					regexPrenexForm.append('\\' + 'n')
				elif mystr[1] == '\t':
					regexPrenexForm.append('\\' + 't')
				elif mystr[1] == '\'':
					regexPrenexForm.append('\\' + '\'')
				elif mystr[1] == '\\':
					regexPrenexForm.append('\\' + '\\')
				else:
					regexPrenexForm.append(mystr[1])
			elif mystr[0] == '*':
				regexPrenexForm.append("STAR")
			elif mystr[0] == '.':
				regexPrenexForm.append("CONCAT")
			elif mystr[0] == '|':
				regexPrenexForm.append("UNION")
			elif mystr[0] == '+':
				regexPrenexForm.append("PLUS")
		# print(regexPrenexForm)
		self.prenexFormOfRegex = regexPrenexForm

def transformPrenexToDFA(token):
	# se retin in liste diferite tokenii care reprezinta operatii unare, binare
	# print(token.regex)
	unaryOps = ["STAR", "PLUS"]
	binaryOps = ["CONCAT", "UNION"]

	regexStack = []
	instNumber = 0

	prenexForm = token.prenexFormOfRegex
	# print("ToDFA: " + str(prenexForm))

	# LOGICA DE CREARE A ARBORELUI:
	# Pentru fiecare token de tip operatie se adauga in stiva o noua instanta a clasei specifice
	# La parsarea unei Variabile, se trece in faza de reducere a stivei, adica crearea legaturilor
	# specifice arborelui in mod recursiv
	for word in prenexForm:
		instNumber
		if word in unaryOps:
			# trebuie parsat un operator unar
			regexStack.append(UnaryOp(instNumber, word, None))
		elif word in binaryOps:
			# trebuie parsat un operator binar
			regexStack.append(BinaryOp(instNumber, word, None, None))
		else:
			# trebuie parsata o variabila
			newVar = Variable(instNumber, word)
			reduceStack(newVar, regexStack)
		
		instNumber += 1

	# Arborele generat se va afla pe prima pozitie (adica 0) din lista folosita ca stiva
	tree = regexStack.pop()
	# print(tree)
	stateNumber = [0] # contorizarea starilor din NFA
	instNumberPtr = [0] # unicitatea instantelor de tip State
	# Regex -> NFA
	finalNFA = traverseTree(tree, stateNumber, instNumberPtr)
	finalNFA.statesNumber = stateNumber[0]
	# NFA -> DFA
	finalDFA = NFAtoDFA(finalNFA)
	# print(token.name)
	return createDFAstr(finalDFA, token.name)

def preprocessLexerInput(lexerInput, tokenList):
	lexerInputLists = lexerInput.split(";\n")
	lexerInputLists.pop()
	# print(lexerInputLists)

	for el in lexerInputLists:
		global instNumberEt3
		tokenRegexPair = el.split(" ", 1)
		# print("TokenRegexPair: " + str(tokenRegexPair))
		tokenList.append(TokenEt3(instNumberEt3, tokenRegexPair[0], tokenRegexPair[1]))
		instNumberEt3 += 1

def runcompletelexer(lexer, finput, foutput):
	global instNumberEt3
	instNumberEt3 = 0
	tokenList = []
	lexerFileHandler = open(lexer, 'r')
	lexerInput = lexerFileHandler.read()
	preprocessLexerInput(lexerInput, tokenList)
	lexerFileHandler.close()

	operatorsPrecedence['+'] = 3
	operatorsPrecedence['*'] = 3
	operatorsPrecedence['.'] = 2
	operatorsPrecedence['|'] = 1

	strAllDFAs = ""
	for el in tokenList:
		el.transfToPrenex()
		# print(el.name + ':' + el.regex)
		DFAstr = transformPrenexToDFA(el)
		strAllDFAs += DFAstr
		strAllDFAs += '\n'
	
	wordFile = open(finput, 'r')
	wordToProcess = wordFile.read()
	wordFile.close()

	dfa_codif = strAllDFAs.split("\n\n")
	dfa_codif.pop()

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
		error = 1
		for i in range(0, len(dfas)):
			(index, errRecv) = dfas[i].max_prefix_len(my_word)
			if index > max_index and errRecv == 0:
				error = 0
				max_index = index
				best_dfa = i
			elif index > max_index_err and errRecv == 1 and error == 1:
				max_index_err = index
				best_dfa = i
		if error == 0:
			parsed_ch += max_index
		if error == 1:
			parsed_ch += max_index_err
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
	writeToFile = open(foutput, 'w')
	if error == 0:
		print(output[0:(len(output) - 1)], file=writeToFile)
	else:
		print("No viable alternative at character " + str(parsed_ch - 1) + ", line 0", file=writeToFile, end='')
	writeToFile.close()

def runparser(finput, foutput):
	outHandler = open(foutput, 'w')
	print("Hello World", file=outHandler)
