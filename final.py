from ast import Constant
from matplotlib.pyplot import new_figure_manager
from numpy import isin
from prolog_structures import Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass
'''
Please read prolog_structures.py for data structures
that represent Prolog terms, rules, and goals.
'''
class Interpreter:
	def __init__(self):
		pass

	'''
	Example
	occurs_check (v, t) where v is of type Variable, t is of type Term.
	occurs_check (v, t) returns true if the Prolog Variable v occurs in t.
	Please see the lecture note Control in Prolog to revisit the concept of
	occurs-check.
	'''
	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False


	'''
	Problem 1
	variables_of_term (t) where t is of type Term.
	variables_of_clause (c) where c is of type Rule.

	The function should return the Variables contained in a term or a rule
	using Python set.

	The result must be saved in a Python set. The type of each element (a Prolog Variable)
	in the set is Variable.
	'''
	def variables_of_term (self, t : Term) -> set :
		x = set()
		if isinstance(t,Variable):
			return set([t])
		elif isinstance(t,Rule):
			self.variables_of_clause(t)
		elif isinstance(t,Function):
			for t in t.terms:
				temp = self.variables_of_term (t)
				x = x.union(temp)
		return x

	def variables_of_clause (self, c : Rule) -> set :
		if isinstance(c,Term):
			self.variables_of_term(c)
	
		x = self.variables_of_term(c.head)
		for i in c.body.terms:
			y = self.variables_of_term(i)
			x = x.union(y)
		return x


	'''
	Problem 2
	substitute_in_term (s, t) where s is of type dictionary and t is of type Term
	substitute_in_clause (s, t) where s is of type dictionary and c is of type Rule,

	The value of type dict should be a Python dictionary whose keys are of type Variable
	and values are of type Term. It is a map from variables to terms.

	The function should return t_ obtained by applying substitution s to t.

	Please use Python dictionary to represent a subsititution map.
	'''
	def substitute_in_term (self, s : dict, t : Term) -> Term:
		x = []
		if isinstance(t, Function):
			for term in t.terms:
				if isinstance(term, Function):
					x.append(self.substitute_in_term(s,term))
					continue
				if term in s.keys():
					x.append(s[term])	
				else:
					x.append(term)	
		elif not(t in s):
			if isinstance(t,Variable):
				return Variable(t.value)
			elif isinstance(t,Atom):
				return Atom(t.value)
			else:
				return Number(t.value)
		elif isinstance(t,Rule):
			self.substitute_in_clause(s,t)
		elif isinstance(s[t],Variable):
			return Variable(s[t].value)
		elif isinstance(s[t],Number):
			return Number(s[t].value)
		elif isinstance(s[t],Atom):
			return Atom(s[t].value)
		return Function(t.relation,x)

	def substitute_in_clause (self, s : dict, c : Rule) -> Rule:
		temp = []
		Head = self.substitute_in_term(s,c.head)
		for term in c.body.terms:
			temp.append(self.substitute_in_term(s,term))
		return Rule(Head,RuleBody(temp))


	'''
	Problem 3
	unify (t1, t2) where t1 is of type term and t2 is of type Term.
	The function should return a substitution map of type dict,
	which is a unifier of the given terms. You may find the pseudocode
	of unify in the lecture note Control in Prolog useful.

	The function should raise the exception raise Not_unfifiable (),
	if the given terms are not unifiable.

	Please use Python dictionary to represent a subsititution map.
	'''
	
	def unify (self, t1: Term, t2: Term) -> dict:
		if t1 == t2 and not(isinstance(t1,Function)) and not(isinstance(t2,Function)): return {}
		if isinstance(t1,Variable):
			return {t1:t2}
		if isinstance(t2,Variable):
			return {t2:t1}
		if t1 != t2 and (not(isinstance(t1,Function)) or not(isinstance(t2,Function))): raise Not_unifiable
		if isinstance(t1,Function) and isinstance(t2,Function):
			if(not len(t1.terms) == len(t2.terms)):
				raise Not_unifiable
			if(not t1.relation == t2.relation): 
				raise Not_unifiable
			dic = {}
			for i in range(len(t1.terms)):
				temp1 = self.substitute_in_term(dic,t1.terms[i])
				temp2 = self.substitute_in_term(dic,t2.terms[i])
				temp3 = self.unify(temp1,temp2)
				for key in temp3:
					temp1 = key
					break
				for k, v in dic.items():
					if(k == temp1):
						del dic[k]
						dic[temp2] = v
					if(v == temp1):
						dic[k] = temp2
				dic = {**dic,**temp3}
			return dic
		else: raise Not_unifiable

	fresh_counter = 0
	def fresh(self) -> Variable:
		self.fresh_counter += 1
		return Variable("_G" + str(self.fresh_counter))
	def freshen(self, c: Rule) -> Rule:
		c_vars = self.variables_of_clause(c)
		theta = {}
		for c_var in c_vars:
			theta[c_var] = self.fresh()

		return self.substitute_in_clause(theta, c)


	'''
	Problem 4
	Following the Abstract interpreter pseudocode in the lecture note Control in Prolog to implement
	a nondeterministic Prolog interpreter.

	nondet_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of Terms (results), which is an instance of the original goal and is
	a logical consequence of the program. See the tests cases (in src/main.py) as examples.
	'''
	def nondet_query (self, program : List[Rule], pgoal : List[Term]) -> List[Term]:
		res = pgoal.copy()
		# for i in pgoal[0].terms:
		# 	print(i)
		# if(len(program) >= 2): print(program[1])
		x = random.randint(0,len(res)-1)
		counter = False
		map = {}
		while len(res) > 0:
			test2 = False
			if(counter):
				x = 0
			else:
				counter = True
			a = res[x]
			test = set()
			temp = {}
			checker1 = False
			if isinstance(a,Function):
				for i in range(len(a.terms)):
					if(i == len(a.terms)-1): break
					if(a.terms[i] == a.terms[i+1]): checker1 = True
					else: checker1 = False
			if(checker1): 
				res.remove(a)
				if(len(res) == 0): break
				else: continue
			while True:
				i = random.randint(0,len(program)-1)
				if len(test) == len(program): 
					test2 = True
					break
				if i in test: continue
				temp = (program[i])
				try:
					test = self.unify(a,temp.head)
					temp = self.freshen(program[i])
					test = self.unify(a,temp.head)
					map = {**map,**test}
					break
				except:
					test.add(i)
			if(test2): 
				res.remove(a)
				break
			if(len(temp.body.terms) == 0):
				res.remove(a)
			else:
				res.remove(a)
				for i in temp.body.terms:
					res.append(i)
			if(not len(res) == 0):
				for i in range(len(res)):
					res[i] = self.substitute_in_term(map,res[i])
			for i in range(len(pgoal)):
				pgoal[i] = self.substitute_in_term(map,pgoal[i])
			for i in range(len(pgoal)):
				pgoal[i] = self.substitute_in_term(map,pgoal[i])
			for i in range(len(pgoal)):
				pgoal[i] = self.substitute_in_term(map,pgoal[i])
			for i in range(len(pgoal)):
				pgoal[i] = self.substitute_in_term(map,pgoal[i])
		if(len(res) == 0):
			return pgoal
		else:
			self.nondet_query(program,pgoal)


	'''
	Challenge Problem

	det_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of term lists (results). Each of these results is
	an instance of the original goal and is a logical consequence of the program.
	If the given goal is not a logical consequence of the program, then the result
	is an empty list. See the test cases (in src/main.py) as examples.
	'''
	def det_query (self, program : List[Rule], pgoal : List[Term]) -> List[List[Term]]:
		def dfs(resolvent, goal, solutions):
			if len(resolvent) == 0:
				solutions.append(goal)
				return
			else:
				chosen_goal = resolvent.pop(0) 
				for rule in program: 
					try:
						self.unify(chosen_goal, rule.head)
					except: 
						continue
					rule = self.freshen(rule) 
					theta = self.unify(chosen_goal, rule.head) 
					new_resolvent, new_goal = resolvent.copy(), goal.copy() 
					for term in rule.body.terms:
						new_resolvent.append(term) 
					for i in range(0, len(new_resolvent)):
						new_resolvent[i] = self.substitute_in_term(theta, new_resolvent[i]) 
					for i in range(0, len(new_goal)):
						new_goal[i] = self.substitute_in_term(theta, new_goal[i]) 
					dfs(new_resolvent, new_goal, solutions)

		solutions = []
		dfs(pgoal.copy(), pgoal.copy(), solutions)
		return solutions	