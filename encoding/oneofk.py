from model import Formula, Variable
from typing import List

def at_most_one(cnf, varlist : List[Variable]) -> None:
	for i in range(len(varlist)):
		for j in range(i+1, len(varlist)):
			cnf.add([~varlist[i], ~varlist[j]])

def at_least_one(cnf, varlist : List[Variable]) -> None:
	cnf.add(varlist)

def one_of_k_naive(cnf : Formula, varlist : List[Variable]) -> None:
	at_least_one(cnf, varlist)
	at_most_one(cnf, varlist)

def commander_variable(cnf : Formula, group : List[Variable]) -> Variable:
	at_most_one(cnf, group)

	var = cnf.new_var()

	# var <=> (a or b or c ...)
	for i in range(len(group)):
		cnf.add([~group[i], var])

	clause = group[:]
	clause.append(~var)
	cnf.add(clause)

	return var

def one_of_k_commander(cnf : Formula, varlist : List[Variable], group_size : int) -> None:
	at_least_one(cnf, varlist)

	length = len(varlist)
	if length == 1:
		cnf.add([varlist[0]])
		return
	assert(length % group_size == 0)

	treevars = [] #type: List[Variable]
	for i in range(int(length/group_size)):
		idx = group_size*i
		group = varlist[idx:idx+group_size]

		treevar = commander_variable(cnf, group)
		treevars.append(treevar)

	one_of_k_commander(cnf, treevars, group_size)
