from model import Formula, Variable
from typing import List

#make this more compact and efficient buckawoo
def one_of_k(cnf : Formula, varlist : List[Variable]) -> None:
	#at least one
	cnf.add(varlist)

	#at most one
	for i in range(len(varlist)):
		for j in range(i+1, len(varlist)):
			cnf.add([~varlist[i], ~varlist[j]])
