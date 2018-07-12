from model import Formula, Variable
from typing import List, Tuple

def new_integer(cnf : Formula, bits : int) -> List[Variable]:
	return [cnf.new_var() for i in range(bits)]

def new_bitmap(cnf : Formula, width : int, height : int) -> List[List[Variable]]:
	return [[cnf.new_var() for i in range(width)] for j in range(height)]

def flatten(a : List[List[Variable]]) -> List[Variable]:
	return [item for sublist in a for item in sublist]

def pad(cnf : Formula, a : List[Variable], b : List[Variable]) -> Tuple[List[Variable], List[Variable]]:
	aa = a[:]
	bb = b[:]
	if len(aa) < len(bb):
		for i in range(len(aa), len(bb)):
			aa.append(cnf.const_false())
	elif len(bb) < len(aa):
		for i in range(len(bb), len(aa)):
			bb.append(cnf.const_false())

	assert(len(aa) == len(bb))

	return aa, bb
