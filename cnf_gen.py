#!/usr/bin/env python3
from typing import List, Tuple

#todo:
# automatic invocation of minisat
# extraction of integer values from sat solution
# automatic padding during addition/multiplication
# find and restrict overflow from happening
# optimized squaring clauses/addition??
# modularization....? separate class for bitvectors encoding integers
# wouldn't it be cool if you can just do "a + b = c" and it just works

class CNFVariable:
	def __init__(self, val : int) -> None:
		self.__val = val #type: int

	def __invert__(self) -> 'CNFVariable':
		return CNFVariable(-self.__val)

	def __str__(self) -> str:
		return str(self.__val)

class CNFFormula:
	def __init__(self) -> None:
		self.__maxvar = 1 #type: int
		self.__clauses = [] #type: List[List[CNFVariable]]

	def new_var(self) -> CNFVariable:
		var = self.__maxvar
		self.__maxvar += 1
		return CNFVariable(var)

	def add(self, clause : List[CNFVariable]) -> None:
		self.__clauses.append(clause)

	def output(self) -> None:
		print("p cnf %d %d" % (self.__maxvar - 1, len(self.__clauses)))
		for clause in self.__clauses:
			print(" ".join(str(x) for x in clause) + " 0")

class SATSolver:
	def __init__(self, )

#code from https://blog.lse.epita.fr/articles/24-using-sat-and-smt-to-defeat-simple-hashing-algorit.html
def cnf_int(cnf : CNFFormula, bits : int) -> List[CNFVariable]:
	return [cnf.new_var() for i in range(bits)]

def cnf_equal(cnf : CNFFormula, n : List[CNFVariable], c : int) -> None:
	for i in range(len(n)):
		b = c & 1
		c >>= 1
		if b:
			cnf.add([n[i]])
		else:
			cnf.add([~n[i]])

def cnf_1bitadder(cnf : CNFFormula, a : CNFVariable, b : CNFVariable, c : CNFVariable) -> Tuple[CNFVariable, CNFVariable]:
	res = cnf.new_var()
	res_carry = cnf.new_var()

	# (d|a|~b|~c)&(d|~a|b|~c)&(d|~a|~b|c)&(d|~a|~b|~c)&(~d|a|b|c)&(~d|a|b|~c)&(~d|a|~b|c)&(~d|~a|b|c)
	cnf.add([res_carry, a, ~b, ~c])
	cnf.add([res_carry, ~a, b, ~c])
	cnf.add([res_carry, ~a, ~b, c])
	cnf.add([res_carry, ~a, ~b, ~c])
	cnf.add([~res_carry, a, b, c])
	cnf.add([~res_carry, a, b, ~c])
	cnf.add([~res_carry, a, ~b, c])
	cnf.add([~res_carry, ~a, b, c])

	# (d|a|b|~c)&(d|a|~b|c)&(d|~a|b|c)&(d|~a|~b|~c)&(~d|a|b|c)&(~d|a|~b|~c)&(~d|~a|b|~c)&(~d|~a|~b|c)
	cnf.add([res, a, b, ~c])
	cnf.add([res, a, ~b, c])
	cnf.add([res, ~a, b, c])
	cnf.add([res, ~a, ~b, ~c])
	cnf.add([~res, a, b, c])
	cnf.add([~res, a, ~b, ~c])
	cnf.add([~res, ~a, b, ~c])
	cnf.add([~res, ~a, ~b, c])

	return res, res_carry

def cnf_add(cnf : CNFFormula, a : List[CNFVariable], b : List[CNFVariable]) -> List[CNFVariable]:
	assert(len(a) == len(b))

	carry = cnf.new_var()
	cnf.add([~carry]) # The first carry is always 0

	out = []
	for (ai, bi) in zip(a, b):
		res, carry = cnf_1bitadder(cnf, ai, bi, carry)
		out.append(res)
	out.append(carry)

	return out

#rest of this is my stuff

# creates a new var d st. (a ^ b) <=> d
def cnf_1bitmultiplier(cnf : CNFFormula, a : CNFVariable, b : CNFVariable) -> CNFVariable:
	#according to wolfie: CNF | (¬a ∨ ¬b ∨ d) ∧ (a ∨ ¬d) ∧ (b ∨ ¬d)
	d = cnf.new_var()

	cnf.add([~a, ~b, d])
	cnf.add([a, ~d])
	cnf.add([b, ~d])

	return d

def cnf_mult(cnf : CNFFormula, a : List[CNFVariable], b : List[CNFVariable]) -> List[CNFVariable]:
	assert(len(a) == len(b))
	#partial product table
	ppt = []
	for i in range(len(a)):
		pptrow = []
		for j in range(len(b)):
			d = cnf_1bitmultiplier(cnf, a[i], b[j])
			pptrow.append(d)
		ppt.append(pptrow)

	out = ppt[0][:]
	#add a silly little padding variable so we can do the adding loop
	dumbo = cnf.new_var()
	cnf.add([~dumbo])
	out.append(dumbo)

	for i in range(1, len(a)):
		# print(i)
		# print(out)
		out[i:] = cnf_add(cnf, out[i:], ppt[i][:])
		# print(out)

	return out

if __name__ == "__main__":
	cnf = CNFFormula()

	bitdepth = 32
	a = cnf_int(cnf, bitdepth)
	b = cnf_int(cnf, bitdepth)
	# c = cnf_int(cnf, bitdepth)

	a2 = cnf_mult(cnf, a, a)
	b2 = cnf_mult(cnf, b, b)
	# c2 = cnf_mult(cnf, c, c)

	a2b2 = cnf_add(cnf, a2, b2)
	# a2b2c2 = cnf_add(cnf, a2b2, c2)

	cnf.add(a)
	cnf.add(b)
	# cnf.add(c)

	# cnf_equal(cnf, a, 0b0111)
	# cnf_equal(cnf, b, 0b0111)
	cnf_equal(cnf, a2b2, 0b11111010001011111111010100000010)

	print("c a = " + " ".join(str(x) for x in a))
	print("c b = " + " ".join(str(x) for x in b))
	# print("c c = " + " ".join(str(x) for x in c))

	cnf.output()