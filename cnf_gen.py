#!/usr/bin/env python3
from typing import List, Tuple, IO
import subprocess

#todo:
# automatic padding during addition/multiplication
# find and restrict overflow from happening
# optimized squaring clauses/addition??
# modularization....? separate class for bitvectors encoding integers
# wouldn't it be cool if you can just do "a + b = c" and it just works

class CNFVariable:
	def __init__(self, val : int) -> None:
		self.__val = val #type: int

	#this sucks and makes no sense
	def __eq__(self, other : object) -> bool:
		if not isinstance(other, CNFVariable):
			return NotImplemented

		return abs(self.__val) == abs(other.__val)

	def __len__(self) -> int:
		if self.__val > 0:
			return 1
		else:
			return 0

	def __invert__(self) -> 'CNFVariable':
		return CNFVariable(-self.__val)

	def __str__(self) -> str:
		return str(self.__val)


class CNFFormula:
	def __init__(self) -> None:
		self.__maxvar = 1 #type: int
		self.__clauses = [] #type: List[List[CNFVariable]]

		self.__always_false = self.new_var()
		self.__always_true = self.new_var()

		self.add([~self.__always_false])
		self.add([self.__always_true])

	def new_var(self) -> CNFVariable:
		var = self.__maxvar
		self.__maxvar += 1
		return CNFVariable(var)

	def const_true(self) -> CNFVariable:
		return self.__always_true

	def const_false(self) -> CNFVariable:
		return self.__always_false

	def add(self, clause : List[CNFVariable]) -> None:
		self.__clauses.append(clause)

	def write(self, fd : IO[bytes]) -> None:
		fd.write(("p cnf %d %d\n" % (self.__maxvar - 1, len(self.__clauses))).encode('ascii'))
		for clause in self.__clauses:
			fd.write((" ".join(str(x) for x in clause) + " 0\n").encode('ascii'))


class SATSolver:
	def __init__(self, cnf : CNFFormula) -> None:
		self.__cnf = cnf
		self.__solver_invoked = False #type: bool
		self.__satisfiable = False #type: bool
		self.__solution = [] #type: List[CNFVariable]

	def solve(self) -> None:
		print("Invoking sat solver...")
		minisat = subprocess.Popen(["minisat", "/dev/stdin", "/dev/stderr"], stdin=subprocess.PIPE, stderr=subprocess.PIPE)

		self.__cnf.write(minisat.stdin)
		minisat.stdin.close()

		#output is like 'SAT\n1 -2 -3 4 5 0\n' or 'UNSAT\n'
		satisfiable = minisat.stderr.readline()[:-1].decode('ascii')
		self.__satisfiable = (satisfiable == "SAT")

		if self.__satisfiable:
			solution = minisat.stderr.readline()[:-1].decode('ascii')
			solution = solution.strip().split(" ")[:-1]

			for var in solution:
				self.__solution.append(CNFVariable(int(var)))

		self.__solver_invoked = True

	def satisfiable(self) -> bool:
		assert(self.__solver_invoked)
		return self.__satisfiable

	def varlist_to_int(self, varlist : List[CNFVariable]) -> int:
		assert(self.__solver_invoked)
		assert(self.__satisfiable)

		bitvector = [] #type: List[bool]

		for var in varlist:
			for solvar in self.__solution:
				if var == solvar:
					bitvector.append(bool(solvar))

					break

		assert(len(bitvector) == len(varlist))

		intval = 0 #type: int

		for i in range(len(bitvector)):
			if bitvector[i]:
				intval += pow(2, i)

		return intval

#code from https://blog.lse.epita.fr/articles/24-using-sat-and-smt-to-defeat-simple-hashing-algorit.html
def cnf_int(cnf : CNFFormula, bits : int) -> List[CNFVariable]:
	return [cnf.new_var() for i in range(bits)]

def cnf_constant(cnf : CNFFormula, n : List[CNFVariable], c : int) -> None:
	for i in range(len(n)):
		b = c & 1
		c >>= 1
		if b:
			cnf.add([n[i]])
		else:
			cnf.add([~n[i]])

	if c > 0:
		print("WARNING: overflow in cnf_constant!")

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

def cnf_padout(a : List[CNFVariable], b : List[CNFVariable]) -> Tuple[List[CNFVariable], List[CNFVariable]]:
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

def cnf_add(cnf : CNFFormula, a : List[CNFVariable], b : List[CNFVariable]) -> List[CNFVariable]:
	#if the lengths are incorrect, just pad up with zero variables
	a, b = cnf_padout(a, b)

	carry = cnf.const_false() # The first carry is always 0

	out = []
	for (ai, bi) in zip(a, b):
		res, carry = cnf_1bitadder(cnf, ai, bi, carry)
		out.append(res)
	out.append(carry)

	return out

#rest of this is my stuff
def cnf_1bitequal(cnf : CNFFormula, a : CNFVariable, b : CNFVariable) -> None:
	cnf.add([a, ~b])
	cnf.add([~a, b])

def cnf_equal(cnf : CNFFormula, a : List[CNFVariable], b : List[CNFVariable]) -> None:
	a, b = cnf_padout(a, b)

	for i in range(len(a)):
		cnf_1bitequal(cnf, a[i], b[i])

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

	for i in range(1, len(a)):
		out[i:] = cnf_add(cnf, out[i:], ppt[i][:])

	return out

def cnf_square(cnf : CNFFormula, a : List[CNFVariable]) -> List[CNFVariable]:
	return cnf_mult(cnf, a, a)

if __name__ == "__main__":
	cnf = CNFFormula()

	bitdepth = 8
	a = cnf_int(cnf, bitdepth)
	b = cnf_int(cnf, bitdepth)
	c = cnf_int(cnf, bitdepth)

	a2 = cnf_square(cnf, a)
	b2 = cnf_square(cnf, b)
	c2 = cnf_square(cnf, c)

	a2b2 = cnf_add(cnf, a2, b2)

	#ensure neither a nor b is 1, i.e. at least one bit other than the first is set
	cnf.add(a)
	cnf.add(b)
	cnf.add(c)

	# cnf_constant(cnf, a, 3)
	# cnf_constant(cnf, b, 4)
	cnf_equal(cnf, a2b2, c2)

	solver = SATSolver(cnf)
	solver.solve()
	print("satisfiable: " + str(solver.satisfiable()))

	if (solver.satisfiable()):
		aint = solver.varlist_to_int(a)
		bint = solver.varlist_to_int(b)
		cint = solver.varlist_to_int(c)
		# a2b2int = solver.varlist_to_int(a2b2)

		print("a: " + str(aint))
		print("b: " + str(bint))
		print("c: " + str(cint))

		assert(aint*aint + bint*bint == cint*cint)
