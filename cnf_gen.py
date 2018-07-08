#!/usr/bin/env python3
from typing import List, Tuple, IO
import subprocess

#todo:
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

#exactly one number is odd out of the three
def cnf_odd1(cnf : CNFFormula, a : List[CNFVariable], b : List[CNFVariable], c : List[CNFVariable]) -> None:
	x = a[0]
	y = c[0]
	z = b[0]

	cnf.add([x, y, z])
	cnf.add([~x, ~y])
	cnf.add([~x, ~z])
	cnf.add([~y, ~z])

def cnf_1div4(cnf : CNFFormula, a : List[CNFVariable]) -> None:
	cnf.add([~a[0]])
	cnf.add([~a[1]])

def cnf_1div16(cnf : CNFFormula, a : List[CNFVariable]) -> None:
	cnf.add([~a[0]])
	cnf.add([~a[1]])
	cnf.add([~a[2]])
	cnf.add([~a[3]])

#exactly two numbers are odd out of the three
def cnf_odd2(cnf : CNFFormula, a : List[CNFVariable], b : List[CNFVariable], c : List[CNFVariable]) -> None:
	x = a[0]
	y = c[0]
	z = b[0]

	cnf.add([~x, ~y, ~z])
	cnf.add([x, y])
	cnf.add([x, z])
	cnf.add([y, z])

#at least 2 divisible by 4
def cnf_div4(cnf : CNFFormula, a : List[CNFVariable], b : List[CNFVariable], c : List[CNFVariable]) -> None:

	x = a[0]
	y = a[1]

	z = b[0]
	w = b[1]

	p = c[0]
	q = c[1]

	cnf.add([~x, ~z])
	cnf.add([~x, ~w])
	cnf.add([~x, ~p])
	cnf.add([~x, ~q])
	cnf.add([~y, ~z])
	cnf.add([~y, ~w])
	cnf.add([~y, ~p])
	cnf.add([~y, ~q])
	cnf.add([~z, ~p])
	cnf.add([~z, ~q])
	cnf.add([~w, ~p])
	cnf.add([~w, ~q])

if __name__ == "__main__":
	cnf = CNFFormula()

	bitdepth = 13
	a = cnf_int(cnf, bitdepth)
	b = cnf_int(cnf, bitdepth)
	c = cnf_int(cnf, bitdepth)

	d = cnf_int(cnf, bitdepth)
	e = cnf_int(cnf, bitdepth)
	f = cnf_int(cnf, bitdepth)

	g = cnf_int(cnf, bitdepth)

	a2 = cnf_square(cnf, a)
	b2 = cnf_square(cnf, b)
	c2 = cnf_square(cnf, c)

	d2 = cnf_square(cnf, d)
	e2 = cnf_square(cnf, e)
	f2 = cnf_square(cnf, f)

	g2 = cnf_square(cnf, g)

	a2b2 = cnf_add(cnf, a2, b2)
	a2c2 = cnf_add(cnf, a2, c2)
	b2c2 = cnf_add(cnf, b2, c2)

	a2b2c2 = cnf_add(cnf, a2b2, c2)

	# add the system of equations
	cnf_equal(cnf, a2b2, d2)
	cnf_equal(cnf, a2c2, e2)
	cnf_equal(cnf, b2c2, f2)

	cnf_equal(cnf, a2b2c2, g2)

	#ensure a, b, c != 0
	cnf.add(a)
	cnf.add(b)
	cnf.add(c)

	#add conditions from the wiki article
	cnf.add([a[0]]) #force a to be the odd side
	cnf_1div4(cnf, b) #force b to be the side divisible by 4
	cnf_1div16(cnf, c) #force c to be the side divisible by 16

	#a odd and b divisible by 4 => d = 4k + 1 for some k
	cnf.add([d[0]])
	cnf.add([~d[1]])

	#a odd and c divisible by 16 => e = 4k + 1 for some k
	cnf.add([e[0]])
	cnf.add([~e[1]])

	#b divisible by 4 and c divisible by 16 => f = 16k for some k
	cnf_1div16(cnf, f)

	#given properties of a,b,c, => g = 4k + 1 for some k
	cnf.add([g[0]])
	cnf.add([~g[1]])

	solver = SATSolver(cnf)
	solver.solve()
	print("satisfiable: " + str(solver.satisfiable()))

	if (solver.satisfiable()):
		aint = solver.varlist_to_int(a)
		bint = solver.varlist_to_int(b)
		cint = solver.varlist_to_int(c)

		dint = solver.varlist_to_int(d)
		eint = solver.varlist_to_int(e)
		fint = solver.varlist_to_int(f)
		# a2b2int = solver.varlist_to_int(a2b2)

		print("a: " + str(aint))
		print("b: " + str(bint))
		print("c: " + str(cint))

		assert(aint*aint + bint*bint == dint*dint)
		assert(aint*aint + cint*cint == eint*eint)
		assert(bint*bint + cint*cint == fint*fint)
