#!/usr/bin/env python3
from model import Variable, Formula
from solver import Solver
from encoding import new_integer
from typing import List, Tuple

#todo:
# experimenting with redundant binary representation for multiplication
# use a sat solver to find a repeating cnf circuit that does squaring???
# verify the validity of the pythtrip code by forcing the solver to enumerate over all bricks with/without it
# add some divisor constraints
# optimized squaring clauses/addition??
# modularization....? separate class for bitvectors encoding integers
# wouldn't it be cool if you can just do "a + b = c" and it just works

#code from https://blog.lse.epita.fr/articles/24-using-sat-and-smt-to-defeat-simple-hashing-algorit.html

def cnf_constant(cnf : Formula, n : List[Variable], c : int) -> None:
	for i in range(len(n)):
		b = c & 1
		c >>= 1
		if b:
			cnf.add([n[i]])
		else:
			cnf.add([~n[i]])

	if c > 0:
		print("WARNING: overflow in cnf_constant!")

def cnf_1bitadder(cnf : Formula, a : Variable, b : Variable, c : Variable) -> Tuple[Variable, Variable]:
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

def cnf_padout(a : List[Variable], b : List[Variable]) -> Tuple[List[Variable], List[Variable]]:
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

def cnf_add(cnf : Formula, a : List[Variable], b : List[Variable]) -> List[Variable]:
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
def cnf_1bitequal(cnf : Formula, a : Variable, b : Variable) -> None:
	cnf.add([a, ~b])
	cnf.add([~a, b])

def cnf_equal(cnf : Formula, a : List[Variable], b : List[Variable]) -> None:
	a, b = cnf_padout(a, b)
 
	for i in range(len(a)):
		cnf_1bitequal(cnf, a[i], b[i])

# creates a new var d st. (a ^ b) <=> d
def cnf_1bitmultiplier(cnf : Formula, a : Variable, b : Variable) -> Variable:
	#according to wolfie: CNF | (¬a ∨ ¬b ∨ d) ∧ (a ∨ ¬d) ∧ (b ∨ ¬d)
	d = cnf.new_var()

	cnf.add([~a, ~b, d])
	cnf.add([a, ~d])
	cnf.add([b, ~d])

	return d

def cnf_mult(cnf : Formula, a : List[Variable], b : List[Variable]) -> List[Variable]:
	a, b = cnf_padout(a, b)
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

def cnf_square(cnf : Formula, a : List[Variable]) -> List[Variable]:
	return cnf_mult(cnf, a, a)

#exactly one number is odd out of the three
def cnf_odd1(cnf : Formula, a : List[Variable], b : List[Variable], c : List[Variable]) -> None:
	x = a[0]
	y = c[0]
	z = b[0]

	cnf.add([x, y, z])
	cnf.add([~x, ~y])
	cnf.add([~x, ~z])
	cnf.add([~y, ~z])

def cnf_1div4(cnf : Formula, a : List[Variable]) -> None:
	cnf.add([~a[0]])
	cnf.add([~a[1]])

def cnf_1div16(cnf : Formula, a : List[Variable]) -> None:
	cnf.add([~a[0]])
	cnf.add([~a[1]])
	cnf.add([~a[2]])
	cnf.add([~a[3]])

#exactly two numbers are odd out of the three
def cnf_odd2(cnf : Formula, a : List[Variable], b : List[Variable], c : List[Variable]) -> None:
	x = a[0]
	y = c[0]
	z = b[0]

	cnf.add([~x, ~y, ~z])
	cnf.add([x, y])
	cnf.add([x, z])
	cnf.add([y, z])

#at least 2 divisible by 4
def cnf_div4(cnf : Formula, a : List[Variable], b : List[Variable], c : List[Variable]) -> None:

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

#use euclid's formula to impose even more structure to the pythagorean triples.
#will produce all primitive triples, which is good!
def cnf_enforce_pyth_trip(cnf : Formula, a : List[Variable], b : List[Variable], c : List[Variable], primitive : bool) -> None:
	assert(len(a) == len(b))
	assert(len(a) == len(c))

	bitdepth = len(a)

	m = new_integer(cnf, bitdepth)
	n = new_integer(cnf, bitdepth)

	m2 = cnf_square(cnf, m)
	n2 = cnf_square(cnf, n)

	m2n2 = cnf_add(cnf, m2, n2)

	two = [cnf.const_false(), cnf.const_true()]

	mn = cnf_mult(cnf, m, n)
	mn2 = cnf_mult(cnf, mn, two)

	# a disgusting way to do subtraction. fix me please
	m2subn2 = new_integer(cnf, bitdepth)
	m2_tmp = cnf_add(cnf, m2subn2, n2)
	cnf_equal(cnf, m2_tmp, m2)

	if not primitive:
		k = new_integer(cnf, bitdepth)
		m2subn2 = cnf_mult(cnf, m2subn2, k)
		mn2 = cnf_mult(cnf, mn2, k)
		m2n2 = cnf_mult(cnf, m2n2, k)

	cnf_equal(cnf, a, m2subn2)
	cnf_equal(cnf, b, mn2)
	cnf_equal(cnf, c, m2n2)

if __name__ == "__main__":
	cnf = Formula()

	bitdepth = 14
	a = new_integer(cnf, bitdepth)
	b = new_integer(cnf, bitdepth)
	c = new_integer(cnf, bitdepth)

	d = new_integer(cnf, bitdepth)
	e = new_integer(cnf, bitdepth)
	f = new_integer(cnf, bitdepth)

	g = new_integer(cnf, bitdepth)

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

	#ensure a, b, c != 0
	cnf.add(a)
	cnf.add(b)
	cnf.add(c)

	# add the system of equations
	cnf_equal(cnf, a2b2, d2)
	cnf_equal(cnf, a2c2, e2)
	cnf_equal(cnf, b2c2, f2)

	cnf_equal(cnf, a2b2c2, g2)

	#enforce euclid's formula on the triples
	cnf_enforce_pyth_trip(cnf, a, b, d, True)
	cnf_enforce_pyth_trip(cnf, a, c, e, False)
	cnf_enforce_pyth_trip(cnf, b, c, f, True)

	# cnf_enforce_pyth_trip(cnf, a, f, g, False)
	# cnf_enforce_pyth_trip(cnf, b, e, g, False)
	# cnf_enforce_pyth_trip(cnf, c, d, g, False)

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

	# with open("brick.cnf", "wb") as myfile:
	# 	cnf.write(myfile)

	solver = Solver(cnf)
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
