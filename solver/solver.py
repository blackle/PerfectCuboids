from model import Variable, Formula
from typing import List
import subprocess

class Solver:
	def __init__(self, cnf : Formula) -> None:
		self.__cnf = cnf
		self.__solver_invoked = False #type: bool
		self.__satisfiable = False #type: bool
		self.__solution = [] #type: List[Variable]

	def solve(self) -> None:
		minisat = subprocess.Popen(["manysat", "-ncores=8", "-rnd-init", "/dev/stdin", "/dev/stderr"], stdin=subprocess.PIPE, stderr=subprocess.PIPE, stdout=subprocess.PIPE)

		self.__cnf.write(minisat.stdin)
		minisat.stdin.close()

		#output is like 'SAT\n1 -2 -3 4 5 0\n' or 'UNSAT\n'
		satisfiable = minisat.stderr.readline()[:-1].decode('ascii')
		self.__satisfiable = (satisfiable == "SAT")

		if self.__satisfiable:
			solution = minisat.stderr.readline()[:-1].decode('ascii')
			solution = solution.strip().split(" ")[:-1]

			for var in solution:
				self.__solution.append(Variable(int(var)))

		self.__solver_invoked = True

	def satisfiable(self) -> bool:
		assert(self.__solver_invoked)
		return self.__satisfiable

	def solution(self) -> List[Variable]:
		assert(self.__solver_invoked)
		assert(self.__satisfiable)
		return self.__solution

	def varlist_to_int(self, varlist : List[Variable]) -> int:
		assert(self.__solver_invoked)
		assert(self.__satisfiable)

		intval = 0 #type: int

		for i in range(len(varlist)):
			solvar = self.__solution[int(varlist[i])-1]
			assert(solvar == varlist[i])
			if solvar:
				intval += pow(2, i)

		return intval