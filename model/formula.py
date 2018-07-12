from model import Variable
from typing import List, IO

class Formula:
	def __init__(self) -> None:
		self.__maxvar = 1 #type: int
		self.__clauses = [] #type: List[List[Variable]]

		#create two variables that are always true and always false, for convenience
		self.__always_false = self.new_var()
		self.__always_true = self.new_var()

		self.add([~self.__always_false])
		self.add([self.__always_true])

	def new_var(self) -> Variable:
		var = self.__maxvar
		self.__maxvar += 1
		return Variable(var)

	def const_true(self) -> Variable:
		return self.__always_true

	def const_false(self) -> Variable:
		return self.__always_false

	def add(self, clause : List[Variable]) -> None:
		self.__clauses.append(clause)

	def write(self, fd : IO[bytes]) -> None:
		fd.write(("p cnf %d %d\n" % (self.__maxvar - 1, len(self.__clauses))).encode('ascii'))
		for clause in self.__clauses:
			fd.write((" ".join(str(x) for x in clause) + " 0\n").encode('ascii'))

