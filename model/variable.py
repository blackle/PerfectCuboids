class Variable:
	def __init__(self, val : int) -> None:
		self.__val = val #type: int

	def __int__(self) -> int:
		return abs(self.__val)

	#this sucks and makes no sense(?)
	def __eq__(self, other : object) -> bool:
		if not isinstance(other, Variable):
			return NotImplemented

		return abs(self.__val) == abs(other.__val)

	def __len__(self) -> int:
		if self.__val > 0:
			return 1
		else:
			return 0

	def __invert__(self) -> 'Variable':
		return Variable(-self.__val)

	def __str__(self) -> str:
		return str(self.__val)
