from model import Variable, Formula
from solver import Solver
from encoding import new_bitmap, flatten, one_of_k_commander
from typing import List, Tuple

def knight_movement(cnf : Formula, timeboard : List[List[List[Variable]]], t : int, tnew : int, x : int, y : int) -> None:
	bt = len(timeboard)
	bx = len(timeboard[0])
	by = len(timeboard[0][0])

	if tnew >= bt or tnew < 0:
		return

	#too lazy to generate this programatically...
	nw = (x+2, y-1)
	ne = (x+2, y+1)
	en = (x-1, y+2)
	es = (x+1, y+2)
	sw = (x-2, y-1)
	se = (x-2, y+1)
	wn = (x-1, y-2)
	ws = (x+1, y-2)

	varlist = [] #type: List[Variable]
	for pos in [nw, ne, en, es, sw, se, wn, ws]:
		if pos[0] < 0 or pos[0] >= bx:
			continue

		if pos[1] < 0 or pos[1] >= by:
			continue

		varlist.append(timeboard[tnew][pos[0]][pos[1]])

	if len(varlist) == 0:
		return

	varlist.append(~timeboard[t][x][y])

	cnf.add(varlist)

if __name__ == "__main__":
	cnf = Formula()

	board_size = 8
	tour_len = board_size*board_size

	#make an instance of the board for each moment in the tour
	timeboard = [new_bitmap(cnf, board_size, board_size) for i in range(tour_len)]

	#ensure the knight is in exactly one place at any moment in time
	for board in timeboard:
		one_of_k_commander(cnf, flatten(board), 4)

	#ensure the knight doesn't visit the same spot multiple times
	for i in range(board_size):
		for j in range(board_size):
			one_of_k_commander(cnf, [timeboard[t][i][j] for t in range(tour_len)], 8)

	#ensure knight movement is correct for each spot
	for t in range(tour_len):
		for x in range(board_size):
			for y in range(board_size):
				knight_movement(cnf, timeboard, t, t+1, x, y)
				knight_movement(cnf, timeboard, t, t-1, x, y)

	#start us in the top left corner
	cnf.add([timeboard[0][0][0]])
	#end us there too
	# cnf.add([timeboard[-1][1][2], timeboard[-1][2][1]])

	solver = Solver(cnf)
	solver.solve()

	# with open("tour.cnf", "wb") as myfile:
	# 	cnf.write(myfile)

	while solver.satisfiable():
		for x in range(board_size):
			for y in range(board_size):
				tpos = 0
				for t in range(tour_len):
					spaceint = solver.varlist_to_int([timeboard[t][x][y]])
					if spaceint == 1:
						tpos = t
						break
				print(str(tpos).ljust(3), end='')
						
			print("")
		print("")

		cnf.add([~var for var in solver.solution()])
		break

		solver = Solver(cnf)
		solver.solve()
