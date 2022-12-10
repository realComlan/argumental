import numpy as np
import pysat 

class SolverManager:
	
	def __init__(self):
		pass
class Solver:
	pass

class MatrixSolver(Solver):

	def __init__(self):
		self.arguments = dict()
		self.attacks = np.array()

	def add_argument(self, arg):
		if str(arg) not in self.arguments:
			self.arguments[str(arg)] = len(self.arguments)

	def add_attack(self, a, b):
		self.attacks = np.append(self.attacks, (a,b))

	def prepare_attack_matrix(self):
		n=len(self.arguments)
		self.attack_matrix=np.zeros(n,n)
	
	def conflict_free_sets(self):
		result=np.array()
		n=len(self.arguments)
		N=1<<(n-1)
		for i in range(N):
			ss=np.array()
			for j in range(n):
				if i&(1<<j):
					ss=np.append(ss,[j])
			result=np.append(result,[j])

	def characteristic_function(self):
		pass

class SATBasedSolver(Solver):
	
	def __init__(self):
		pass

	def solve(self):
		pass





