import argumental

if __name__ == "__main__":
	solverManager = SolverManager.get_instance()
	solverManager.solve(method=Solver.SATBASED)
	solverManager.solve(method=Solver.MATRIXBASED)
