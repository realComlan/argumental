from pysat.solvers import Solver
from pysat.formula import CNF 

class SolverManager:
	instance = None
	help_string = """
	This is Argumental 1.0. Thanks for using it.	
	"""
	def __init__(self):
		self.problem = None
		self.argument = None
		self.solver = SATBasedSolver()
		self.parse_inputs()

	def parse_inputs(self):
		import sys
		argv = sys.argv[1:]
		try:
			i=0
			while i < len(argv):
				if argv[i] not in {'-p', '-f', '-a'}:
					print("param not recognized")
					return
				if argv[i] == '-p':
					problem = argv[i+1]
					self.set_problem(problem)
				elif argv[i] == '-f':
					filename = argv[i+1]
					self.get_framework_from_file(filename)
				elif argv[i] == '-a':
					argument = argv[i+1]
					self.set_argument(argument)
				i+=2
		except Exception as e:
			print(f"\x1b[41m {e}\033[00m")
			print(SolverManager.help_string)

	def get_framework_from_file(self, filename):
		import re
		with open(filename) as f:
			line = f.readline()
			while line:
				if line[:3] == 'arg':
					arg = re.search("\(.+\)", line).group(0)[1:-1]
					self.solver.add_argument(arg)
				elif line[:3] == 'att':
					args = re.search("\(.+\)", line).group(0)[1:-1].split(",")
					self.solver.add_attack((args[0],args[1]))
				line = f.readline()
	
	def set_problem(self, problem):
		self.problem = problem

	def set_argument(self, argument):
		self.argument = argument

	def get_instance():
		if not SolverManager.instance:
			SolverManager.instance = SolverManager()
		return SolverManager.instance
	
	def solve(self):
		print(self.solver.solve(self.problem, self.argument))


class SATBasedSolver:

	NAME="g4"
	SOME_EXTENSION="SE"
	CREDULOUS="DC"
	SKEPTICAL="DS"
	
	def __init__(self):
		self.arguments = dict()
		self.attackers_list = dict()
		self.cf_sets = None

	def solve(self, problem=None, arg=None):
		self.all_arguments_clause=list(self.arguments.values())
		if problem == "SE-CO":
			return self.complete_extensions(problem=SATBasedSolver.SOME_EXTENSION, arg=arg)
		elif problem == "DC-CO":
			return self.complete_extensions(problem=SATBasedSolver.CREDULOUS, arg=arg)
		elif problem == "DS-CO":
			return self.complete_extensions(problem=SATBasedSolver.SKEPTICAL, arg=arg)
		elif problem == "SE-ST":
			return self.stable_extensions(problem=SATBasedSolver.SOME_EXTENSION, arg=arg)
		elif problem == "DC-ST":
			return self.stable_extensions(problem=SATBasedSolver.CREDULOUS, arg=arg)
		elif problem == "DS-ST":
			return self.stable_extensions(problem=SATBasedSolver.SKEPTICAL, arg=arg)
		else:
			return "Unknown problem..."

	def add_argument(self, arg):
		if str(arg) not in self.arguments:
			self.arguments[str(arg)] = len(self.arguments)+1

	def add_attack(self, attack):
		attacker, attacked = self.arguments[attack[0]], self.arguments[attack[1]]
		if attacked not in self.attackers_list:
			self.attackers_list[attacked] = [attacker] 
		else:
			self.attackers_list[attacked].append(attacker)

	def solution_for_print(self, solution):
		reversed_arg = dict()
		for key, val in self.arguments.items():
			reversed_arg[val] = key
		solution = str([reversed_arg[i] for i in solution if i > 0])
		solution = solution.replace("'","")
		solution = solution.replace(" ","")
		return solution

	def conflict_free_sets_CNF(self):
		cnf = CNF()
		for (arg, attackers) in self.attackers_list.items():
			for att in attackers:
				cnf.append([-int(arg), -int(att)])
		return cnf

	def call_SAT_oracle(self, cnf, problem, arg):
		solver = Solver(name=SATBasedSolver.NAME, bootstrap_with=cnf.clauses)
		solved = solver.solve()
		if solved:
			if problem==SATBasedSolver.SOME_EXTENSION:
				return self.solution_for_print(solver.get_model())
			else:
				for model in solver.enum_models():
					arg_in_extension = self.arguments[arg] in model
					if problem==SATBasedSolver.CREDULOUS and arg_in_extension:
						return "YES"
					elif problem==SATBasedSolver.SKEPTICAL and not arg_in_extension:
						return "NO" 
		else:
			return "NO"
		solver.delete()
		if problem==SATBasedSolver.SOME_EXTENSION:
			return "NO"
		elif problem==SATBasedSolver.CREDULOUS:
			return "NO"
		elif problem==SATBasedSolver.SKEPTICAL:
			return "YES"

	def build_defenders_list(self):
		self.defenders_list=dict()
		for arg in self.arguments.values():
			self.defenders_list[arg]=[]
		for arg in self.attackers_list.keys():
			for att in self.attackers_list[arg]:
				if att in self.attackers_list:
					self.defenders_list[arg].extend(self.attackers_list[att])
		
	def complete_extensions(self, problem=False, arg=None):
		"""
		complete extensions	
		"""
		self.build_defenders_list()
		# Build the clauses
		cnf = self.conflict_free_sets_CNF()
		for argument in self.arguments.values():
			# In the complete semantics, each argument which is defended
			# must have the same truth value as all its defenders. They
			# must be all in the extension or all outside.
			for defender in self.defenders_list[argument]:
				cnf.append([-argument, defender])
				cnf.append([argument, -defender])
			# Unattacked arguments must hold because they are defended
			# by the empty set!
			if argument not in self.attackers_list:
				cnf.append([argument])
			# Arguments which are attacked but not defended
			# cannot hold.
			if argument in self.attackers_list and not len(self.defenders_list[argument]):
				cnf.append([-argument])

		return self.call_SAT_oracle(cnf, problem, arg)

	def stable_extensions(self, problem=False, arg=None):
		"""
		problem is SATBasedSolver.SOME_EXTENSION | SATBasedSolver.CREDULOUS | SATBasedSolver.SKEPTICAL
		arg is the argument of which we are checking acceptability
		"""
		# Build the clauses
		cnf = self.conflict_free_sets_CNF()
		for argument in self.arguments.values():
			# If a certain argument is not accepted then
			# one its attackers has been accepted.
			cl=[argument]
			if argument in self.attackers_list.keys():
				cl.extend(self.attackers_list[argument])
			cnf.append(cl)

		return self.call_SAT_oracle(cnf, problem, arg)


