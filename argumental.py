import pyeda
from pysat.solvers import Solver
from pysat.formula import CNF 
from collections import defaultdict

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
		self.attackers_list = defaultdict(lambda: [])
		self.attacked_list = defaultdict(lambda: [])

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
			self.attacked_list[attacker] = [attacked] 
		else:
			self.attackers_list[attacked].append(attacker)
			self.attacked_list[attacker].append(attacked)

	def solution_for_print(self, solution):
		reversed_arg = dict()
		for key, val in self.arguments.items():
			reversed_arg[val] = key
		solution = [reversed_arg[i] for i in solution if i > 0]
		solution = str(solution)
		solution = solution.replace("'","")
		solution = solution.replace(" ","")
		return solution

	def conflict_free_sets_CNF(self):
		cnf = CNF()
		for (arg, attackers) in self.attackers_list.items():
			for att in attackers:
				cnf.append([-int(arg), -int(att)])
		return cnf

	def call_SAT_oracle_for_stable(self, cnf, problem, arg):
		solver = Solver(use_timer=True, name=SATBasedSolver.NAME, bootstrap_with=cnf.clauses)
		solved = solver.solve()
		if solved:
			if problem==SATBasedSolver.SOME_EXTENSION:
				model = solver.get_model()	
				solver.delete()
				return self.solution_for_print(model)
			else:
				for model in solver.enum_models():
					arg_in_extension = self.arguments[arg] in model
					if problem==SATBasedSolver.CREDULOUS and arg_in_extension:
						solver.delete()
						return "YES"
					elif problem==SATBasedSolver.SKEPTICAL and not arg_in_extension:
						solver.delete()
						return "NO" 
		else:
			solver.delete()
			return "NO"
		solver.delete()
		if problem==SATBasedSolver.SOME_EXTENSION:
			return "NO"
		elif problem==SATBasedSolver.CREDULOUS:
			return "NO"
		elif problem==SATBasedSolver.SKEPTICAL:
			return "YES"

	def call_SAT_oracle_for_complete(self, cnf, problem, arg):
		solver = Solver(use_timer=True, name=SATBasedSolver.NAME, bootstrap_with=cnf.clauses)
		solved = solver.solve()
		if solved:
			if problem==SATBasedSolver.SOME_EXTENSION:
				i=0
				from time import time
				t=time()
				for model in solver.enum_models():
					if self.contains_all_defended(model, i):
						#solver.delete()
						print("found one at", i, "after", time()-t)
						print(self.solution_for_print(model))
					i+=1
			else:
				for model in solver.enum_models():
					if self.contains_all_defended(model):
						arg_in_extension = self.arguments[arg] in model
						if problem==SATBasedSolver.CREDULOUS and arg_in_extension:
							solver.delete()
							return "YES"
						elif problem==SATBasedSolver.SKEPTICAL and not arg_in_extension:
							solver.delete()
							return "NO" 
		else:
			solver.delete()
			return "NO"
		solver.delete()
		if problem==SATBasedSolver.SOME_EXTENSION:
			return "NO"
		elif problem==SATBasedSolver.CREDULOUS:
			return "NO"
		elif problem==SATBasedSolver.SKEPTICAL:
			return "YES"

	def contains_all_defended(self, model, i=0):
		#print("############# ", i)
		in_model=defaultdict(lambda: 0)
		for arg in model:
			if arg > 0:
				in_model[arg]=1
		for argument in model:
			if argument < 0:
				continue
			for attacked in self.attacked_list[argument]:
				for defended in self.attacked_list[attacked]:
					# this insider is defending an outsider
					if not in_model[defended]:
						# but is that outsider attacked by another insider?
						attacked=False
						for att in self.attackers_list[defended]:
							# yes he is, then it's fine,
							# he deserve to be dead
							if in_model[att]:
								attacked=True
								break
						# no, he is not. Then, this is not a complete extension.
						if not attacked:
							return False 
		return True

	def _contains_all_defended(self, model, i=0):
		print("############# ", i)
		#print("checking for contains all defended:", model)
		in_model=defaultdict(lambda: 0)
		for arg in model:
			if arg > 0:
				in_model[arg]=1
		print("how many in model: ", len(in_model), "over", len(model))
		for arg in model:
			# We check dead arguments only, i.e. negated arguments, arguments outside of model. 
			# Basically we wanna check that each dead argument is undefended against
			# at least one of its attackers. That would justify its deadness. Otherwise
			# Otherwise this model is not describing a complete extension since one defended argument
			# is outside the model.
			if arg < 0:
				defended = False
				for attack, defenders in self.defenders_list[-arg].items():
					for defender in defenders:
						# if arg is defended against this attack
						# we continue checking for the other attacks it receives
						if in_model[defender]:
							defended = True
							break
					# if this argument IS NOT defended against the current attack
					# then it's fine that it is out of the model
					if not defended:
						break
				# if this argument IS defended by an argument in the model
				# then it should be in the model as well. This model is thus not a complete extension.
				# So we return False.
				if defended:
					return False
		# No argument outside of the model was defended
		# so we return False
		return True

	def build_defenders_list(self):
		self.defenders_list=dict()
		for arg in self.arguments.values():
			self.defenders_list[arg]=dict()
		for arg in self.attackers_list.keys():
			for att in self.attackers_list[arg]:
				self.defenders_list[arg][att]=[]
				if att in self.attackers_list:
					self.defenders_list[arg][att].extend(self.attackers_list[att])
		
	def complete_extensions(self, problem=False, arg=None):
		"""
		complete extensions	
		"""
		# Since our algorithm for solving stable extensions is faster
		# we take advantage of this fact.
		if problem == SATBasedSolver.SOME_EXTENSION \
			or problem == SATBasedSolver.SKEPTICAL:
			solution = self.stable_extensions(problem, arg)
			if problem == SATBasedSolver.SOME_EXTENSION and solution != "NO":
				return solution
			if problem == SATBasedSolver.SKEPTICAL and solution == "NO":
				return solution
		# Build the defense lists
		self.build_defenders_list()
		# Build the conflict freeness clauses
		cnf = self.conflict_free_sets_CNF()
		for argument in self.arguments.values():
			# Unattacked arguments must hold because they are defended
			# by the empty set
			if len(self.attackers_list[argument]) == 0:
				cnf.append([argument])
			else:
				# Each argument in the complete extension must be 
				# defended against each of its attackers
				for attacker in self.attackers_list[argument]:
					# argument holds implies that at least one of its defenders against THIS attacker holds
					clause=[-argument]+self.defenders_list[argument][attacker]
					cnf.append(clause)
					
		return self.call_SAT_oracle_for_complete(cnf, problem, arg)

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

		return self.call_SAT_oracle_for_stable(cnf, problem, arg)


