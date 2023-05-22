import pl_search as pls

# The complete code for the NxN magic square example as discussed in README
# Change the next line for a larger magic square
N = 3
N2 = N**2

# each row, column, diagonal sum
SUM = (N * (N2 + 1))//2

# The square to be filled in with the numbers 1,2,3,.. N**2
CHOICES = set(range(1,N2+1))

class MSVar(pls.Var):
    """The variables used to initialize the magic square.
    """
    
    def set_disjoint(self, disjoints):
        self.disjoints = disjoints

    def bind(self, n):
        """Check that n is a valid choice and if so bind to n"""
        if n in self.disjoints or n not in CHOICES:
            return False
        return super().bind(n)

    def get_choices(self):
        """Return a list containing the possible valid choices"""
        known_disjoints = {pls.dereference(n) for n in self.disjoints
                           if not pls.var(n)}
        return CHOICES.difference(known_disjoints)
    
class Print(pls.DetPred):
    """Pretty print the supplied array."""
    
    def __init__(self, array):
        self.array = array

    def initialize_call(self):
        for j in range(N):
            print(''.join(f'{str(pls.dereference(self.array[j][i])):>5}'
                           for i in range(N)))
        print()

def generate_constraints(square):
    """Return the row, column and diagonal sum constraints."""
    constraints = \
        [pls.UpdatableVar(([square[i][j] for i in range(N)], SUM))
         for j in range(N)] + \
        [pls.UpdatableVar(([square[j][i] for i in range(N)], SUM))
         for j in range(N)] + \
        [pls.UpdatableVar(([square[i][i] for i in range(N)], SUM))] + \
        [pls.UpdatableVar(([square[i][N-1-i] for i in range(N)], SUM))]
    return constraints

def check_constraints(constraints):
    """ check and simplify constraints.
    Return True iff constraints are satisfiable.
    """
    progress = True
    while progress:
        # keep repeating until no more 'useful' simplifications are possible
        progress = False        
        for c in constraints:
            lhs, rhs = c.value
            if lhs == [] and rhs == 0:
                # solved constraint
                continue
            var_lhs = [x for x in lhs if  pls.var(x)]
            ground_lhs = [pls.dereference(x) for x in lhs 
                          if not x in var_lhs]
            new_rhs = rhs - sum(ground_lhs)
            if var_lhs == []:
                if new_rhs == 0:
                    # newly solved constraint
                    pls.engine.unify(c, ([], 0))
                    continue
                return False
            if new_rhs < 0:
                # no solution is possible
                return False
            if len(var_lhs) == 1: # constraint is Var = new_rhs
                progress = True
                if not pls.engine.unify(var_lhs[0], new_rhs):
                    # this fails when new_rhs is too big
                    # or is already taken
                    return False
                # newly solved constraint
                pls.engine.unify(c, ([], 0))
            elif new_rhs != rhs:
                # the constraint is simplified
                progress = True
                pls.engine.unify(c, (var_lhs, new_rhs))
    return True

def get_best_var(all_vars):
    """Return the first remaining variable in all_vars else return None if
    there are no more variables."""
    for v in all_vars:
        if pls.var(v):
            return v
    return None
    
class BodyPred(pls.Pred):
    """This predicate is called in the body of Loop.
    """
    def __init__(self, constraints, all_vars, best_var):
        self.constraints = constraints
        self.all_vars = all_vars
        self.best_var = best_var

    def initialize_call(self):
        #required method and self.choice_iterator must be given a value
        self.choice_iterator = \
            pls.VarChoiceIterator(self.best_var, self.best_var.get_choices())
        return True

    def test_choice(self):
        # We need to check the constraints and carry out deductions so this 
        # method is required
        return check_constraints(self.constraints)
       
class MSFactory(pls.LoopBodyFactory):
    """The factory called by Loop."""
    
    def __init__(self, constraints, all_vars):
        self.constraints =  constraints
        self.all_vars = all_vars

    def loop_continues(self):
        self.best_var = get_best_var(self.all_vars)
        return self.best_var is not None

    def make_body_pred(self) -> pls.Pred:
        return BodyPred(self.constraints, self.all_vars, self.best_var)

def solve(): 
    all_vars = [MSVar() for _ in range(N2)]
    for v in all_vars:
        v.set_disjoint(all_vars)
    square = [all_vars[i:i+N] for i in range(0, N2, N)]
    constraints = generate_constraints(square)
    # first solution
    pls.engine.execute(pls.conjunct([pls.Loop(MSFactory(constraints, all_vars)), Print(square)]))
    
    #all solutions
    #pls.engine.execute(pls.conjunct([pls.Loop(MSFactory(constraints, all_vars)), Print(square), pls.fail]))


if __name__ == "__main__":
    solve()


    
