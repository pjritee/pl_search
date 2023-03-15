import pl_search as pls

# This is an implementation for the send more money puzzle using pl_search.
# This would almost certainly be easier in other constraint handling systems
# but is given to illustrate the approach.

# The puzzle is to choose distinct values for D,E,N,R,S,M,O,Y from
# 0,1,2,3,4,5,6,7,8,9 to make the following addition true.

#   SEND
# + MORE
# ------
#  MONEY

# One strategy is to use PuzzlePred below. In this approach
# we simply pick a variable, make a choice, test the choice and
# repeat until we find a solution.
# The other strategy is to use SmartPuzzlePred and that is
# perhaps more typical for constraint solving. After a variable is chosen
# and a choice made and checked we see what can be deduced (i.e. are there
# any other variables whose values are forced).
# In the second approach we are assuming that the time taken to do deductions
# is smaller than the time taken to make choices and backtrack over failed
# choices for those variables.
# For this program the Smart approach seems to be about 40 to 50 times faster
# than the simpler approach.

DIGITS0 = {0,1,2,3,4,5,6,7,8,9}
DIGITS = {1,2,3,4,5,6,7,8,9}
CARRY = {0,1,2}   # easy to deduce 2 is not needed

class PuzzleVar(pls.Var):
    def __init__(self, choices):
        super().__init__()
        self.choices = choices
        self.disjoints = []

    def set_disjoints(self, disj):
        self.disjoints = disj
    # Allow checking before binding
    # Note that the check is not needed when using PuzzleHander
    # as get_choices returns only valid choices
    # However, when using SmartPuzzleHandler, the deductions might
    # choose a value that's not valid. As an alternative we could
    # have tested if the choice was valid before binding. This
    # approach was chosen to illustrate the power of doing tests
    # inside bind. In another context we might bind one variable to another
    # and in that context the possible choices then become the intersection
    # of each variables choices. If that set was empty then the binding
    # should fail and if the set was a singleton then we could bind both
    # variables to that value (both deductions).
    def bind(self, val):
        if val not in self.choices or val in self.disjoints:
                return False
        super().bind(val)
        return True

    # As variables get bound to digits those digits are no longer
    # possible choices for other variables.
    def get_choices(self):
        known_disjoints = {pls.engine.dereference(n) for n in self.disjoints
                           if not pls.var(n)}
        return iter(self.choices.difference(known_disjoints))

# A predicate for trying alternative choices for an unbound variable.
class PuzzlePred(pls.Pred):
    def __init__(self, constraint_sums, all_vars):
        self.constraint_sums = constraint_sums
        self.all_vars = all_vars

    # This method is required and is used to initialize the predicate call
    # In this case we pick an unbound variable and determine the possible
    # choices for this variable. The attribute choice_iterator is used
    # by the system to backtrack over the possible choices and this attribute
    # needs to be given a value in this method for nondeterministic predicates.
    def initialize_call(self):
        v = get_best_var(self.all_vars)
        self.best_var = v
        self.choice_iterator = v.get_choices()
        return True

    # This method is also required and is called immediately after
    # initialize_call and each time the system backtracks to try an alternative
    # The argument to the method is the current choice pruduced by
    # next(self.choice_iterator). It return True iff the choice is a valid one.
    def try_choice(self, choice) -> bool:
        # As in Prolog implementations it's more typical to use unify
        # rather than bind directly as it's more general.
        return pls.engine.unify(self.best_var, choice) and self.test_choice()
   
    def test_choice(self):
        # Check if all the ground columns in the sum produce the correct result.
        for left, right in self.constraint_sums:
            if all(not pls.var(x) for x in left) and \
               all(not pls.var(x) for x in right):
                if sum(x.deref() for x in left) != \
                    right[0].deref() + 10*right[1].deref():
                     return False
        return True

def get_best_var(all_vars):
    # Simply find the next available variable.
    # We could have been more clever and, for example, picked the
    # variable with the smallest number of choices but that takes time
    # so it's a trade off.
    for v in all_vars:
        if pls.var(v):
            return v
    return None

def more_vars(all_vars):
    return any(pls.var(v) for v in all_vars)

# SmartPuzzlePred uses deductions as part of testing the choice.
class SmartPuzzlePred(PuzzlePred):
    def test_choice(self):
        progress = True
        # keep doing deductions until none are possible
        while progress:
            progress = False
            for left, right in self.constraint_sums:
                left = [pls.engine.dereference(x) for x in left]
                right = [pls.engine.dereference(x) for x in right]
                ground_left = [x for x in left if not pls.var(x)]
                ground_right = [x for x in right if not pls.var(x)]
                
                if len(left) == len(ground_left):
                    # above the line is ground and so we know
                    # what is below the line and the carry
                    top = sum(ground_left)
                    if any(pls.var(x) for x in right):
                        progress = True
                    c,d = divmod(top, 10)
                    if not pls.engine.unify(right[0], d) or \
                       not pls.engine.unify(right[1], c):
                        return False
                elif len(left) == len(ground_left)+1 and \
                     len(right) == len(ground_right):
                    # we know below the line and the carry are ground
                    # and all but one above the line are ground and
                    # so we can uniquely determine the remaining one
                    left_vars = [v for v in left if v not in right]
                    n = right[0] + 10*right[1] - sum(ground_left)
                    progress = True
                    if not pls.engine.unify(left_vars[0], n):
                        return False
        return True

# Used in the Loop predicate to generate a predicate
# to backtrack over choices for a given variable.
class PuzzleFactory(pls.LoopBodyFactory):

    def __init__(self, pred, constraint_sums, all_vars):
        self.pred = pred
        self.constraint_sums =  constraint_sums
        self.all_vars = all_vars

    # This method is required and is used to determine if the loop
    # predicate should continue.
    def loop_continues(self) -> bool:
        return more_vars(self.all_vars)

    # This method is required and is used to create a predicate
    # to be called as part of the loop body.
    def make_body_pred(self) -> pls.Pred:
        return self.pred(self.constraint_sums, self.all_vars)

# A predicate to print out the solution
class SuccessPrint(pls.DetPred):
    def initialize_call(self):
        print(f'   {S}{E}{N}{D}')
        print(f' + {M}{O}{R}{E}')
        print(' ------')
        print(f'  {M}{O}{N}{E}{Y}')

# Make the variables global so they can be easily printed inside SuccessPrint
S = PuzzleVar(DIGITS)
E = PuzzleVar(DIGITS0)
N = PuzzleVar(DIGITS0)
D = PuzzleVar(DIGITS0)
M = PuzzleVar({1,2})       # could deduce M = 1 (similar to carry)
O = PuzzleVar(DIGITS0)
R = PuzzleVar(DIGITS0)
Y = PuzzleVar(DIGITS0)


def solve():

    disjoint = [D,E,N,R,S,M,O,Y]

    for v in disjoint:
        v.set_disjoints(disjoint)
    
    C1 = PuzzleVar(CARRY)
    C2 = PuzzleVar(CARRY)
    C3 = PuzzleVar(CARRY) 
    
    # Encoding the problem in terms of each column in the sum
    # (including each carry)
    constraint_sums = [
        ([D,E], (Y,C1)),     # D + E == Y + 10*C1
        ([N,R,C1], (E,C2)),
        ([E,O,C2], (N, C3)),
        ([S,M,C3], (O, M))
        ]

    all_vars = disjoint + [C1,C2,C3]

    # Change commented line below to try alternative strategy
    factory = PuzzleFactory(SmartPuzzlePred, constraint_sums, all_vars)
    #factory = PuzzleFactory(PuzzlePred, constraint_sums, all_vars)
    
    pred = pls.conjunct([pls.Loop(factory), SuccessPrint()])
    result = pls.engine.execute(pred)

    
if __name__ == "__main__":
    solve()
