import pl_search as pls

#   SEND
# + MORE
# ------
#  MONEY

DIGITS0 = {0,1,2,3,4,5,6,7,8,9}
DIGITS = {1,2,3,4,5,6,7,8,9}
CARRY = {0,1,2}

class PuzzleVar(Var):
    def __init__(self, choices):
        super().__init__()
        self.choices = choices
        self.disjoint = []

    def set_disjoint(self, disjoint):
        self.disjoint = disjoint

    # allow checking before binding
    def bind(self, val):
        if val not in self.choices:
                return False
        super().bind(val)
        return True
         
    def get_choices(self):
        known_disjoints = {prolog.dereference(n) for n in self.disjoint
                           if not var(n)}
        return list(self.choices.difference(known_disjoints))

class PuzzleHandler(Handler):
    def __init__(self, args):
        self.constraint_sums, self.all_vars = args
        self.best_var = None
        self.choice_iter = iter([])
        
    def generate_choice(self) :
        v = self.get_best_var()
        if v is None:
            # no more steps - soln found
            return False
        self.best_var = v
        self.choice_iter = iter(v.get_choices())
        return True

    def make_choice(self):
        choice = next(self.choice_iter)
        return prolog.unify(self.best_var, choice) and self.test_choice()
   
    def test_choice(self):
        for left, right in self.constraint_sums:            
            if all(not var(x) for x in left) and \
               all(not var(x) for x in right):
                 if sum(x.deref() for x in left) != \
                    right[0].deref() + 10*right[1].deref():
                     return False
        return True

    def get_best_var(self):
        for v in self.all_vars:
            if var(v):
                return v
        return None
    

class SmartPuzzleHandler(PuzzleHandler):
    def test_choice(self):
        while True:
            progress = False
            for left, right in self.constraint_sums:
                left = [prolog.dereference(x) for x in left]
                right = [prolog.dereference(x) for x in right]
                ground_left = [x for x in left if not var(x)]
                ground_right = [x for x in right if not var(x)]
                
                if len(left) == len(ground_left):
                    # above the line is ground and so we know
                    # what is below the line and the carry
                    top = sum(left)
                    if any(var(x) for x in right):
                        progress = True
                    c,d = divmod(top, 10)
                    if not prolog.unify(right[0], d) or \
                       not prolog.unify(right[1], c):
                        return False
                elif len(left) == len(ground_left)+1 and \
                     len(right) == len(ground_right):
                    # we know below the line and the carry are ground
                    # and all but one above the line are ground and
                    # so we can uniquely determine the remaining one
                    left_vars = [v for v in left if v not in right]
                    n = right[0] + 10*right[1] - sum(ground_left)
                    progress = True
                    if not prolog.unify(left_vars[0], n):
                        return False
            if not progress:
                break
        return True

    
def solve():
    S = PuzzleVar(DIGITS)
    E = PuzzleVar(DIGITS0)
    N = PuzzleVar(DIGITS0)
    D = PuzzleVar(DIGITS0)
    M = PuzzleVar({1,2})
    O = PuzzleVar(DIGITS0)
    R = PuzzleVar(DIGITS0)
    Y = PuzzleVar(DIGITS0)
    C1 = PuzzleVar(CARRY)
    C2 = PuzzleVar(CARRY)
    C3 = PuzzleVar(CARRY) 
    disjoint = [D,E,N,R,S,M,O,Y]
    S.set_disjoint(disjoint)
    E.set_disjoint(disjoint)
    N.set_disjoint(disjoint)
    D.set_disjoint(disjoint)
    M.set_disjoint(disjoint)
    O.set_disjoint(disjoint)
    R.set_disjoint(disjoint)
    Y.set_disjoint(disjoint)

    constraint_sums = [
        ([D,E], (Y,C1)),     # D + E == Y + 10*C1
        ([N,R,C1], (E,C2)),
        ([E,O,C2], (N, C3)),
        ([S,M,C3], (O, M))
        ]

    all_vars = disjoint + [C1,C2,C3]
    result = prolog.execute(ChoicePred(SmartPuzzleHandler, (constraint_sums, all_vars), Success()))

    print(f'{result = }')
    if result:
        print(f'   {S}{E}{N}{D}')
        print(f' + {M}{O}{R}{E}')
        print(' ------')
        print(f'  {M}{O}{N}{E}{Y}')
    
