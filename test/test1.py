# Testing aspects of pl_search

import pl_search as pls
import subprocess
import contextlib
from io import StringIO
import sys
import itertools

class FailPrint(pls.Pred):
    def __init__(self, vs):
        self.vs = vs
        
    def initialize_call(self):
        # print suppied term
        print(f'{self.vs}')
        # making the iterator empty causes this predicate to fail
        # when called
        self.choice_iterator = iter([])
        


# The same as the Prolog predicate member - it can be used in the same way
# as well i.e. both as a way of backtracking over the elements of the list
# and , less commonly, testing membership (like in)
class Member(pls.Pred):
    def __init__(self, v, choices):
        self.v = v
        self.choices = choices

    def initialize_call(self):
        self.choice_iterator = pls.VarChoiceIterator(self.v, self.choices)


class Print(pls.DetPred):
    def __init__(self, varlst):
        self.varlst = varlst

    def initialize_call(self):
        print(f'{self.varlst}')

    def __repr__(self):
        return f'Print({self.varlst}) : {self.continuation}'

class LoopBodyPred(pls.Pred):
    def __init__(self, pred_vars):
        self.pred_vars = pred_vars

    def initialize_call(self):
        for v in self.pred_vars:
            if pls.var(v):
                self.v = v
                break
        # The possible choices are 1,2
        self.choice_iterator = pls.VarChoiceIterator(v, [1,2])
        
    def __repr__(self):
        return f'LoopTest {self.continuation = }'
            
class LoopFactory(pls.LoopBodyFactory):

    def __init__(self, vars_):
        self.vars_ = vars_

    def loop_continues(self):
        return any(pls.var(x) for x in self.vars_)

    def make_body_pred(self):
        return LoopBodyPred(self.vars_)

v1 = pls.Var()
v2 = pls.Var()
v3 = pls.Var()


class SetChoiceIterator:

    def __init__(self, vars_, choices):
        self.vars_ = vars_
        n = len(vars_)
        self.choices = itertools.combinations(choices, n)

    def __iter__(self):
        return self

    def __next__(self):
        return pls.VarChoice(self.vars_, list(next(self.choices)))

class SetChoicePred(pls.Pred):
    def __init__(self, vars_, choices):
        self.vars_ = vars_
        self.choices = choices

    def initialize_call(self):
        self.choice_iterator = SetChoiceIterator(self.vars_, self.choices)


class TestExecute(pls.Pred):
    def __init__(self, v, choices, allowed, unbind = True):
        self.v = v
        self.choices = choices
        self.allowed = allowed
        self.unbind = unbind
        
    def initialize_call(self):
        self.choice_iterator = pls.VarChoiceIterator(self.v, self.choices)

    def test_choice(self):
        result = pls.engine.execute(Member(self.v, self.allowed), self.unbind)
        return result


        
EXPECTED_OUTPUT = """All solutions using FailPrint
[1, a]
[1, b]
[2, a]
[2, b]
All solutions using Print and Fail
[1, a]
[1, b]
[2, a]
[2, b]
First Solution
[1, a]
Loop Test
[1, 1]
[1, 2]
[2, 1]
[2, 2]
Once Test Without Once
[1, 1, 1]
[1, 1, 2]
[1, 2, 1]
[1, 2, 2]
[2, 1, 1]
[2, 1, 2]
[2, 2, 1]
[2, 2, 2]
Once Test
['after once']
[1, 1, 1]
[1, 1, 2]
['after once']
[2, 1, 1]
[2, 1, 2]
Disjunction Test
['first choice', 1]
[1, 1]
['first choice', 2]
[2, 1]
[a, 1]
[b, 1]
Deterministic Predicate Test
['v1', 1]
['v2', 1]
['v3', a]
['v3', b]
['v1', 1]
['v2', 2]
['v3', a]
['v3', b]
['v1', 2]
['v2', 1]
['v3', a]
['v3', b]
['v1', 2]
['v2', 2]
['v3', a]
['v3', b]
SetChoiceIterator Test
[1, 2]
[1, 3]
[1, 4]
[2, 3]
[2, 4]
[3, 4]
NotNot Test
['after member call', 1]
['at end of call', X01]
Inner Execute Test with Unbind
[3]
After Inner Execute Test with Unbind v1 = X01
Inner Execute Test without Unbind
[3]
After Inner Execute Test without Unbind v1 = 3
"""

def run_tests():
    print("All solutions using FailPrint")
    pls.engine.execute(pls.conjunct([Member(v1, [1,2]),
                                     Member(v2, ['a','b']),
                                     FailPrint([v1,v2])]))
    
    print("All solutions using Print and Fail")
    pls.engine.execute(pls.conjunct([Member(v1, [1,2]),
                                     Member(v2, ['a','b']),
                                     Print([v1,v2]),
                                     pls.fail]))
    
    print("First Solution")
    pls.engine.execute(pls.conjunct([Member(v1, [1,2]),
                                     Member(v2, ['a','b']),
                                     Print([v1,v2])]))

    print("Loop Test")
    body_factory = LoopFactory([v1,v2])
    pred = pls.conjunct([pls.Loop(body_factory),
                         Print([v1,v2]),
                         pls.fail])
    pls.engine.execute(pred)

    print("Once Test Without Once")
    pls.engine.execute(pls.conjunct([Member(v1, [1,2]),
                                     Member(v2, [1,2]),
                                     Member(v3, [1,2]),
                                     FailPrint([v1,v2,v3])]))
    print("Once Test")
    pls.engine.execute(pls.conjunct([Member(v1, [1,2]),
                                     pls.conjunct([
                                         pls.Once(Member(v2, [1,2])),
                                         Print(['after once'])]),
                                     Member(v3, [1,2]),
                                     FailPrint([v1,v2,v3])]))

    print("Disjunction Test")
    pls.engine.execute(pls.conjunct([pls.Disjunction(
        [pls.conjunct([Member(v1, [1,2]), Print(["first choice", v1])]),
         Member(v1, ['a', 'b'])]),
                                     pls.Once(Member(v2, [1,2])),
                                     Print([v1,v2]),
                                     pls.fail]))
    print("Deterministic Predicate Test")
    pls.engine.execute(pls.conjunct([Member(v1, [1,2]),
                                     Member(v2, [1,2]),
                                     Print(['v1', v1]),
                                     Print(['v2', v2]),
                                     Member(v3, ['a','b']),
                                     Print(['v3',v3]),
                                     pls.fail]))
    print("SetChoiceIterator Test")
    pls.engine.execute(pls.conjunct([SetChoicePred([v1,v2], [1,2,3,4]),
                                     Print([v1,v2]),
                                     pls.fail]))
    print("NotNot Test")
    pls.engine.execute(pls.conjunct(
        [pls.NotNot(pls.conjunct([Member(v1, [1,2]),
                                  Print(["after member call", v1])])),
         Print(['at end of call', v1])]))

    print("Inner Execute Test with Unbind")
    pls.engine.execute(pls.conjunct([TestExecute(v1, [1,2,3,4], [3]),
                                     Print([v1])]))
    print(f'After Inner Execute Test with Unbind {v1 = }')
    
    print("Inner Execute Test without Unbind")
    pls.engine.execute(pls.conjunct([TestExecute(v1, [1,2,3,4], [3]),
                                     Print([v1])]), False)
    print(f'After Inner Execute Test without Unbind {v1 = }')
    
    

def test():
    test_stdout = StringIO()
    with contextlib.redirect_stdout(test_stdout):
        run_tests()
    output = test_stdout.getvalue().strip()
    print("------- TEST OUTPUT ------")
    print(output)
    if output == EXPECTED_OUTPUT.strip():
        print("------- TESTS SUCCEEDED ------")
    else:
        print("------- TESTS FAILED ------")
    
if __name__ == "__main__":
    test()
