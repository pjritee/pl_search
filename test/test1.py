# Testing aspects of pl_search

import pl_search as pls
import subprocess
import contextlib
from io import StringIO
import sys
import itertools
from typing import  Any


class FailPrint(pls.Pred):
    def __init__(self, vs):
        super().__init__()
        self.vs = vs
        
    def call(self) -> bool:
        # print suppied term
        print(f'{self.vs}')
        return False
        



class Print(pls.Pred):
    def __init__(self, varlst):
        super().__init__()
        self.varlst = varlst

    def call(self) -> bool:
        print(f'{self.varlst}')
        return self.call_continuation()

    def __repr__(self):
        return f'Print({self.varlst}) : {self.continuation}'

class LoopBodyPred(pls.VarChoicePred):
    def __init__(self, pred_vars):
        # In this example var and choices are not passed in to the constructor they are
        # determined in __init__
        self.continuation = None
        self.choices = [1,2]
        self.len_choices = 2
        self.index = 0
        for v in pred_vars:
            if pls.var(v):
                self.var = v
                break
        
    def __repr__(self):
        return f'LoopTest {self.continuation = }'
            
class LoopFactory(pls.LoopBodyFactory):

    def __init__(self, vars_):
        self.vars_ = vars_

    def loop_continues(self, _):
        # There are still variables for which choices need to be made
        return any(pls.var(x) for x in self.vars_)

    def make_body_pred(self, _):
        return LoopBodyPred(self.vars_)

v1 = pls.Var()
v2 = pls.Var()
v3 = pls.Var()


class SetChoicePred(pls.ChoicePred):
    def __init__(self, vars_list:list[pls.Var], choices:list[Any]):
        super().__init__()
        self.choices = [list(c) for c in itertools.combinations(choices, len(vars_list))]
        self.vars_list = vars_list
        self.index = 0
        
    def call_init(self):
        self.index = 0

    def has_next(self) -> bool:
        return self.index < len(self.choices)
    
    def make_choice(self) -> bool:
        choice = self.choices[self.index]
        self.index += 1
        return pls.unify(self.vars_list, choice)
    

        
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
SetChoicePred Test
[1, 2]
[1, 3]
[1, 4]
[2, 3]
[2, 4]
[3, 4]
NotNot Test
['after VarChoicePred call', 1]
['at end of call', X01]
"""

def run_tests():
    print("All solutions using FailPrint")
    pls.conjunct([
        pls.VarChoicePred(v1, [1,2]),
        pls.VarChoicePred(v2, ['a','b']),
        FailPrint([v1,v2])]).call()
    pls.trail.unbind_to(0)

    print("All solutions using Print and Fail")
    pls.conjunct([
        pls.VarChoicePred(v1, [1,2]),
        pls.VarChoicePred(v2, ['a','b']),
        Print([v1,v2]),
        pls.fail]).call()
    pls.trail.unbind_to(0)

    print("First Solution")
    pls.conjunct([
        pls.VarChoicePred(v1, [1,2]),
        pls.VarChoicePred(v2, ['a','b']),
        Print([v1,v2])]).call()
    pls.trail.unbind_to(0)

    print("Loop Test")
    body_factory = LoopFactory([v1,v2])
    pls.conjunct([
        pls.Loop(body_factory),
        Print([v1,v2]),
        pls.fail]).call()
    pls.trail.unbind_to(0)


    print("Once Test Without Once")
    pls.conjunct([
        pls.VarChoicePred(v1, [1,2]),
        pls.VarChoicePred(v2, [1,2]),
        pls.VarChoicePred(v3, [1,2]),
        FailPrint([v1,v2,v3])]).call()
    pls.trail.unbind_to(0)

    print("Once Test")
    pls.conjunct([
        pls.VarChoicePred(v1, [1,2]),
        pls.conjunct([
            pls.Once(pls.VarChoicePred(v2, [1,2])),
            Print(['after once'])]),
        pls.VarChoicePred(v3, [1,2]),
        FailPrint([v1,v2,v3])]).call()
    pls.trail.unbind_to(0)

    print("Disjunction Test")
    pls.conjunct([
        pls.DisjPred([
            pls.conjunct([
                pls.VarChoicePred(v1, [1,2]), 
                Print(["first choice", v1])]),
            pls.VarChoicePred(v1, ['a', 'b'])]),
        pls.Once(pls.VarChoicePred(v2, [1,2])),
        Print([v1,v2]),
        pls.fail]).call()
    pls.trail.unbind_to(0)

    print("Deterministic Predicate Test")
    pls.conjunct([
        pls.VarChoicePred(v1, [1,2]),
        pls.VarChoicePred(v2, [1,2]),
        Print(['v1', v1]),
        Print(['v2', v2]),
        pls.VarChoicePred(v3, ['a','b']),
        Print(['v3',v3]),
        pls.fail]).call()
    pls.trail.unbind_to(0)

    print("SetChoicePred Test")
    pls.conjunct([
        SetChoicePred([v1,v2], [1,2,3,4]),
        Print([v1,v2]),
        pls.fail]).call()
    pls.trail.unbind_to(0)

    print("NotNot Test")
    pls.conjunct([
        pls.NotNot(pls.conjunct([
            pls.VarChoicePred(v1, [1,2]),
            Print(["after VarChoicePred call", v1])])),
        Print(['at end of call', v1])]).call()
    pls.trail.unbind_to(0)


    

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
