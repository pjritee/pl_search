####################################
# The MIT License (MIT)
#
# Copyright (c) 2023 Peter Robinson
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:

# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
####################################

"""
This module provides reasonably generic search/constraint solving
capabilities using Prolog ideas. It does not even come close to an 
implementation of Prolog - it simply uses ideas from Prolog like variables 
and backtrack search implemented using a simplified trail and 
environment stack.

For a given application the programmer typically defines one or more 
subclasses of Pred, SemiDetPred or DetPred for carrying out the search. 
The search is then executed by calling engine.execute on a conjunction of 
predicates typically ending in a predicate that prints a solution. If all 
solutions are required then the predicate that prints a solution can be 
followed by the builtin predicate 'fail' that triggers backtracking.

An example of using this module is given in examples/send_more_money.py
that covers a significant portion of the use of the module. Further 
simple examples can be found in test/test1.py.

Below is a description of how some approaches for solving search problems
in Prolog are translated into Python using this module.

The first approach in Prolog follows the pattern:

    solve(State), print_answer(State).

where solve is completely implemented in Prolog. Calling this query (a pair
of predicate calls) would use backtracking search to attempt to find, 
and print a solution.

Using this module the programmer would need to set up a Python equivalent of
State using Var objects for the unknowns and then defining a Pred class
where initialize_call initialises the predicate typically by defining a
choice iterator and, when needed, test_choice to determine if the choice is 
valid and to possibly carry out deductions.

The choice iterator needs to generate Choice objects that contain the
apply_choice method that applies the choice. The simplest choice iterator is 
the builtin VarChoiceIterator that generates VarChoice objects whose 
apply_choice method simply unifies the variable with the choice as in the 
following Member predicate (that is like the Prolog member predicate).

class Member(pls.Pred):
    def __init__(self, v, choices):
        self.v = v
        self.choices = choices

    def initialize_call(self):
        self.choice_iterator = pls.VarChoiceIterator(self.v, self.choices)


The management of calling predicates and backtracking is done in Engine.

The programmer will typically inherit from DetPred that will print out
the answer as part of it's make_call.

The equivalent of calling the query might be something like

engine.execute(conjunct([Solve(python_state),  Print(python_state)])

In Prolog, if we want all solutions, we would write:

    solve(State), print_answer(State), fail.

In this case the programmer could write

engine.execute(conjunct([Solve(python_state),  Print(python_state), fail])

where fail is an instance of the Fail predicate and is like the fail 
predicate in Prolog.

The second approach is to follow a standard Prolog pattern

    solve(State) :-
        loop_continues(State),
        !,
        body_call(State),
        solve(State).
    solve(_).

In this case the programmer can use the Loop predicate that takes a
LoopBodyFactory. The programmer inherits from LoopBodyFactory and defines 
the methods loop_continues which succeeds if the loop should continue and
make_body_pred which returns an instance of the predicate to be called
in the body.
 
The send_more_money uses this approach.

Sometimes, in Prolog, we might break down the search into parts, for example

solve_part1(State), solve_part2(State), solve_part2(State

This can be done by creating a conjunct of programmer defined predicate:

conjunct([Solve1(state), Solve2(state), Solve3(state)])

In some cases the programmer might only need the first solution of, say,
Solve2(state). In this case the programmer can use the Once predicate which is
the same as once in Prolog - i.e. it removes alternative solutions from
the supplied argument as follows.

conjunct([Solve1(state), Once(Solve2(state)), Solve3(state)])

The Disjunction predicate provides the equivalent of disjunction
in Prolog e.g.

pred1 ; pred2 ; pred3

by using 

Disjunction([pred1, pred2, pred3]).

In some situations the programmer might want to see if a predicate has a 
solution but without any instantiations (bindings) of variables in the call 
persisting. This can be done with the equivalent of \+ \+ pred (not not) in 
Prolog as follows.

NotNot(pred)

This will return True iff pred returns True but with the bindings of any 
variables bound during the computation undone.
"""

from .pred import *
from .choice import *
