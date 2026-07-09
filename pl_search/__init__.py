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
and backtrack search implemented using a simplified trail.

For a given application the programmer typically defines one or more 
subclasses of Pred for carrying out the search. 
The search is then executed by calling call() on the first predicate of a 
conjunction of predicates typically ending in a predicate that prints/saves the solution
and returns True. If all solutions are required then the end predicate should prints/saves 
the solution and return False. This will trigger backtracking to find other solutions.

Each predicate has a continuation - the predicate to be called if this predicate succeeds.
When a predicate instance is created its continuation is None (treated as success). The function
conjunction takes a list of predicates and creates a continuation chain so that, when called,
each predicate in the chain will call its continuation predicate (if it succeeds). 
Some meta-predicates like Loop also modify the continuation of predicates.


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

When using this module the programmer would need to set up a Python equivalent of
State using Var objects for the unknowns and then define a ChoicePred
or VarChoicePred class where the __init__ method would find one or more
'interesting' variables and possible choices for the variables. The 
has_next, make_choice and test_choice methods would then be defined 
in such a way that the execution of this predicate would try choices 
one at a time, typically binding variables, and testing state constraints.


The equivalent of calling the query might be something like

solve_pred = Solve(python_state)
conjunction([solve_pred,  Print(python_state)])
solve_pred.call()

where Print is a subclass of Pred where the call method prints out and answer and then 
returns True.

In Prolog, if we want all solutions, we would write:

    solve(State), print_answer(State), fail.

In this case the programmer could write

solve_pred = Solve(python_state)
conjunction([solve_pred,  PrintFail(python_state)])
solve_pred.call()

where PrintFail is a subclass of Pred where the call method prints out and answer and then 
returns False. Returning False will trigger backtracking to find other solutions.


The second approach is to follow a standard Prolog pattern

    solve(State, Depth) :-
        loop_continues(State, Depth),
        !,
        body_call(State, Depth),
        Depth1 is Depth+1,
        solve(State, Depth1).
    solve(_, _).

In this case the programmer can use the Loop predicate that takes a
LoopBodyFactory. The programmer inherits from LoopBodyFactory and defines 
the methods loop_continues which succeeds if the loop should continue and
make_body_pred which returns an instance of the predicate to be called
in the body.
 
The send_more_money uses this approach.

Sometimes, in Prolog, we might break down the search into parts, for example

solve_part1(State), solve_part2(State), solve_part2(State)

This can be done by creating a conjunct of programmer defined predicate:

conjunction([Solve1(state), Solve2(state), Solve3(state)])

This function changes the continuation of each predicate to point at the next 
predicate in the sequence.

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
persisting. This can be done with the equivalent of \\+ \\+ pred (not not) in 
Prolog as follows.

NotNot(pred)

This will return True iff pred returns True but with the bindings of any 
variables bound during the computation undone.

IfThenElse(ifpred, thenpred,elsepred) is a predicate that is equivalent to Prolog's if-then-else:

ifpred-> thenpred ; elsepred

"""

from .pred import *

