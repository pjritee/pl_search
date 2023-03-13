
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

For a given application the programmer typically defines a subclass
of Pred for carrying out the search and, typically, a subclass of
Success or Fail for printing one solution or all solutions respectively.

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
where initialize_call initialises and where try_choice defines how to process
a given choice.

The management of calling predicates and backtracking is done in Engine.

The programmer will typically inherit from the Success predicate that will
print out the answer as part of it's make_call.

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
"""

from enum import Enum, auto
from typing import Protocol
from typing import Generator
from abc import ABC, abstractmethod

class Status(Enum):
    """ Engine execution status """
    EXIT = auto()
    FAILURE = auto()
    SUCCESS = auto()


class Pred(ABC):
    """ Approximates Prolog predicates. The programmer needs to define
    self.choice_iterator before the predicate object is 'called'. This
    iterator is used to drive backtracking.
    """

    @property
    def continuation(self):
        """ The predicate to be called if (and when) this predicate succeeds.
        For internal use. """
        if hasattr(self, '_continuation'):
            return self._continuation
        return None
    
    @continuation.setter
    def continuation(self, cont):
        if self.continuation is None:
            self._continuation = cont
        else:
            self._continuation = cont
            
    def _call_pred(self) -> Status:
        """ Call the predicate. For internal use. """
        self.initialize_call()
        return self._try_call()

    def _try_call(self) -> Status:
        """ Try the alternative choices. For internal use. """
        try:
            if self.try_choice(next(self.choice_iterator)):
                # the call succeeded - call the next predicate
                return engine._push_and_call(self.continuation)
            # the call failed
            #engine._pop_call()
            return Status.FAILURE
        except StopIteration:
            # The choices have been exhausted - no more solutions
            engine._pop_call()
            return Status.FAILURE

    @abstractmethod
    def initialize_call(self):
        """This initializes the predicate - for example setting a
        variable and setting the choice_iterator so that, on backtracking,
        the variable can be bound to each choice in the iterator.
        Setting choice_iterator is required here.
        """
        pass

    @abstractmethod
    def try_choice(self, choice)-> bool:
        """choice is the next item of the choice_iterator and this should
        return True iff this is a valid choice for whatever valid means
        in the application.
        """
        pass

    def __repr__(self):
        return f'Pred : {self.continuation}'

class Exit(Pred):
    """A special predicate to exit engine execution - for internal use."""

    def initialize_call(self):
        pass

    def try_choice(self, _) -> bool:
        return True

    def _try_call(self) -> Status:
        return Status.EXIT
    
    def __repr__(self):
        return 'Exit Predicate'


    
class Fail(Pred):
    """Similar to 'fail' in Prolog - typically used as a continuation
    to drive backtracking."""

    def initialize_call(self):
        # making the iterator empty causes this predicate to fail
        # when called
        self.choice_iterator = iter([])

    def try_choice(self, _) -> bool:
        return False

    def __repr__(self):
        return 'Fail Predicate'

# We only need one instance of Fail and Exit
fail = Fail()
_exit = Exit()
    

class Engine:
    """Engine is responsible for managing the execution of (calling) the
    supplied predicate (and it's continuation). This includes managing
    the environment stack, dereferencing terms, unifying terms,
    backtracking and retrying predicates.
    """
    def __init__(self):
        """
        Attributes:
           _env_stack: a list of pairs of predicate objects together with
                the index into the trail that was one past the top of the 
                trail_stack when the predicate was called.

            _trail_stack: a list of variable, old_value pairs so that on
                backtracking the variable's value can be reset to it's old
                value.
        """
        # (_exit, 0) is used as a sentinal that deals with backtracking
        # past the initial predicate call
        self._env_stack = [(_exit, 0)]
        self._trail_stack = []

    def _trail(self, v:"Var"):
        """To be called BEFORE binding the variable so that
        v.value is the old value of the variable.
        """
        self._trail_stack.append((v, v.value))
        
    def dereference(self, t1:object) -> object:
        """Return the dereference of the argument."""
        if isinstance(t1, Var):
            return t1.deref()
        return t1

    # Sometimes it may be useful to dereference an entire list of terms.
    def dereference_list(self, lst:list[object]) -> list[object]:
        """Return the list of the dereferenced elements of the input."""
        return [self.dereference(x) for x in lst]

    def unify(self, t1:object, t2:object) -> bool:
        """Similar to Prolog most general unification algorithm:
        return False if there are no possible bindings of the
        variables in the arguments that make the terms the same.
        If there are apply the most general unifier (binding of variables)
        and return True.
        """
        t1 = self.dereference(t1)
        t2 = self.dereference(t2)
        if t1 == t2:
            # if identical then succeed - note uses __eq__ in Var
            # for comparing Var/Var and Var/nonVar
            return True
        if isinstance(t1, Var):
            # bind and trail
            self._trail(t1)
            return t1.bind(t2)
        if isinstance(t2, Var):
            # bind and trail
            self._trail(t2)
            return t2.bind(t1)
        if isinstance(t1, list):
            # seems useful to unify Python lists as part of unify -
            # probably quite a common requirement
            return isinstance(t2, list) and len(t1) == len(t2) and \
                all(self.unify(x, y) for x,y in zip(t1, t2))
        # approximate unification with other kinds of terms
        # by having a unify_with method in each class of relevant
        # terms - this extends unification to include unification of
        # Python objects (where it makes sense).
        # An example is where the programmer might want the equivalent
        # of specific kinds of 'compound terms' that could contain variables.
        if hasattr(t1, 'unify_with'):
            return t1.unify_with(t2)
        if hasattr(t2, 'unify_with'):
            return t2.unify_with(t1)
        return False

    def _backtrack(self):
        """Backtrack (reset all varible bindings) as a consequence of calling
        the 'current' predicate"""
        _, trail_index = self._env_stack[-1]
        while len(self._trail_stack) > trail_index:
            v, oldvalue = self._trail_stack.pop()
            v.reset(oldvalue)

    def _push(self, pred:Pred):
        """Add a new predicate to the environment stack."""
        self._env_stack.append((pred, len(self._trail_stack)))

    def _push_and_call(self, pred:Pred) -> Status:
        """Add a new predicate to the environment stack and
        call that predicate.
        """
        if pred is None:
            return Status.SUCCESS
        self._push(pred)
        return pred._call_pred()

    def _pop_call(self) -> Pred:
        """Backtrack and then pop the top of env_stack - 
        for 'failing over the current predicate'"""
        self._backtrack()
        return self._env_stack.pop()

    def _pop_to_once_(self):
        """ This is to support Once by removing all calls at the top of 
        env_stack back to (and including) the previous Once entry. Note
        the backtracking is NOT done.
        """
        pred,_ = self._env_stack.pop()
        while not isinstance(pred, Once):
            pred,_ = self._env_stack.pop()

            
    def _current_call(self) -> Pred:
        """Return the current (top) call on the environment stack."""
        return self._env_stack[-1][0]

    def _clear_env_stack(self):
        """This is used to completely clean up after the execution is complete.
        All variables are reset to their original values."""
        while self._env_stack:
            self._pop_call()
        self._env_stack = [(_exit,0)]

    def execute(self, pred:Pred) -> bool:
        """Execute (call) the supplied predicate returning True
        iff the call succeeds.
        """
        status = self._push_and_call(pred)

        while status == Status.FAILURE:
            # backtrack and retry the current call
            self._backtrack()
            pred_call = self._current_call()
            status = pred_call._try_call()
        # Note that the following clears the environment stack
        # including backtracking over all variable bindings
        # and so all binding created by a successful search will be lost.
        # This means the programmer will need to output any relevant
        # information from a successful search in the continuation. 
        self._clear_env_stack()
        return status == Status.SUCCESS

#### !!! NOTE !!!
#### A single global instance of the Engine class is created
#### so that this instance can be accessed everywhere within the application.

engine = Engine()

def var(t):
    """Return True iff the argument is a variable after dereferencing."""
    return isinstance(t, Var) and isinstance(t.deref(), Var)

# The only Prolog data structure is  Var - for all other cases we use
# Python data structures

class Var:
    """Var is like a Prolog variable.

    Class Attribute:
        c : counter for generating unique ID's

    Attributes:
        id_: a unique ID (int)
        value: If the variable is unbound this is None otherwise it
               it is the value the variable is bound (instantiated) to.
    """
    # for generating id's of variables
    c = 0

    @classmethod
    def update(cls) -> int:
        """Return the next ID"""
        cls.c += 1
        return cls.c

    @classmethod
    def reset_count(cls):
        """Reset the counter - in an application where multiple searches
        are carried out then resetting the counter between searches reduces
        the size of the string representation of the variable."""
        cls.c = 0

    def __init__(self):
        self.id_ =  self.update()
        self.value = None

    # For printing the variable
    def __repr__(self):
        val = self.deref()
        if isinstance(val, Var):
            return f"X{val.id_:02d}"
        return f"{val}"

    def deref(self) -> object:
        """Return self if the variable is unbound otherwise follow the
        dereference chain and return the ultimate value."""
        val = self
        while True:
            if val.value is None:
                # unbound variabe
                return val
            if not isinstance(val.value, Var):
                # end of reference chain is a non-var value
                return val.value
            # step down ref chain
            val = val.value
        # check we never get here
        assert False

    def bind(self, val:object):
        """Bind the variable to the supplied value."""
        # check unbound
        assert isinstance(self, UpdatableVar) or self.value is None
        # check we don't get a loop
        assert not (isinstance(val, Var) and val.deref() == self)
        # do binding
        self.value = val
        return True

    def reset(self, oldvalue:object):
        """Reset the value to the supplied value - called when untrailing
        as part of backtracking."""
        self.value = oldvalue

    def __eq__(self, other:object):
        """Test for equality of this var with the supplied term."""
        # deref v and other
        v = self.deref()
        if var(other):
            other = other.deref()
        if isinstance(v, Var) and isinstance(other, Var):
            return v.id_ == other.id_
        if isinstance(v, Var) or isinstance(other, Var):
            return False
        return v == other

    def __lt__(self, other:object):
        """Like the @< test in Prolog."""
        # deref v
        v = self.deref()
        if var(other):
            other = other.deref()
        if var(v):
            if var(other):
                # if both vars then use id's
                return v.id_ < other.id_
            return False
        if var(other):
            return True
        # this can only succeed if both v and i (deref'ed) are
        # equal as Python terms
        return v < other

class UpdatableVar(Var):
    """UpdatableVar is used to implement what some Prologs call
    updatable assignment. This is typically used to store (part of) the
    state in a way that can be backtracked over. For example, after
    binding a variable and then making some deductions the availabe choices
    for another variable might have been reduced and we can use an UpdatableVar
    to store that value as the computation moves forward but on backtracking
    the old value will be restored.
    """
    def __init__(self, initialval:object):
        super().__init__()
        self.value = initialval

    def deref(self):
        """Unlike Var this is doesn't follow the dereference chain and so 
        if the value is another variable we don't deref that variable. 
        This means that the value (variable) will be replaced in a 
        subsequent bind."""
        return self

    def __eq__(self, other):
        return isinstance(other, UpdatableVar) and self.value == other.value

    def __repr__(self):
        return f'UpdatableVar({self.value})'


def conjunct(predlst:list[Pred]) -> Pred:
    """Return a single Pred created by chaining their continuations - the
    same as a sequence of conjunctions in Prolog.
    """
    for p1, p2 in zip(predlst[:-1], predlst[1:]):
        p1.continuation = p2
    return predlst[0]

class LoopBodyFactory(Protocol):
    """A factory for creating instances of a Pred used in the Loop predicate."""
    
    def loop_continues(self) -> bool:
        """Returns True iff the Loop predicate should continue."""
        ...

    def make_body_pred(self) -> Pred:
        """Create an instance of the predicate to be called in the loop body."""
        ...

class Loop(Pred):
    """Creating a predicate that is the equivalent of a Prolog predicate
    like
        loop(State) :-
            loop_continues(State), !,
            body_call(State),
            loop(State).
        loop(_).
    """
    def __init__(self, body_factory:LoopBodyFactory):
        self.body_factory = body_factory

    def initialize_call(self):
        # deterministic predicate
        self.choice_iterator = iter([1])

    def _try_call(self) -> Status:
        try:
            next(self.choice_iterator)
            if self.body_factory.loop_continues():
                pred = self.body_factory.make_body_pred()
                pred.continuation = Loop(self.body_factory)
                pred.continuation.continuation = self.continuation
                return engine._push_and_call(pred)
            return engine._push_and_call(self.continuation)
        except StopIteration:
            engine._pop_call()
            return Status.FAILURE
            
    def try_choice(self, _):
        return True
     

    def __repr__(self):
        return f'Loop(self.body_factory) : {self.continuation}'

class _OnceEnd(Pred):
    """For internal use only. A dummy predicate that when called pops
    the environment (call stack) back to just before the  closest
    Once entry."""
    def initialize_call(self):
        self.choice_iterator = iter([1])

    def _try_call(self) -> Status:
        try:
            next(self.choice_iterator)
            engine._pop_to_once_()
            return engine._push_and_call(self.continuation)
        except StopIteration:
            engine._pop_call()
            return Status.FAILURE
            
    def try_choice(self, _):
        return True
    
class Once(Pred):
    """The Python implementation of the Prolog once meta-predicate
    that removes alternatives from the given predicate.
    """
    
    def __init__(self, pred):
        """ pred is the predicate that Once applies to."""
        self._pred = pred

    def initialize_call(self):
        # deterministic predicate
        self.choice_iterator = iter([1])

    def _try_call(self) -> Status:
        try:
            next(self.choice_iterator)
            self._pred.continuation = _OnceEnd()
            self._pred.continuation.continuation = self.continuation
            return engine._push_and_call(self._pred)
        except StopIteration:
            engine._pop_call()
            return Status.FAILURE
            
    def try_choice(self, _):
        return True

        
class Disjunction(Pred):
    """The predicate that is the disjunction of a list of predicates.
    Similar to Prolog's pred1 ; pred2 ; ...
    """
    
    def __init__(self, pred_list):
        self.pred_list = pred_list
        
    def initialize_call(self):
        self.choice_iterator = iter(self.pred_list)

    def _try_call(self) -> Status:
        try:
            pred = next(self.choice_iterator)
            pred.continuation = self.continuation
            return engine._push_and_call(pred)
        except StopIteration:
            engine._pop_call()
            return Status.FAILURE
            
    def try_choice(self, _):
        return True
