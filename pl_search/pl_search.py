
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
that covers a significant portion of the use of the module.

Below is a description of how some approaches for solving search problems
in Prolog are translated into Python using this module.

The first approach in Prolog follows the pattern:

    solve(State), print_answer(State).

where solve is completely implemented in Prolog. Calling this query (a pair
of predicate calls) would use backtracking search to attempt to find, 
and print a solution.

Using this module the programmer would need to set up a Python equivalent of
State using Var objects for the unknowns and then defining a Pred class
where make_call initialises and starts the search and where retry_call
deals with backtracking and trying alternatives.

The programmer will typically inherit from the Success predicate that will
print out the answer as part of it's make_call.

The equivalent of calling the query might be something like

engine.execute(python_pred, python_state,  python_print_success(python_state))

In Prolog, if we want all solutions, we would write:

    solve(State), print_answer(State), fail.

In this case the programmer would inherit from the Fail predicate and we
would get something like

engine.execute(python_pred, python_state,  python_print_fail(python_state))

The second approach is to follow a standard Prolog pattern as described
later in ChoicePred where the Prolog implementation of solve follows the
pattern

    solve(State) :-
        pick_var(State, Var),
        !,
        generate_var_choices(State, Var, Choices),
        member(Var, Choices),
        check_choice(State),
        solve(State).
    solve(_).

ChoicePred follows this pattern, simplifying the problem for the programmer.
The programmer now only needs to answer the following questions to create
an implementation.

1. How do I pick a variable to choose possible values for?
2. What are the possible values for this variable?
3. How do I check that a given choice is valid?
4. (optionally) Are there any deductions that can be made given the choice?

To program answers to these questions the programmer can define a ChoiceHandler
where generate_choice answers 1. and 2. and make_choice (after binding the
variable to the choice) answers 3. and 4.

The send_more_money uses this approach where solving the puzzle is done as 
follows (where SmartPuzzleHandler implements the answers the above questions).

engine.execute(ChoicePred(SmartPuzzleHandler, 
               (constraint_sums, all_vars), 
               SuccessPrint()))

Sometimes, in Prolog, we might break down the search into parts:

solve_part1(State), solve_part2(State), .....

In this case the equivalent of solve_part2 would be a Pred with its own
continuation and would be the continuation of the equivalent of solve_part1.

"""

from enum import Enum, auto
from typing import Protocol
from typing import Generator

class Status(Enum):
    """ Engine execution status """
    EXIT = auto()
    FAILURE = auto()
    SUCCESS = auto()


class Pred(Protocol):
    """ Approximates Prolog predicates."""
    def make_call(self) -> Status:
        """The definition for the initial call on the predicate."""
        ...

    def retry_call(self) -> Status:
        """The definition for retrying the call on backtracking."""
        ...


class Exit(Pred):
    """A special predicate to exit engine execution - for internal use."""
    def make_call(self) -> Status:
        return Status.EXIT

    def retry_call(self) -> Status:
        # never gets here but some defn is needed
        return Status.EXIT

    def __repr__(self):
        return 'Exit Predicate'


    
# For exiting the engine with success
class Success(Pred):
    """Similar to 'true' in Prolog - typically used as a continuation."""
    def make_call(self) -> Status:
        return Status.SUCCESS

    def retry_call(self) -> Status:
        # never gets here but some defn is needed
        return Status.SUCCESS

    def __repr__(self):
        return 'Success Predicate'

class Fail(Pred):
    """Similar to 'fail' in Prolog - typically used as a continuation."""
    def make_call(self) -> Status:
        return Status.FAILURE

    def retry_call(self) -> Status:
        # never gets here but some defn is needed
        return Status.FAILURE

    def __repr__(self):
        return 'Fail Predicate'


    
# Managing Environments

# An environment consists of the predicate that is (to be) called
# and a trail to be used on backtracking to reset variables that
# are bound as part of making a call on the predicate

class Environment:
    """An approximation of a Prolog environment for managing backtracking
    and retrying predicate calls. This is for internal use.

    Attributes:
        trail: a list of (variable, oldvalue) pairs - on backtracking the
               current value of variable is reset to oldvalue for each
               variable in trail.
        pred: the called predicate that created this environment - on
              backtracking the retry_call method of pred is called
              in order to find alternative solutions for pred
    
    """
    def __init__(self, pred:Pred):
        self.trail = []
        self.pred = pred

    def __repr__(self):
        # for debugging
        return f'Environment({self.pred})'

    def trail_var(self, pvar:"Var"):
        """To be called BEFORE binding the variable so that
        pvar.value is the old value of the variable.
        """
        self.trail.append((pvar, pvar.value))

    def backtrack(self):
        """Backtrack over (reset) all the var bindings in the trail."""
        while self.trail:
            v, oldvalue = self.trail.pop()
            v.reset(oldvalue)

    def __str__(self):
        return str(self.pred)

class EnvironmentStack:
    """An approximation of a Prolog environment stack. It is a list of
    Environments - one for each predicate in the call stack. The stack is
    created by making a predicate call and then calling it's continuation
    predicate (and possibly the continuations continuation etc.).
    This is for internal use.
    """
    def __init__(self):
        """The stack is initialized with a sentinal so that if execution
        backtracks to before the initial predicate call the engine
        exicution will terminate.
        """
        self.env_stack = [Environment(Exit())]

    def trail(self, v:"Var"):
        """Trail v in the current (top) environment. """
        self.env_stack[-1].trail_var(v)

    def backtrack(self):
        """Backtrack in the current (top) environment. """
        self.env_stack[-1].backtrack()

    def push(self, pred:Pred):
        """Add a new environment for pred."""
        self.env_stack.append(Environment(pred))

    def pop(self) -> Pred:
        """Remove the current environment, bactrack in that environment
        and return that environment so that the pred can be retried.
        """
        
        env = self.env_stack.pop()
        env.backtrack()
        return env.pred
    
    def top(self) -> Environment:
        """Return the current (top) environment."""
        return self.env_stack[-1]

    def clear(self):
        """Clear the environment stack - i.e. backtrack to before
        the first pred call.
        """
        while self.env_stack:
            self.pop()
        self.env_stack = [Environment(Exit())]

    def __repr__(self):
        return repr(self.env_stack)

# The engine is responsible for calling the required predicates and managing
# backtracking.
class Engine:
    """Engine is responsible for managing the execution (calling) of the
    supplied predicate (and it's continuation). This includes managing
    the environment stack, dereferencing terms, unifying terms,
    backtracking and retrying predicates.
    """
    def __init__(self):
        self.env_stack = EnvironmentStack()

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
            self.env_stack.trail(t1)
            return t1.bind(t2)
        if isinstance(t2, Var):
            # bind and trail
            self.env_stack.trail(t2)
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

    def backtrack(self):
        """Lifting backtrack from the environment stack."""
        self.env_stack.backtrack()

    def push(self, pred:Pred):
        """Add a new predicate to the environment stack."""
        self.env_stack.push(pred)

    def push_and_call(self, pred:Pred) -> Status:
        """Add a new predicate to the environment stack and
        call that predicate.
        """
        self.env_stack.push(pred)
        return pred.make_call()

    def pop_call(self) -> Pred:
        """Lifting of pop for the environment stack."""
        return self.env_stack.pop()

    def current_call(self) -> Pred:
        """Return the current (top) call on the environment stack."""
        return self.env_stack.top().pred

    def execute(self, pred:Pred) -> bool:
        """Execute (call) the supplied predicate returning True
        iff the call succeeds.
        """
        status = self.push_and_call(pred)

        while status == Status.FAILURE:
            # backtrack and retry the current call
            self.backtrack()
            pred_call = self.current_call()
            status = pred_call.retry_call()
        # Note that the following clears the environment stack
        # including backtracking over all variable bindings
        # and so all binding created by a successful search will be lost.
        # This means the programmer will need to output any relevant
        # information from a successful search in the continuation. 
        self.env_stack.clear()
        return status == Status.SUCCESS

#### !!! NOTE !!!
#### A single global instance of the Engine class is created
#### so that this instance can be accessed everywhere within the application.

engine = Engine()

# a test to see if a term is a variable (after deref) -
# like the Prolog var test
def var(t):
    """Return True iff the argument is a variable after dereferencing."""
    return isinstance(t, Var) and isinstance(t.deref(), Var)

# The only Prolog data structure is  Var - for all other cases we use
# Python data structtures
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
        dereference chain and return the untimate value."""
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

    # bind an unbound variable
    def bind(self, val:object):
        """Bind the variable to the supplied value."""
        # check unbound
        assert isinstance(self, UpdatableVar) or self.value is None
        # check we don't get a loop
        assert not (isinstance(val, Var) and val.deref() == self)
        # do binding
        self.value = val
        return True

    #  (for backtracking)
    def reset(self, oldvalue:object):
        """Reset the value to the supplied value - called when untrailing."""
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

# For use in ChoicePred below for generating choices then making (and testing)
# those choices.
class ChoiceHandler(Protocol):
    """For use in ChoicePred for generating choices then making (and testing)
    those choices.
    """
    def __init__(self, args:object):
        ...

    # returns True if there is another variable that can be chosen
    # and if so produce a generator of possible choices for that variable
    # False means that there are no more variables to be considered and
    # so the ChoicePred succeeds.
    def generate_choice(self) -> bool:
        """Return True if there is another variable that can be chosen
        and if so produce a generator of possible choices for that variable.
        False means that there are no more variables to be considered and
        in which case the ChoicePred succeeds.
        """
        ...

    def make_choice(self) -> bool:
        """Take the variable and generator produced by generate_choice
        and try binding that variable to next of the generator. Return
        True iff the choice is valid. 
        NOTE: It is important that the implementation
        of make_choice uses next on the generator in order to make
        the choice so that retry_call in ChoicePred will terminate.
        """
        ...


class ChoicePred(Pred):
    """
    This predicate behaves like the following Prolog predicate

    solve(State) :-
        pick_var(State, Var),
        !,
        generate_var_choices(State, Var, Choices),
        member(Var, Choices),
        check_choice(State),
        solve(State).
    solve(_).
    
    The programmer is required to implement a choice handler where
    generate_choice should be like the combination of pick_var and
    generate_var_choices and make_choice should be like the combination 
    of member and check_choice above.

    Attributes:
        handler_factory: the ChoiceHandler - in relation to the Prolog
           code above it's for generating a new instance of the body on
           each recursive call.
        handler: like the generated instance of the Prolog body.
        handler_args: the argument used by handle_factory to generate
           a handler - probably a tuple encoding state.
        continuation_pred: the predicate to call when this ChoicePred
        completes with success - like the Prolog call
        choices(State), continuation_pred(State)
    """
    
    def __init__(self, handler_factory:ChoiceHandler,
                 handler_args:object, continuation_pred:Pred):
        self.handler_factory = handler_factory
        self.handler = None
        self.handler_args = handler_args
        self.continuation_pred = continuation_pred

    def make_call(self) -> Status:
        """Make the initial call on the predicte."""
        self.handler = self.handler_factory(self.handler_args)
        if self.handler.generate_choice():
            return self.retry_call()   # code reuse
        # we have succeeded and there are no more variables to choose
        # so call the next predicate
        return engine.push_and_call(self.continuation_pred)

    def retry_call(self) -> Status:
        """Retry calling the predicate on backtracking."""
        try:
            if not self.handler.make_choice():
                # the choice failed
                return Status.FAILURE
            # like the recursive call on the Prolog choice predicate
            return engine.push_and_call(ChoicePred(self.handler_factory,
                                                   self.handler_args,
                                                   self.continuation_pred))
        except StopIteration:
            # run out of choices so fail
            engine.pop_call()
            return Status.FAILURE
