
# This package provides reasonably generic search/constraint solving
# capabilities using Prolog ideas.

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

# This package does not even come close to an implementation of Prolog - it
# simply uses ideas from Prolog like variables and backtrack search implemented
# using a simplified trail and environment stack.

from enum import Enum, auto
from typing import Protocol
from typing import Generator

# Engine execution status
class Status(Enum):
    EXIT = auto()
    FAILURE = auto()
    SUCCESS = auto()

# Predicates approximate Prolog predicates.
# For a given application the programmer typically defines one or more
# predicates for carrying out the search and, typically, a subclass of
# Success or Fail for printing one solution or all solutions respectively.

class Pred(Protocol):

    # the definition for the initial call
    def make_call(self) -> Status:
        ...

    # the definition for retrying the call
    def retry_call(self) -> Status:
        ...


# The special Exit predicate - for internal use.
class Exit(Pred):
    def make_call(self) -> Status:
        return Status.EXIT

    def retry_call(self) -> Status:
        # never gets here but some defn is needed
        return Status.EXIT

    def __repr__(self):
        return 'Exit Predicate'


    
# For exiting the engine with success
class Success(Pred):
    def make_call(self) -> Status:
        return Status.SUCCESS

    def retry_call(self) -> Status:
        # never gets here but some defn is needed
        return Status.SUCCESS

    def __repr__(self):
        return 'Success Predicate'

# Like the Prolog fail - triggers backtracking
class Fail(Pred):
    def make_call(self):
        return Status.FAILURE

    def retry_call(self):
        engine.pop_call()
        return Status.FAILURE

    def __repr__(self):
        return 'Fail Predicate'


    
# Managing Environments

# An environment consists of the predicate that is (to be) called
# and a trail to be used on backtracking to reset variables that
# are bound as part of making a call on the predicate

class Environment:

    def __init__(self, pred:Pred):
        self.trail = []
        self.pred = pred

    def __repr__(self):
        # for debugging
        return f'Environment({self.pred})'

    def trail_var(self, pvar:"Var"):
        # trail var - this is always called before binding the var
        # and so pvar.value is the "old" value of the variable.
        # For normal variables (standard Prolog variables) the old value
        # is None
        self.trail.append((pvar, pvar.value))

    def backtrack(self):
        # backtrack over var bindings - these are the variables
        # that have been bound by the predicate call and so all
        # need to be reset when backtracking over the predicate call.
        while self.trail:
            v, oldvalue = self.trail.pop()
            v.reset(oldvalue)

    def __str__(self):
        return str(self.pred)

class EnvironmentStack:
    def __init__(self):
        # Add a sentinal to the "call stack" so that
        # when there are no more choices (i.e. we backtrack to the beginning)
        # then we exit the engine's computatuion.
        self.env_stack = [Environment(Exit())]

    def trail(self, v:"Var"):
        self.env_stack[-1].trail_var(v)

    def backtrack(self):
        self.env_stack[-1].backtrack()

    def push(self, pred:Pred):
        self.env_stack.append(Environment(pred))

    def pop(self) -> Pred:
        env = self.env_stack.pop()
        env.backtrack()
        return env.pred
    
    def top(self) -> Environment:
        return self.env_stack[-1]

    def clear(self):
        while self.env_stack:
            self.pop()
        self.env_stack = [Environment(Exit())]

    def __repr__(self):
        return repr(self.env_stack)

# The engine is responsible for calling the required predicates and managing
# backtracking.
class Engine:
    def __init__(self):
        self.env_stack = EnvironmentStack()

    def dereference(self, t1) -> object:
        # dereference derefs vars and leaves everything else unchanged
        if isinstance(t1, Var):
            return t1.deref()
        return t1

    # Sometimes it may be useful to dereference an entire list of terms.
    def dereference_list(self, lst) -> list[object]:
        return [self.dereference(x) for x in lst]

    def unify(self, t1, t2) -> bool:
        # unification
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
        # by having a unify_with method in a class - this extends
        # unification to include unification of Python objects (where
        # it makes sense)
        if hasattr(t1, 'unify_with'):
            return t1.unify_with(t2)
        if hasattr(t2, 'unify_with'):
            return t2.unify_with(t1)
        return False

    def backtrack(self):
        # lifting of choicepoint version
        self.env_stack.backtrack()

    def push(self, pred:Pred):
        # add a new call and call it
        self.env_stack.push(pred)

    def push_and_call(self, pred:Pred) -> Status:
        # add a new call and call it
        self.env_stack.push(pred)
        return pred.make_call()

    def pop_call(self) -> Pred:
        # remove old call - note the pop'ed call is returned
        # to be used for retrying
        return self.env_stack.pop()

    def current_call(self) -> Pred:
        # get the call from the top env
        return self.env_stack.top().pred

    def execute(self, pred:Pred) -> bool:
        status = self.push_and_call(pred)

        while status == Status.FAILURE:
            # backtrack and retry the current call
            self.backtrack()
            pred_call = self.current_call()
            status = pred_call.retry_call()
        self.env_stack.clear()
        return status == Status.SUCCESS

#### !!! NOTE !!!
#### A single global instance of the Engine class is created
#### so that this instance can be accessed everywhere.

engine = Engine()

# a test to see if a term is a variable (after deref) -
# like the Prolog var test
def var(t):
    return isinstance(t, Var) and isinstance(t.deref(), Var)

# The only Prolog data structure is  Var - for all other cases we use
# Python data structtures
class Var:
    # for generating id's of variables
    c = 0

    @classmethod
    def update(cls):
        cls.c += 1
        return cls.c

    @classmethod
    def reset_count(cls):
        cls.c = 0

    # A variable consists of an ID and a value if the variable is not bound
    # then the value is None
    def __init__(self):
        self.id_ =  self.update()
        self.value = None

    # For printing the variable
    def __repr__(self):
        val = self.deref()
        if isinstance(val, Var):
            return f"X{val.id_:02d}"
        return f"{val}"

    def deref(self):
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
    def bind(self, val):
        # check unbound
        assert isinstance(self, UpdatableVar) or self.value is None
        # check we don't get a loop
        assert not (isinstance(val, Var) and val.deref() == self)
        # do binding
        self.value = val
        return True

    #  (for backtracking)
    def reset(self, oldvalue):
        self.value = oldvalue

    # test for equality of this var with other
    def __eq__(self, other):
        # deref v and other
        v = self.deref()
        if var(other):
            other = other.deref()
        if isinstance(v, Var) and isinstance(other, Var):
            return v.id_ == other.id_
        if isinstance(v, Var) or isinstance(other, Var):
            return False
        return v == other

    def __lt__(self, other):
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
    def __init__(self, initialval):
        super().__init__()
        self.value = initialval

    # not used as a normal variable - deref just returns self
    # so that it's this variable that will be updated when binding
    # this variable
    def deref(self):
        return self

    def __eq__(self, other):
        return isinstance(other, UpdatableVar) and self.value == other.value

    def __repr__(self):
        return f'UpdatableVar({self.value})'

# The fail predicate
class Fail(Pred):
    def make_call(self):
        return Status.FAILURE

    def retry_call(self):
        engine.pop_call()
        return Status.FAILURE

    def reset(self):
        pass

    def __repr__(self):
        return 'Fail Predicate'

# For use in ChoicePred below for generating choices then making (and testing)
# those choices.
class ChoiceHandler(Protocol):
    def __init__(self, args):
        ...

    # returns True if there is another variable that can be chosen
    # and if so produce a generator of possible choices for that variable
    # False means that there are no more variables to be considered and
    # so the ChoicePred succeeds.
    def generate_choice(self) -> bool:
        ...

    def make_choice(self) -> bool:
        ...

# This predicate is like the following Prolog predicate
#
#  choice(State) :-
#    pick_var(State, Var),
#    !,
#    generate_var_choices(State, Var, Choices),
#    member(Var, Choices),
#    check_choice(State),
#    choice(State).
#  choice(_).
#
#  The programmer is required to implement a choice handler where
#  generate_choice should be like the combination of pick_var and
#  generate_var_choices
#  make_choice should be like the combination of member and check_choice
class ChoicePred(Pred):
    def __init__(self, handler_factory, handler_args, continuation_pred):
        self.handler_factory = handler_factory
        self.handler = None
        self.handler_args = handler_args
        self.continuation_pred = continuation_pred

    def make_call(self) -> Status:
        self.handler = self.handler_factory(self.handler_args)
        if self.handler.generate_choice():
            return self.retry_call()   # code reuse
        # we have succeeded and there are no more variables to choose
        # so call the next predicate
        return engine.push_and_call(self.continuation_pred)

    def retry_call(self) -> Status:
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
