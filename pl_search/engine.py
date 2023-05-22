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
The definition of Engine - an approximation of the way predicate execution
is manages in Prolog.
"""

from .status import *
from .pl_vars import *

def dereference(t1:object) -> object:
    """Return the dereference of the argument."""
    if isinstance(t1, Var):
        return t1.deref()
    return t1

# Sometimes it may be useful to dereference an entire list of terms.
def dereference_list(lst:list[object]) -> list[object]:
    """Return the list of the dereferenced elements of the input."""
    return [dereference(x) for x in lst]

class Engine:
    """Engine is responsible for managing the execution of (calling) the
    supplied predicate (and it's continuation). This includes managing
    the environment stack, unifying terms, backtracking and retrying predicates.
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
        self._env_stack = []
        self._trail_stack = []

    def _trail(self, v:"Var"):
        """To be called BEFORE binding the variable so that
        v.value is the old value of the variable.
        """
        self._trail_stack.append((v, v.value))
        

    def unify(self, t1:object, t2:object) -> bool:
        """Similar to Prolog most general unification algorithm:
        return False if there are no possible bindings of the
        variables in the arguments that make the terms the same.
        If there are apply the most general unifier (binding of variables)
        and return True.
        """
        t1 = dereference(t1)
        t2 = dereference(t2)
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
        trail_stk = self._trail_stack
        while len(trail_stk) > trail_index:
            v, oldvalue = trail_stk.pop()
            v.reset(oldvalue)

    def _push_and_call(self, pred:"Pred") -> Status:
        """Add a new predicate to the environment stack and
        call that predicate.
        """
        if pred is None:
            return Status.SUCCESS
        # Add pred to the environment stack
        self._env_stack.append((pred, len(self._trail_stack)))
        return pred._call_pred()

    def _pop_call(self) -> "Pred":
        """Backtrack and then pop the top of env_stack - 
        for 'failing over the current predicate'"""
        self._backtrack()
        return self._env_stack.pop()

    def _pop_to_pred_(self, to_pred):
        """ This is to support Once by removing all calls at the top of 
        env_stack back to (and including) the previous Once entry. Note
        the backtracking is NOT done.
        """
        pred,_ = self._env_stack.pop()
        while not isinstance(pred, to_pred):
            pred,_ = self._env_stack.pop()

    def _pop_to_after_pred_(self, after_pred):
        """ This is to support Not by removing all calls at the top of 
        env_stack back to (but not including) the previous NotNot entry. Note
        the backtracking is NOT done.
        """
        pred,_ = self._env_stack[-1]       
        while not isinstance(pred, after_pred):
            self._env_stack.pop()
            pred,_ = self._env_stack[-1]       
            
    def _current_call(self) -> "Pred":
        """Return the current (top) call on the environment stack."""
        return self._env_stack[-1][0]

    def _clear_env_stack(self):
        """This is used to completely clean up after the execution is complete.
        All variables are reset to their original values."""
        while self._env_stack:
            self._pop_call()

    def execute(self, pred:"Pred") -> bool:
        """Execute (call) the supplied predicate returning True
        iff the call succeeds.
        """
        status = self._push_and_call(pred)

        while status == Status.FAILURE:
            if self._env_stack == []:
                status = Status.EXIT
                continue
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
