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

from abc import ABC, abstractmethod
from typing import Protocol
from .status import *
from .engine import *

"""
Support for defining predicates that approximate Prolog predicates.
"""

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

    def last_pred(self):
        """Follow the continuation chain returning the last pred in the chain."""
        if self.continuation is None:
            return self
        else:
            return self.continuation.last_pred()

        
    def _call_pred(self) -> Status:
        """ Call the predicate. For internal use. """
        self.initialize_call()
        return self._try_call()

    def test_choice(self):
        """Test the choice (just made). To be overridden in subclass
        if a test is required for the given choice."""
        return True
    
    def _try_call(self) -> Status:
        """ Try the alternative choices. For internal use. """
        try:
            if next(self.choice_iterator).apply_choice() and \
               self.test_choice():
                # the call succeeded - call the next predicate
                return engine._push_and_call(self.continuation)
            # the call failed
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

    def __repr__(self):
        return f'Pred : {self.continuation}'

class SemiDetPred(Pred):
    """ A semi-deterministic predicate (0 or 1 solutions). 
    As any predicate that inherits from SemiDetPred is semi-deterministic the 
    programmer is not required to define choice_iterator. 
    """

    def _try_call(self) -> Status:
        # remove this pred from stack as it's no longer required
        engine._env_stack.pop()
        if self.test_choice():
            return engine._push_and_call(self.continuation)
        return Status.FAILURE

class DetPred(Pred):
    """ A deterministic predicate (exectly one solutions).
    As any predicate that inherits from DetPred is deterministic the 
    programmer is not required to define choice_iterator. 
    All the work should be done in initialize_call.
    """
    def _try_call(self) -> Status:
        # remove this pred from stack as it's no longer required
        engine._env_stack.pop()
        return engine._push_and_call(self.continuation)
    
class Exit(Pred):
    """A special predicate to exit engine execution - for internal use."""

    def initialize_call(self):
        pass

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

    def __repr__(self):
        return 'Fail Predicate'

# We only need one instance of Fail and Exit
fail = Fail()
_exit = Exit()



def conjunct(predlst:list[Pred]) -> Pred:
    """Return a single Pred created by chaining their continuations - the
    same as a sequence of conjunctions in Prolog.
    """
    if predlst == []:
        return None
    for i in range(len(predlst)-1):
        predlst[i].last_pred().continuation = predlst[i+1]
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
        pass

    def _try_call(self) -> Status:
        # remove Loop pred from stack as it's no longer required
        engine._env_stack.pop()
        if self.body_factory.loop_continues():
            pred = self.body_factory.make_body_pred()
            # reuse this object as the continuation for pred
            pred.last_pred().continuation = self
            return engine._push_and_call(pred)

        return engine._push_and_call(self.continuation)
            

    def __repr__(self):
        return f'Loop({self.body_factory}) : {self.continuation}'

class _OnceEnd(DetPred):
    """For internal use only. A dummy predicate that when called pops
    the environment (call stack) back to just before the  closest
    Once entry."""

    def initialize_call(self):
        pass
    
    def _try_call(self) -> Status:
        engine._pop_to_pred_(Once)
        return engine._push_and_call(self.continuation)
            
    
class Once(DetPred):
    """The Python implementation of the Prolog once meta-predicate
    that removes alternatives from the given predicate.
    """
    
    def __init__(self, pred):
        """ pred is the predicate that Once applies to."""
        self._pred = pred

    def initialize_call(self):
        pass
    
    def _try_call(self) -> Status:
        self._pred.continuation = _OnceEnd()
        self._pred.continuation.continuation = self.continuation
        return engine._push_and_call(self._pred)
            
        
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
            pred.last_pred().continuation = self.continuation
            return engine._push_and_call(pred)
        except StopIteration:
            engine._pop_call()
            return Status.FAILURE
            

    def __repr__(self):
        return f'Disjunction({self.pred_list}) : {self.continuation}'

class _NotNotEnd(DetPred):
    """For internal use only. A dummy predicate that when called pops
    the environment (call stack) back to just after the  closest
    NotNot entry."""

    def initialize_call(self):
        pass
    
    def _try_call(self) -> Status:
        engine._pop_to_after_pred_(NotNot)
        return Status.SUCCESS
            

    
class NotNot(Pred):
    """NotNot(pred) returns True iff pred returns True but with all variable
    bindings created by calling pred removed. Like Prolog's \+ \+ pred
    """

    def __init__(self, pred):
        """ pred is the predicate that NotNot applies to."""
        self._pred = pred
        self.succeeded = False

    def initialize_call(self):
        self.choice_iterator = iter([1,2])

    def _try_call(self) -> Status:
        try:
            i = next(self.choice_iterator)
            if i == 1:
                # the first choice is like Once(pred), Fail
                # except we remember if pred succeeds
                self._pred.last_pred().continuation  = _NotNotEnd()
                if engine._push_and_call(self._pred) == Status.SUCCESS:
                    self.succeeded = True
                return Status.FAILURE
            if self.succeeded:
               return engine._push_and_call(self.continuation)
            return self.Status.FAILURE
        except StopIteration:
            engine._pop_call()
            return Status.FAILURE
    
    def __repr__(self):
        return f'NotNot({self._pred})'
