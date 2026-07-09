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
The Pred class and several of its subclasses. The Trail class is included here
as it is used throughout the Pred classes.
"""

from typing import Protocol, Any

from .pl_vars import *


class Trail:
    """A trail is a list of (variable, old_value) pairs so that on backtracking
    the variable's value can be reset to it's old value.
    """
    def __init__(self):
        self.stack = []  # a list of (variable, old_value) pairs so that on backtracking the variable's value can be reset to it's old value.

    def push(self, v:Var):
        """Push the variable together with its current value onto the trail stack."""
        self.stack.append((v, v.value))

    def unbind_to(self, old_tos:int):
        """unbind_to the trail stack back to the given top of stack."""
        while len(self.stack) > old_tos:
            v, old_value = self.stack.pop()
            v.value = old_value

    def size(self) -> int:
        """Return the size of the trail stack (top of stack)."""
        return len(self.stack)
    
trail = Trail()  # One instance of the trail stack is required for the entire program.

def dereference(t1:Any) -> Any:
    """Return the dereference of the argument."""
    if isinstance(t1, Var):
        return t1.deref()
    return t1  # all other values included user-defined terms are already dereferenced

# Sometimes it may be useful to dereference an entire list of terms.
def dereference_list(lst:list[Any]) -> list[Any]:
    """Return the list of the dereferenced elements of the input."""
    return [dereference(x) for x in lst]


def unify(t1:Any, t2:Any) -> bool:
    """Similar to Prolog most general unification algorithm:
    return False if there are no possible bindings of the
    variables in the arguments that make the terms the same.
    """
    t1 = dereference(t1)
    t2 = dereference(t2)
    if t1 == t2:
        # if identical then succeed - note uses __eq__ in Var
        # for comparing Var/Var and Var/nonVar
        return True
    if isinstance(t1, Var):
        # bind and trail
        trail.push(t1)
        return t1.bind(t2)
    if isinstance(t2, Var):
        # bind and trail
        trail.push(t2)
        return t2.bind(t1)
    if isinstance(t1, list):
        # seems useful to unify Python lists as part of unify -
        # probably quite a common requirement
        return isinstance(t2, list) and len(t1) == len(t2) and \
            all(unify(x, y) for x,y in zip(t1, t2))
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

"""
Base class for Prolog-like predicates.

The Pred class implements Prolog-like predicates.
It uses a continuation-passing style to manage the flow of execution.
Derived classes implement specific predicate behaviors.
Predicates are used to program backtrack search in a Prolog-like style.
Execution of the search is initiated by calling the call() method of the first
predicate in a chain of predicates. Non-determinism is typically implemented
using one or more ChoicePred predicates which are used to make choices.
The DisjPred meta-predicate can also be used to implement non-determinism by providing
alternatives to be tried in order. It's possible for the user to implement non-deterministic
predicates themselves but a combination of ChoicePred predicates and DisjPred predicates is usually sufficient.
   
The key method is call() which is called to execute the predicate. Any system defined and user defined call()
method is required to satisfy the following contract for each choice point in the execution of the predicate:
- If the execution for this choice succeeds "locally" then the call() method must call the continuation
    of the predicate by calling call_continuation().
- If the execution fails either locally or due to a failure in the continuation then the call() method should
    try the next choice point (if any).
- If the execution fails and there are no more choice points then the call() method should return false.
For non-deterministic predicates, whenever failure occurs the call() method must unbind any variables that
were bound during the execution of the predicate.
   
For a typical search program the only user-defined predicate will be the last predicate in the chain of predicates.
This will typically be a predicate that simply prints or saves solution(s) found by the search.
If only the first solution is required then the predicate should simply returns true and if all solutions are required
then the predicate should return false triggering backtracking. In either case, if this is the only use of
this predicate then the continuation will be nullptr and so it's not necessary to call call_continuation() in this case.
   
For managing unbound variables, the Trail class is used to keep track of variable bindings.
Whenever a variable is bound, it should be trailed using the trail_var() method of the Trail class (which typically happens
when two terms are unified).
When backtracking occurs, the unbind_to() method of the Trail class should be called to reset variables
to their previous values.
Typically in the call() method of a predicate, the current size of the trail is saved at the start of the method and then
whenever the predicate fails, the trail is reset to that size to unbind any variables that were bound during the execution of the predicate.
   
Locally failure typically occurs when a choice is made by binding one or more variables but then a unify fails or some constraint is violated.
   
The ChoicePred::call() method is an example of a predicate that implements this contract.
It saves the trail size (top of stack) at the start of the method and then whenever a choice fails,
it resets the trail to that size to unbind any variables that were bound during the execution of the predicate.
Note that whenever make_choice() succeeds (the predicate succeeds locally) call_continuation() is called.
   
This means that a program written as a chained collection of predicates will be executed in a depth-first manner
with backtracking whenever a predicate fails. The program will therefore explore the search tree in a depth-first
manner and either stop when the first solution is found or explore the entire search tree.
   
Warning: A given instance of a predicate should not be used in multiple contexts as its continuation will be set
for one context and then used in another context. This can be avoided by creating a new instance of the predicate
for each context in which it is used.
   
Note: User programs that do repeated searches should call `unbind_to(0)` to reset all variables back to their 
initial values before starting the next search. This is important to ensure that variables are in a consistent 
state before starting a new search.
"""

class Pred:
    """ Approximates Prolog predicates. 
    """
    def __init__(self):
        self.continuation = None
        
    
    def set_continuation(self, cont):
        """Set this predicates continuation."""
        self.continuation = cont

    def last_pred(self) -> "Pred":
        """Follow the continuation chain returning the last pred in the chain."""
        if self.continuation is None:
            return self
        else:
            return self.continuation.last_pred()

    def call_init(self):
        """Initialize call.
        This method gives the programmer the opportunity to do some initialization
        when this predicate is (re)called (not when the predicate is created). This is typically
        required when implementing non-deterministic predicates as the complete set of choices
        needs to be re-enabled (see VarChoicePred for example). This is also important when
        this predicate is preceeded by a non-deterministic predicate in the call chain. Making
        a different choice in the non-deterministic predicate might require some recomputation.
        LoopBodyFactory typically requires similar considerations but call_init is not required
        for the generated predicate as it will not be recalled.
        The way the system is implemented guarantees that call_init will be called  before call
        for each predicate except the first in the call chain and those generated by LoopBodyFactory.
        call_continuation calls it before the call and the meta-predicates call it directly."""
        pass

    def call(self) -> bool:
        """ 
        To be implemented by subclasses. Returns False as a default.
        """
        return False

    def call_continuation(self) -> bool:
        """Call the continuation predicate if it exists."""
        if self.continuation is not None:
            self.continuation.call_init()
            return self.continuation.call()
        return True # None is treated as the true predicate.

    def __repr__(self):
        """For debugging."""
        return f'Pred : {self.continuation}'


class FailPred(Pred):
    """Similar to 'fail' in Prolog - typically used as a continuation
    to drive backtracking."""

    def call(self) -> bool:
        """Always fails."""
        return False

    def __repr__(self) -> str:
        return 'Fail Predicate'

# We only need one instance of Fail
fail = FailPred()

class TruePred(Pred):
    """Similar ro true in Prolog."""
    def __init__(self):
        super().__init__()

    def call(self) -> bool:
        return True

class ChoicePred(Pred):
    """This is an abstract base class. Subclasses will typically be the only predicate classes users will need to define."""
    
    def has_next(self) -> bool:
        return False

    
    def make_choice(self) -> bool:
        """Make a choice. Default return is False."""
        return False

    def test_choice(self) -> bool:
        """Test the choice. Default return is True."""
        return True
    
    def call(self) -> bool:
        size = trail.size()
        while self.has_next():
            if self.make_choice() and self.call_continuation():
                return True
            trail.unbind_to(size)
        return False
    
    def __repr__(self) -> str:
        return 'Choice Predicate'


class VarChoicePred(ChoicePred):
    """VarChoicePred is a subclass of TermChoicePred where the term of interest is a variable"""
    def __init__(self, var:Var, choices: list[Any]) -> None:
        super().__init__() 
        self.var = var
        self.choices = choices
        self.index = 0


    def has_next(self) -> bool:
        return  self.index < len(self.choices)
    
    def make_choice(self) -> bool: 
        t = self.choices[self.index]
        self.index += 1 
        return unify(self.var, t) and self.test_choice()
    

    def call_init(self):
        self.index = 0
        
    def __repr__(self):
        """For debugging."""
        return f'VarChoicePred : {self.continuation}'


def conjunct(predlst:list[Pred]) -> Pred :
    """Return a single Pred created by chaining their continuations - the
    same as a sequence of conjunctions in Prolog.
    """
    if predlst == []:
        return TruePred()
    for i in range(len(predlst)-1):
        predlst[i].last_pred().set_continuation(predlst[i+1])
    return predlst[0]


class DisjPred(Pred):
    """A Disjunction of predicates - similar to  pred1 ; pred2 ; ... , predn  in Prolog."""
    def __init__(self, preds:list[Pred]) -> None:
        super().__init__()
        self.preds = preds

    def call(self) -> bool:
        size = trail.size()    # save the current TOS
        for pred in self.preds:
            pred.call_init()
            if pred.call():
                return True
            trail.unbind_to(size)  # pred.call failed so unbind all varibles that where bound during the execution of call
        return False

    def set_continuation(self, cont):
        """Set the continuations for all disjuncts to cont"""
        self.continuation = cont
        for pred in self.preds:
            pred.last_pred().set_continuation(cont)     
        

class Once(Pred):
    """The same as Once in Prolog - all choicepoints for pred are removed."""
    def __init__(self, pred:Pred) -> None:
        super().__init__()
        self.pred = pred

    def call(self) -> bool:
        size = trail.size()
        self.pred.call_init()
        if self.pred.call() and self.call_continuation():
            # Note that if pred.call() succeeds but calling the continuation fails then 
            # alternative choices withing pred are ignored
            return True
        trail.unbind_to(size)
        return False


class NotNot(Pred):
    """The same as not-not  (i.e. \\+ \\+) in Prolog. As with Once all choicepoints for pred are removed. Also all bindings
    of variables made during the pred.call() are removed on both success and failure."""
    def __init__(self, pred:Pred) -> None:
        super().__init__()
        self.pred = pred

    def call(self) -> bool:
        size = trail.size()
        self.pred.call_init()
        if self.pred.call():
            trail.unbind_to(size)   # unbind variables on success
            return self.call_continuation()     
        trail.unbind_to(size)       # unbind variables on failure (as usual)
        return False
   
class IfThenElse(Pred):
    """The same as if-then-else (i.e. ifpred -> thenpred ; elsepred) in Prolog."""
    def __init__(self, ifpred:Pred, thenpred:Pred, elsepred:Pred) -> None:
        super().__init__()
        self.ifpred = ifpred
        self.thenpred = thenpred
        self.elsepred = elsepred

    def call(self) -> bool:
        size = trail.size()
        self.ifpred.call_init()
        if self.ifpred.call():
            self.thenpred.call_init()
            if self.thenpred.call():
                return True
            trail.unbind_to(size)
            return False
        
        trail.unbind_to(size)
        self.elsepred.call_init()
        if self.elsepred.call():
            return True
        trail.unbind_to(size)
        return False
    
    def set_continuation(self, cont:Pred | None) -> None:
        """Set the continuation for both the then and else branches. Note that ifpred is a local call and so its
        continuation stays as None."""
        self.continuation = cont
        self.thenpred.set_continuation(cont)
        self.elsepred.set_continuation(cont)


class LoopBodyFactory(Protocol):
    """A factory for creating instances of a Pred used in the Loop predicate."""
    
    def loop_continues(self, depth:int) -> bool:
        """Returns True iff the Loop predicate should continue."""
        ...

    def make_body_pred(self, depth:int) -> Pred:
        """Create an instance of the predicate to be called in the loop body."""
        ...

class Loop(Pred):
    """Creating a predicate that is like the Prolog predicate template
    like
        loop(State, Depth) :-
            loop_continues(State, Depth), !,
            body_call(State, Depth),
            Depth1 is Depth+1,
            loop(State, Depth1).
        loop(_, _).

    depth is, in the Prolog version, the depth of recursion. In this implementation it's more
    like the number of loop iterations.
    """
    def __init__(self, body_factory:LoopBodyFactory, depth:int = 0):
        super().__init__()
        self.body_factory = body_factory
        self.depth = depth

    def call(self)-> bool:
        if not self.body_factory.loop_continues(self.depth): 
            # Like the second clause of the Prolog code: loop(_, _)
            # Note that the continuation is only called when the loop exits (on success).
            return self.call_continuation() 
        # Like the recursive Prolog clause
        # Create an new instance of the body predicate
        body_pred = self.body_factory.make_body_pred(self.depth)
        # Create a new instance of the Loop predicate
        next_loop_pred = Loop(self.body_factory, self.depth+1)
        # next_loop_pred is to be called when/if next_loop_pred.call() succeeds
        body_pred.last_pred().set_continuation(next_loop_pred)
        # Pass the initial continuation of Loop down to the next level
        next_loop_pred.set_continuation(self.continuation)
        return body_pred.call()

            

    def __repr__(self):
        return f'Loop({self.body_factory}) : {self.continuation}'

