# A module for searching and constraint programming using Prolog ideas

There are several Python constraint solvers but it appears that they are tailored for specific domains such as integers. The aim of this module is to be quite generic and support searching and constraint solving over a wide range of domains including working with symbolic state and constraints. This module relies quite heavily on ideas from Prolog such as Prolog like variables, environments and trailing to support backtracking search.

Being more generic means that the programmer may have more work to do that in other constraint solvers.

The top-level docstring in `pl_search/pl_search.py` gives details of the module and `examples/send_more_money.py` is an example of the use of this module. Further `test/test1.py` has a collection of various simple searches.

## Installation

The simplest option is a direct installation from github:

`python3 -m pip install -U git+https://github.com/pjritee/pl_search.git`

The other option is to clone the repository and then, from the top-level of the cloned repository, do a pip install:

`python3 -m pip install -U .`

## Example Usage

To illustrate the use of the module we work through a constraint handling solution to finding NxN magic squares.
The program described here is supplied in `examples/magic_squares.py`.

The first step is to import the module:

```python
import pl_search as pls
```

We first initialise some constants (for a 3x3 magic square) .

```python
N = 3
N2 = N**2

# each row, column, diagonal sum
SUM = (N * (N2 + 1))//2

# The square to be filled in with the numbers 1,2,3,.. N**2
CHOICES = set(range(1,N2+1))

```
The approach is to create a NxN array containing distinct variables and then use constraint programming and backtrack search to find appropriate values for these variables.

We could use `pls.Var()` but given we need to check that the variables
have to have disjoint values it's better to create a subclass as follows.

```python
class MSVar(pls.Var):

    def set_disjoint(self, disjoints):
        self.disjoints = disjoints

    def bind(self, n):
        if n in self.disjoints or n not in CHOICES:
            return False
        return super().bind(n)

    def get_choices(self):
        known_disjoints = {pls.engine.dereference(n) for n in self.disjoints
                           if not pls.var(n)}
        return CHOICES.difference(known_disjoints)
```
By checking the value for the variable is a valid choice in `bind` we guarantee that the choice for the variable value satisfies the disjointness constraint and comes from the required set. We use `set_disjoint` to set the disjoint list to be all the variables (after all the variables have been created). Later when we start searching we will use `get_choices` to  an iterator to be used to backtrack through possible choices in the search predicate.

We can then create a list of variables, set their disjoints attribute and create a 3x3 array as follows.

```python
all_vars = [MSVar() for _ in range(N2)]
for v in all_vars:
    v.set_disjoint(all_vars)
square = [all_vars[i:i+N] for i in range(0, N2, N)]

```
If we do that in the interpreter and then look at the value of square we get
```python
[[X01, X02, X03], [X04, X05, X06], [X07, X08, X09]]
```
where `X01` etc. are the string representations of the variables.

The next step is to consider how we represent the row, column and diagonal sum constraints. The approach taken here is to represent a constraint like

`X01 + X02 + X03 = SUM`

as the pair

`([X01,X02, X03], SUM)`.

As we search for a solution, variables get bound to numbers and the constraints need to be checked and deductions made where possible. There are two approaches we could take. The first is to leave the constraints unchanged and check them and do deductions as variables get bound. The other approach is to simplify the constraints as we proceed. For this simple problem the first approach is viable but as the size and complexity of the constraints increase this approach will become very inefficient. We will take the second approach but we need to be careful because the simplifications that can be made are based on choices for variables and so when we backtrack we also have to undo simplifications to constraints. This can be managed using `UpdatableVar` to implement a form of backtrackable assignment.

Again, we have two approaches. The first is to have one `UpdatableVar` to store the entire list of constraints and the other is to use an `UpdatableVar` for each constraint. For the first approach, when we simplify the constraints we need to make a new list containing the update constraints.
This gives us a chance to remove solved constraints. The downside of this approach is that we end up with lots of near copies of the constraints list as we move forward in the search. The downside of the second approach is we don't get a chance to remove solved constraints.

We take the second approach and define

```python
def generate_constraints(square):
    """Return the row, column and diagonal sum constraints."""
    constraints = \
        [pls.UpdatableVar(([square[i][j] for i in range(N)], SUM))
         for j in range(N)] + \
        [pls.UpdatableVar(([square[j][i] for i in range(N)], SUM))
         for j in range(N)] + \
        [pls.UpdatableVar(([square[i][i] for i in range(N)], SUM))] + \
        [pls.UpdatableVar(([square[i][N-1-i] for i in range(N)], SUM))]
    return constraints
```
Continuing in the interpreter we get

```
>>> generate_constraints(square)
[UpdatableVar(([X01, X04, X07], 15)), UpdatableVar(([X02, X05, X08], 15)), UpdatableVar(([X03, X06, X09], 15)), UpdatableVar(([X01, X02, X03], 15)), UpdatableVar(([X04, X05, X06], 15)), UpdatableVar(([X07, X08, X09], 15)), UpdatableVar(([X01, X05, X09], 15)), UpdatableVar(([X03, X05, X07], 15))]

```
Now that we have generated the constraints we need to be able to test them and carry out any possible deductions and so we give the following definition.

```python
def check_constraints(constraints):
    """ check and simplify constraints.
    Return True iff constraints are satisfiable.
    """
    progress = True
    while progress:
        # keep repeating until no more 'useful' simplifications are possible
        progress = False        
        for c in constraints:
            lhs, rhs = c.value
            if lhs == [] and rhs == 0:
                # solved constraint
                continue
            var_lhs = [x for x in lhs if  pls.var(x)]
            ground_lhs = [pls.engine.dereference(x) for x in lhs
                          if not x in var_lhs]
            new_rhs = rhs - sum(ground_lhs)
            if var_lhs == []:
                if new_rhs == 0:
                    # newly solved constraint
                    pls.engine.unify(c, ([], 0))
                return False
            if new_rhs < 0:
                # no solution is possible
                return False
            if len(var_lhs) == 1: # constraint is Var = new_rhs
                progress = True
                if not pls.engine.unify(var_lhs[0], new_rhs):
                    # this fails when new_rhs is too big
                    # or is already taken
                    return False
                # newly solved constraint
                pls.engine.unify(c, ([], 0))
            elif new_rhs != rhs:
                # the constraint is simplified
                progress = True
                pls.engine.unify(c, (var_lhs, new_rhs))
    return True

```
`pl_search` contains an `Engine` class and an instance `engine` of that class.
The `engine` object is responsible for executing predicates, including managing backtracking. Notice that we use `pls.engine.unify` rather than `bind`
as `bind` does not trail the variable and so the binding would not be undone on backtracking. We also use `pls.engine.dereference(x)` although in this case we could have used `x.deref()` because we know x is a variable (that might be bound). In general it's better to use `pls.engine.dereference` as this also works as expected when the argument is not a variable.

Note, above, that `c` is an `UpdatableVar` and `c.value` is the current values for `c` and `pls.engine.unify(c, (var_lhs, new_rhs))` assigns this new value to `c`. The old value of `c` is trailed so that, on backtracking, the old value will be restored.

We can test this in the interpreter as, for example:

```python
>>> pls.engine.unify(all_vars[0], 8)
True
>>> pls.engine.unify(all_vars[1], 1)
True
>>> check_constraints(constraints)
True
>>> constraints
[UpdatableVar(([X04, X07], 7)), UpdatableVar(([X05, X08], 14)), UpdatableVar(([X06, X09], 9)), UpdatableVar(([], 0)), UpdatableVar(([X04, X05, X06], 15)), UpdatableVar(([X07, X08, X09], 15)), UpdatableVar(([X05, X09], 7)), UpdatableVar(([X05, X07], 9))]
>>> all_vars
[8, 1, 6, X04, X05, X06, X07, X08, X09]
```
Notice that we were able to deduce `X03` must be 6 and that several of the constraints have been simplified.

Now that we have the basic machinery we are ready to define predicates to carry out the search.

When we execute (call) a predicate there are two possible outcomes. One is that the call fails and the other is that it succeeds. In both cases `engine` will carry out a complete reset - equivalent to backtracking to before the call to the predicate. This means that, even on success, the variable bindings
will be undone and so, in order to get solutions we need to either print them
or deal with solutions some other way inside a predicate - for example store them away, send them as a message or put them on a queue.

Below is a predicate definition that prints the array when called.

```python  
class Print(pls.DetPred):
    """Pretty print the supplied array."""

    def __init__(self, array):
        self.array = array

    def initialize_call(self):
        for j in range(N):
            print(''.join(f'{str(pls.engine.dereference(self.array[j][i])):>5}'
                           for i in range(N)))
        print()
```
`Print` is declared as a `DetPred` which means it is deterministic - it has exactly one solution. We are required to define `initialize_call` that gets executed as soon as a `Print` predicate is called.

We can test this in the interpreter as follows (continuing on from the earlier interpreter interaction)

```
>>> pls.engine.execute(Print(square))
    8    1    6
  X04  X05  X06
  X07  X08  X09
True
```

Now we are ready to write the code that will carry out the search.

Pseudo-code for this kind of problem is something like
```
while there are variables left
    pick a variable
    calculate the possible choices for the variable
    make a choice for the variable
    if the constraints are satisfiable then continue
    else backtrack and make another choice
```
This strategy can be implemented using the `Loop` meta-predicate. This takes a single argument that is a subclass of `LoopBodyFactory` with definitions for `loop_continues` (which returns True if the loop should continue) and `make_body_pred` that generates a predicate to be called in the body of the loop.

Suitable definitions are given below (including `get_best_var`)

```python
def get_best_var(all_vars):
    """Return the first remaining variable in all_vars else return None if
    there are no more variables."""
    for v in all_vars:
        if pls.var(v):
            return v
    return None

class BodyPred(pls.Pred):
    def __init__(self, constrains, all_vars, best_var):
        self.constraints = constraints
        self.all_vars = all_vars
        self.best_var = best_var

    def initialize_call(self):
        #required method and self.choice_iterator must be given a value
        self.choice_iterator = \
            pls.VarChoiceIterator(self.best_var, self.best_var.get_choices())
        return True

    def test_choice(self):
        # We need to check the constraints and carry out deductions so this
        # method is required
        return check_constraints(self.constraints)

class MSFactory(pls.LoopBodyFactory):

    def __init__(self, constraints, all_vars):
        self.constraints =  constraints
        self.all_vars = all_vars

    def loop_continues(self):
        self.best_var = get_best_var(self.all_vars)
        return self.best_var is not None

    def make_body_pred(self) -> pls.Pred:
        return BodyPred(self.constraints, self.all_vars, self.best_var)

```
Here we take the simplest approach and choose the first remaining variable in `all_vars` for `get_best_var` but we probably should have chosen a variable from a constraint with the smallest left hand side.

Now we can carry out the search. If we just want the first solution we can try:
```
pls.engine.execute(pls.conjunct([pls.Loop(MSFactory(constraints, all_vars)), Print(square)])
```
and we will get the output
```
    2    7    6
    9    5    1
    4    3    8
```
On the other hand, if we want all solutions we can try:
```
pls.engine.execute(pls.conjunct([pls.Loop(MSFactory(constraints, all_vars)), Print(square), pls.fail])
```
The meta-predicate `pls.conjunct` conjoins a list of predicates into one predicate by chaining the predicates continuations and is like conjunction in Prolog. The builtin predicate `pls.fail` simply fails, triggering backtracking (like fail in Prolog).

For this problem we use the builtin ```VarChoiceIterator``` because we simply need to try each choice for a given variable. In more complicated situations the programmer might need to define their own choice iterator.

As an example consider the case where we have a list of variables and we want the choices to be all possible sublists (without order) of some list of values. In ```test/test1.py``` we define the following.

```python
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

```
In the above example we still use ```VarChoice``` as we are simply unifying two terms. In an even more sophisticated example, each choice might mean the addition of some sort of constraint. In that case we would need to define a choice iterator class  as well as a Choice class for adding the constraint.

## Version History

* 1.7
  - Make choice iteration more generic by having choice iterators generate Choice objects that are responsible for making the choice.
  - Update the examples and README to use these choice iterators.
* 1.6
  - Add sections on installation and example use to README
* 1.5
  - Improve efficiency of send_more_money example by computing best_var only once per loop iteration
  - add a check to test1.py to determine if output is OK
* 1.4
  - Add SemiDetPred (semi-deterministic predicate)
* 1.3
  - Add DetPred (deterministic predicate)
  - Update top-level docstring
* 1.2
  - Improve efficiency of Loop
* 1.1
  - Add Disjunction
  - Fix bug - not untrailing on execute success
* 1.0
  - Major rewrite of Pred to simplify the programmers task.
  - The addition of predicate conjunction, looping and once
  - Re-factoring of Engine.
* 0.1
  - Initial release.
