# A module for searching and constraint programming using Prolog ideas

There are several Python constraint solvers but it appears that they are tailored for specific domains such as integers. The aim of this module is to be quite generic and support searching and constraint solving over a wide range of domains including working with symbolic state and constraints. This module relies quite heavily on ideas from Prolog such as Prolog like variables, environments and trailing to support backtracking search.

Being more generic means that the programmer will have more work to do that in other constraint solvers.

The top-level docstring in pl_search/pl_search.py gives details of the module and examples/send_more_money.py is an example of the use of this module. Further test/test1.py has a collection of various simple searches.

## Version History

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
