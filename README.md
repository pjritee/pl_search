# A module for searching and constraint programming using Prolog ideas

There are several Python constraint solvers but it appears that they are tailored for specific domains such as integers. The aim of this module is to be quite generic and support searching and constraint solving over a wide range of domains including working with symbolic state and constraints. This module relies quite heavily on ideas from Prolog such as Prolog like variables, environments and trailing to support backtracking search.

Being more generic means that the programmer will have more work to do that in other constraint solvers.

The top-level docstring in pl_search/pl_search.py gives details of the implementation and examples/send_more_money.py is an example of the use of this module.