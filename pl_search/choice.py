
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
Support for defining choices and choice iterators.
"""

from typing import Protocol
from .engine import *

class Choice(Protocol):
    """Creating choice instances - the return of a choice iterator."""

    def apply_choice(self) -> bool:
        """Apply the choice returning True iff the choice is OK."""

class VarChoiceIterator:
    """Create an iterator for a variable and it's possible choices. """

    def __init__(self, var_, choices):
        self.var_ = var_
        self.choices = iter(choices)

    def __iter__(self):
        return self

    def __next__(self):
        return VarChoice(self.var_, next(self.choices))


class VarChoice(Choice):
    """A particular choice (next) from a VarChoiceIterator."""

    def __init__(self, var_, choice):
        self.var_ = var_
        self.choice = choice
        
    def apply_choice(self):
        return engine.unify(self.var_, self.choice)
    

