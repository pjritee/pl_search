
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
Support for Prolog like variables.
"""

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
            val_value = val.value
            if val_value is None:
                # unbound variabe
                return val
            if not isinstance(val_value, Var): 
                # end of reference chain is a non-var value
                return val_value
            # step down ref chain
            val = val_value

    def bind(self, val:object):
        """Bind the variable to the supplied value."""
        # check unbound
        #assert isinstance(self, UpdatableVar) or self.value is None
        # check we don't get a loop
        #assert not (isinstance(val, Var) and val.deref() == self)
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
        other_is_var = isinstance(other, Var)
        if other_is_var:
            other = other.deref()
            other_is_var = isinstance(other, Var)
        v_is_var = isinstance(v, Var)
        if other_is_var:
            return v_is_var and v.id_ == other.id_
        return not v_is_var and v == other

    def __lt__(self, other:object):
        """Like the @< test in Prolog."""
        # deref v
        v = self.deref()
        other_is_var = isinstance(other, Var)
        if other_is_var:
            other = other.deref()
            other_is_var = isinstance(other, Var)
        v_is_var = isinstance(v, Var)
        if other_is_var:
            # if both vars then use id's
            return  v_is_var and v.id_ < other.id_
        # this can only succeed if both v and i (deref'ed) are
        # equal as Python terms
        return not v_is_var and v < other

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


