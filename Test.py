
import itertools
from collections import defaultdict
import bisect
import collections
import collections.abc
import operator
import os.path
import random
import math
import functools
import time

infix_ops = '==> <== <=>'.split()

infer = []

class FolKB():
    """A knowledge base consisting of first-order definite clauses.
    >>> kb0 = FolKB([expr('Farmer(Mac)'), expr('Rabbit(Pete)'),
    ...              expr('(Rabbit(r) & Farmer(f)) ==> Hates(f, r)')])
    >>> kb0.tell(expr('Rabbit(Flopsie)'))
    >>> kb0.retract(expr('Rabbit(Pete)'))
    >>> kb0.ask(expr('Hates(Mac, x)'))[x]
    Flopsie
    >>> kb0.ask(expr('Wife(Pete, x)'))
    False
    """

    def __init__(self, initial_clauses=[]):
        self.clauses = []  # inefficient: no indexing
        for clause in initial_clauses:
            self.tell(clause)

    def tell(self, sentence):
        if is_definite_clause(sentence):
            self.clauses.append(sentence)
        else:
            raise Exception("Not a definite clause: {}".format(sentence))

    def ask(self, query):
        """Return a substitution that makes the query true, or, failing that, return False."""
        return first(self.ask_generator(query), default=False)

    def ask_generator(self, query):
        return fol_fc_ask(self, query)

    def retract(self, sentence):
        self.clauses.remove(sentence)

    def fetch_rules_for_goal(self, goal):
        return self.clauses

class Expr(object):
    """A mathematical expression with an operator and 0 or more arguments.
    op is a str like '+' or 'sin'; args are Expressions.
    Expr('x') or Symbol('x') creates a symbol (a nullary Expr).
    Expr('-', x) creates a unary; Expr('+', x, 1) creates a binary."""

    def __init__(self, op, *args):
        self.op = str(op)
        self.args = args

    # Operator overloads
    def __neg__(self):
        return Expr('-', self)

    def __pos__(self):
        return Expr('+', self)

    def __invert__(self):
        return Expr('~', self)

    def __add__(self, rhs):
        return Expr('+', self, rhs)

    def __sub__(self, rhs):
        return Expr('-', self, rhs)

    def __mul__(self, rhs):
        return Expr('*', self, rhs)

    def __pow__(self, rhs):
        return Expr('**', self, rhs)

    def __mod__(self, rhs):
        return Expr('%', self, rhs)

    def __and__(self, rhs):
        return Expr('&', self, rhs)

    def __xor__(self, rhs):
        return Expr('^', self, rhs)

    def __rshift__(self, rhs):
        return Expr('>>', self, rhs)

    def __lshift__(self, rhs):
        return Expr('<<', self, rhs)

    def __truediv__(self, rhs):
        return Expr('/', self, rhs)

    def __floordiv__(self, rhs):
        return Expr('//', self, rhs)

    def __matmul__(self, rhs):
        return Expr('@', self, rhs)

    def __or__(self, rhs):
        """Allow both P | Q, and P |'==>'| Q."""
        if isinstance(rhs, Expression):
            return Expr('|', self, rhs)
        else:
            return PartialExpr(rhs, self)

    # Reverse operator overloads
    def __radd__(self, lhs):
        return Expr('+', lhs, self)

    def __rsub__(self, lhs):
        return Expr('-', lhs, self)

    def __rmul__(self, lhs):
        return Expr('*', lhs, self)

    def __rdiv__(self, lhs):
        return Expr('/', lhs, self)

    def __rpow__(self, lhs):
        return Expr('**', lhs, self)

    def __rmod__(self, lhs):
        return Expr('%', lhs, self)

    def __rand__(self, lhs):
        return Expr('&', lhs, self)

    def __rxor__(self, lhs):
        return Expr('^', lhs, self)

    def __ror__(self, lhs):
        return Expr('|', lhs, self)

    def __rrshift__(self, lhs):
        return Expr('>>', lhs, self)

    def __rlshift__(self, lhs):
        return Expr('<<', lhs, self)

    def __rtruediv__(self, lhs):
        return Expr('/', lhs, self)

    def __rfloordiv__(self, lhs):
        return Expr('//', lhs, self)

    def __rmatmul__(self, lhs):
        return Expr('@', lhs, self)

    def __call__(self, *args):
        "Call: if 'f' is a Symbol, then f(0) == Expr('f', 0)."
        if self.args:
            raise ValueError('can only do a call for a Symbol, not an Expr')
        else:
            return Expr(self.op, *args)

    # Equality and repr
    def __eq__(self, other):
        "'x == y' evaluates to True or False; does not build an Expr."
        return (isinstance(other, Expr)
                and self.op == other.op
                and self.args == other.args)

    def __hash__(self): return hash(self.op) ^ hash(self.args)

    def __repr__(self):
        op = self.op
        args = [str(arg) for arg in self.args]
        if op.isidentifier():       # f(x) or f(x, y)
            return '{}({})'.format(op, ', '.join(args)) if args else op
        elif len(args) == 1:        # -x or -(x + 1)
            return op + args[0]
        else:                       # (x - y)
            opp = (' ' + op + ' ')
            return '(' + opp.join(args) + ')'

class PartialExpr:
    """Given 'P |'==>'| Q, first form PartialExpr('==>', P), then combine with Q."""
    def __init__(self, op, lhs):
        self.op, self.lhs = op, lhs

    def __or__(self, rhs):
        return Expr(self.op, self.lhs, rhs)

    def __repr__(self):
        return "PartialExpr('{}', {})".format(self.op, self.lhs)

class defaultkeydict(collections.defaultdict):
    """Like defaultdict, but the default_factory is a function of the key.
    >>> d = defaultkeydict(len); d['four']
    4
    """
    def __missing__(self, key):
        self[key] = result = self.default_factory(key)
        return result

def dissociate(op, args):
    """Given an associative op, return a flattened list result such
    that Expr(op, *result) means the same as Expr(op, *args)."""
    result = []

    def collect(subargs):
        for arg in subargs:
            if arg.op == op:
                collect(arg.args)
            else:
                result.append(arg)
    collect(args)
    return result

def conjuncts(s):
    """Return a list of the conjuncts in the sentence s.
    >>> conjuncts(A & B)
    [A, B]
    >>> conjuncts(A | B)
    [(A | B)]
    """
    return dissociate('&', [s])

def is_symbol(s):
    """A string s is a symbol if it starts with an alphabetic char."""
    return isinstance(s, str) and s[:1].isalpha()

def is_definite_clause(s):
    """Returns True for exprs s of the form A & B & ... & C ==> D,
    where all literals are positive.  In clause form, this is
    ~A | ~B | ... | ~C | D, where exactly one clause is positive.
    >>> is_definite_clause(expr('Farmer(Mac)'))
    True
    """

    if is_symbol(s.op):
        return True
    elif s.op == '==>':
        antecedent, consequent = s.args
        return (is_symbol(consequent.op) and
                all(is_symbol(arg.op) for arg in conjuncts(antecedent)))
    else:
        return False


def fol_fc_ask(KB, alpha):
    """A simple forward-chaining algorithm. [Figure 9.3]"""
    # TODO: Improve efficiency
    kb_consts = list({c for clause in KB.clauses for c in constant_symbols(clause)})

    def enum_subst(p):
        query_vars = list({v for clause in p for v in variables(clause)})
        for assignment_list in itertools.product(kb_consts, repeat=len(query_vars)):
            theta = {x: y for x, y in zip(query_vars, assignment_list)}
            yield theta

    # check if we can answer without new inferences
    for q in KB.clauses:
        phi = unify(q, alpha, {})
        # print(q, " ", alpha)
        if phi is not None:
            yield phi
    # print("WHILE LOOP")
    while True:
        # print("TESTING2")
        new = []
        for rule in KB.clauses:
            p, q = parse_definite_clause(rule)
            # print(p , " ", q)
            for theta in enum_subst(p):
                if set(subst(theta, p)).issubset(set(KB.clauses)):
                    q_ = subst(theta, q)
                    if all([unify(x, q_, {}) is None for x in KB.clauses + new]):
                        new.append(q_)
                        # print(q_, " ", alpha)
                        phi = unify(q_, alpha, {})
                        # print("PHI: ", phi)
                        if phi is not None:
                            # print("Test")
                            # print(new)
                            infer.append(new[0])
                            yield phi
        if not new:
            break
        for clause in new:
            # print("Clause: ", clause)
            infer.append(clause)
            KB.tell(clause)
    # print("TESTING")
    return None

def is_var_symbol(s):
    """A logic variable symbol is an initial-lowercase string."""
    return is_symbol(s) and s[0].islower()

def subst(s, x):
    """Substitute the substitution s into the expression x.
    >>> subst({x: 42, y:0}, F(x) + y)
    (F(42) + 0)
    """
    if isinstance(x, list):
        return [subst(s, xi) for xi in x]
    elif isinstance(x, tuple):
        return tuple([subst(s, xi) for xi in x])
    elif not isinstance(x, Expr):
        return x
    elif is_var_symbol(x.op):
        return s.get(x, x)
    else:
        return Expr(x.op, *[subst(s, arg) for arg in x.args])

def parse_definite_clause(s):
    """Return the antecedents and the consequent of a definite clause."""
    assert is_definite_clause(s)
    if is_symbol(s.op):
        return [], s
    else:
        antecedent, consequent = s.args
        return conjuncts(antecedent), consequent

def constant_symbols(x):
    """Return the set of all constant symbols in x."""
    if not isinstance(x, Expr):
        return set()
    elif is_prop_symbol(x.op) and not x.args:
        return {x}
    else:
        return {symbol for arg in x.args for symbol in constant_symbols(arg)}

def is_prop_symbol(s):
    """A proposition logic symbol is an initial-uppercase string."""
    return is_symbol(s) and s[0].isupper()

def variables(s):
    """Return a set of the variables in expression s.
    >>> variables(expr('F(x, x) & G(x, y) & H(y, z) & R(A, z, 2)')) == {x, y, z}
    True
    """
    return {x for x in subexpressions(s) if is_variable(x)}

def subexpressions(x):
    """Yield the subexpressions of an Expression (including x itself)."""
    yield x
    if isinstance(x, Expr):
        for arg in x.args:
            yield from subexpressions(arg)

def is_variable(x):
    """A variable is an Expr with no args and a lowercase symbol as the op."""
    return isinstance(x, Expr) and not x.args and x.op[0].islower()

def unify(f1,f2,s={}):
    # print(f1)
    # print(f2)
    subs = {}
    # print(f1.args == f2.args)
    # print(f1.op, " ", f2.op)
    # print(f1, len(f1.args), " ", f2, len(f2.args))

    if len(f1.args) != len(f2.args):
        return None

    if f1.op != f2.op:
        return None
    for i in range(0,len(f1.args)):
        a1 = f1.args[i]
        a2 = f2.args[i]
        if is_variable(a1):
            if a1 in subs.keys() and subs[a1] != a2:
                return None
            else:
                subs[a1] = a2
        elif a1 != a2:
            return None
        
    return subs

# def unify(x, y, s={}):
#     """Unify expressions x,y with substitution s; return a substitution that
#     would make x,y equal, or None if x,y can not unify. x and y can be
#     variables (e.g. Expr('x')), constants, lists, or Exprs. [Figure 9.1]"""
#     if s is None:
#         return None
#     elif x == y:
#         return s
#     elif is_variable(x):
#         return unify_var(x, y, s)
#     elif is_variable(y):
#         return unify_var(y, x, s)
#     elif isinstance(x, Expr) and isinstance(y, Expr):
#         return unify(x.args, y.args, unify(x.op, y.op, s))
#     elif isinstance(x, str) or isinstance(y, str):
#         return None
#     elif issequence(x) and issequence(y) and len(x) == len(y):
#         if not x:
#             print(s)
#             return s
#         r = unify(x[1:], y[1:], unify(x[0], y[0], s))
#         return r
#     else:
#         return None

def unify_var(var, x, s):
    if var in s:
        return unify(s[var], x, s)
    elif x in s:
        return unify(var, s[x], s)
    elif occur_check(var, x, s):
        return None
    else:
        return extend(s, var, x)

def extend(s, var, val):
    """Copy the substitution s and extend it by setting var to val; return copy."""
    s2 = s.copy()
    s2[var] = val
    return s2


def occur_check(var, x, s):
    """Return true if variable var occurs anywhere in x
    (or in subst(s, x), if s has a binding for x)."""
    if var == x:
        return True
    elif is_variable(x) and x in s:
        return occur_check(var, s[x], s)
    elif isinstance(x, Expr):
        return (occur_check(var, x.op, s) or
                occur_check(var, x.args, s))
    elif isinstance(x, (list, tuple)):
        return first(e for e in x if occur_check(var, e, s))
    else:
        return False

def expr(x):
    """Shortcut to create an Expression. x is a str in which:
    - identifiers are automatically defined as Symbols.
    - ==> is treated as an infix |'==>'|, as are <== and <=>.
    If x is already an Expression, it is returned unchanged. Example:
    >>> expr('P & Q ==> Q')
    ((P & Q) ==> Q)
    """
    if isinstance(x, str):
        return eval(expr_handle_infix_ops(x), defaultkeydict(Symbol))
    else:
        return x

def expr_handle_infix_ops(x):
    """Given a str, return a new str with ==> replaced by |'==>'|, etc.
    >>> expr_handle_infix_ops('P ==> Q')
    "P |'==>'| Q"
    """
    for op in infix_ops:
        x = x.replace(op, '|' + repr(op) + '|')
    return x

def Symbol(name):
    """A Symbol is just an Expr with no args."""
    return Expr(name)

def first(iterable, default=None):
    """Return the first element of an iterable or the next element of a generator; or default."""
    try:
        # return iterable[0]
        r = iterable[1]
        # print(r)
        return r
    except IndexError:
        return default
    except TypeError:
        return next(iterable, default)

def issequence(x):
    """Is x a sequence?"""
    return isinstance(x, collections.abc.Sequence)

Number = (int, float, complex)
Expression = (Expr, Number)

l = ['Instrument(y)  &  Musician(x)  ==>  Plays(x,y)',
    "Instrument(y)  &  Plays(x,y)  ==>  NotToneDeaf(x)",
     "Musician(Grace)",
    "Instrument(I1)"]

l = [
    "American(x)  &  Weapon(y)  &  Nation(z)  &  Hostile(z)  &  Sells(x,z,y)  ==>  Criminal(x)",
    "Owns(Nono,x)  &  Missile(x)  ==>  Sells(West,Nono,x)",
    "Missile(x)  ==>  Weapon(x)",
    "Enemy(x,America)  ==>  Hostile(x)",
    "American(West)",
    "Nation(Nono)",
    "Enemy(Nono,America)",
    "Owns(Nono,M1)",
    "Missile(M1)",
    "Nation(America)"
]

m = map(expr, l)
kb2 = FolKB(m)



prove = expr("NotToneDeaf(Grace)")
prove = expr("Criminal(West)")

# # # print(kb2.clauses)

print(kb2.ask(prove) != None)
for i in infer:
    print(i)

# print(kb2.clauses)



# exp1 = expr("Owns(x,y)")
# exp2 = expr("Owns(Nono,M1)")
# r = unify2(exp1,exp2)
# print(r)