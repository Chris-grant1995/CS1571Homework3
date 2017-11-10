
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
import sys

infix_ops = '==> <== <=>'.split()

infer = []

class FolKB():
    def __init__(self, initial_clauses=[]):
        self.clauses = []  # inefficient: no indexing
        for clause in initial_clauses:
            self.tell(clause)

    def tell(self, sentence, k=0):
        if isDefClause(sentence):
            self.clauses.append(sentence)
        else:
            raise Exception("Not a definite clause: {}".format(sentence))

    def ask(self, query):
        return first(self.ask_generator(query), default=False)

    def ask_generator(self, query):
        return forwardChain(self, query)

    def retract(self, sentence):
        self.clauses.remove(sentence)

    def fetch_rules_for_goal(self, goal):
        return self.clauses

class Expr(object):
    def __init__(self, op, *args):
        self.op = str(op)
        self.args = args
    def __and__(self, rhs):
        return Expr('&', self, rhs)

    def __or__(self, rhs):
        if isinstance(rhs, Expression):
            return Expr('|', self, rhs)
        else:
            return PartialExpr(rhs, self)
    def __call__(self, *args):
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
    def __init__(self, op, lhs):
        self.op, self.lhs = op, lhs

    def __or__(self, rhs):
        return Expr(self.op, self.lhs, rhs)

    def __repr__(self):
        return "PartialExpr('{}', {})".format(self.op, self.lhs)

class defaultkeydict(collections.defaultdict):
    def __missing__(self, key):
        self[key] = result = self.default_factory(key)
        return result

def dissociate(op, args):
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
    return dissociate('&', [s])

def isSym(s):
    return isinstance(s, str) and s[:1].isalpha()

def isDefClause(s):
    if isSym(s.op):
        return True
    elif s.op == '==>':
        antecedent, consequent = s.args
        return (isSym(consequent.op) and
                all(isSym(arg.op) for arg in conjuncts(antecedent)))
    else:
        return False


def forwardChain(KB, alpha):
    
    #Forward Chaining, based on figure 9.3 from the book
    kbCon = list({c for clause in KB.clauses for c in constants(clause)})

    def enum_subst(p):
        query_vars = list({v for clause in p for v in variables(clause)})
        # print(query_vars, " ", p)
        for assignment_list in itertools.product(kbCon, repeat=len(query_vars)):
            theta = {x: y for x, y in zip(query_vars, assignment_list)}
            # print("THETA: ",theta)
            yield theta

    # check if we can answer without new inferences
    for q in KB.clauses:
        phi = unify(q, alpha)
        # print(q, " ", alpha)
        if phi is not None:
            yield phi
    # print("WHILE LOOP")
    while True:
        # print("TESTING2")
        new = []
        for rule in KB.clauses:
            p, q = parseDefClause(rule)
            #print(rule," ",p , " ", q)
            for theta in enum_subst(p):
                if set(subst(theta, p)).issubset(set(KB.clauses)):
                    q_ = subst(theta, q)
                    if all([unify(x, q_) is None for x in KB.clauses + new]):
                        new.append(q_)
                        # print(q_)
                        # print(q_, " ", alpha)
                        phi = unify(q_, alpha)
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

def isVarSym(s):
    return isSym(s) and s[0].islower()

def subst(s, x):
    if isinstance(x, list):
        return [subst(s, xi) for xi in x]
    elif isinstance(x, tuple):
        return tuple([subst(s, xi) for xi in x])
    elif not isinstance(x, Expr):
        return x
    elif isVarSym(x.op):
        return s.get(x, x)
    else:
        return Expr(x.op, *[subst(s, arg) for arg in x.args])

def parseDefClause(s):
    assert isDefClause(s)
    if isSym(s.op):
        return [], s
    else:
        antecedent, consequent = s.args
        return conjuncts(antecedent), consequent

def constants(x):
    if not isinstance(x, Expr):
        return set()
    elif isPropSym(x.op) and not x.args:
        return {x}
    else:
        return {symbol for arg in x.args for symbol in constants(arg)}

def isPropSym(s):
    return isSym(s) and s[0].isupper()

def variables(s):
    return {x for x in subexpressions(s) if is_variable(x)}

def subexpressions(x):
    yield x
    if isinstance(x, Expr):
        for arg in x.args:
            yield from subexpressions(arg)

def is_variable(x):
    return isinstance(x, Expr) and not x.args and x.op[0].islower()

def unify(f1,f2):
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


def expr(x):
    if isinstance(x, str):
        return eval(expr_handle_infix_ops(x), defaultkeydict(Symbol))
    else:
        return x

def expr_handle_infix_ops(x):
    for op in infix_ops:
        x = x.replace(op, '|' + repr(op) + '|')
    return x

def Symbol(name):
    return Expr(name)

def first(iterable, default=None):
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
    return isinstance(x, collections.abc.Sequence)

Number = (int, float, complex)
Expression = (Expr, Number)

def parse_input(l):
    #L is a list representation of the file

    p = l.pop()
    p = p.replace("PROVE ", "")


    # Have to repalce ^ and -> because expr uses & and ==>
    for i in range(0,len(l)):
        s = l[i]
        s = s.replace("^", "&")
        s = s.replace("->", "==>")
        l[i] = s
    return (l,p)


def main():
    
    f = sys.argv[1]
    file = open(f)
    l = file.readlines()

    l, p = parse_input(l)

    m = map(expr, l)
    kb2 = FolKB(m)

    prove = expr(p)

    # # # print(kb2.clauses)
    # print(kb2.IFCclauses)
    print(kb2.ask(prove) != False)
    for i in infer:
        print(i)

main()