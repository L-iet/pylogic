# Friday, Feb 23, 2024, 1:37 AM PT
I started coding around 12:12 AM. I'm trying to restrcuture the code into packages.

I found out I can't use circular imports even with packages in Python, if I want to use values at the top-level of modules. Most of these values are for typing.
I'm consdiering using type-stubs.

# Saturday, Mar 02, 2024, 4:47 AM PT
Begin session at 4:47am.

6:26am: end session. I've managed to organise the code into reasonable directories.
There are still type errors for now, but these will be resolved eventually. They mainly deal with imports being done at the right places and using the right aliases, especially for SympyExpression.

# Monday, Mar 04, 2024, 5:42 AM PT
I need to do two main things at this point:
- fix type errors
- Remove argValueTypes and argValues from propositions

I'm inclined to start on the second task first as I think it'll clean up the code.

# Monday, Mar 04, 2024, 6:30 AM PT
Begin session around 5:45am. I forgot to make the initial commit.

9:47am: end session. I've modified the following files:

- pylogic/proposition/proposition.py
- pylogic/proposition/quantified/exists.py
- pylogic/proposition/quantified/forall.py
- pylogic/proposition/quantified/quantified.py
- pylogic/proposition/relation/contains.py
- pylogic/proposition/relation/equals.py
- pylogic/set/sets.py

- pylogic/variable.py

I've fixed types in all except contains.py for now. Removed argValueTypes and argValues. Introduced Variable which also subclasses sp.Basic.

# Saturday, Apr 06, 2024, 12:30 PM PT
Begin session around 12:30pm.

1:34pm I'm trying to add axioms/theorems to the system. I need sympy to not evaluate certain expressions. Found this: https://github-wiki-see.page/m/sympy/sympy/wiki/Unevaluated-Expressions

So we can use syntax like
```python
with evaluate(False):
...     print(Integer(3)*4)
```
or
```python
sympify('3*4', evaluate=False)
```

# Saturday, Apr 08, 2024, 6:18am PT
Begin session.

8:32am: end session. I added some work on sets and containment, and started a file
called divisible.py for some theorems related to divisibility.

# Monday, Apr 15, 2024, 8:00pm PT
Begin session. (Began earlier but forgot to log in) I'm adding proof search for the classes `Proposition`, `Forall`, `Exists`, `And`, `Or`, `Not`, `Implies`.

11:21pm: end session. Added starting code for the proof search.

# Tuesday Apr 16, 2024, 12:49am PT
Begin session.

2:53am Need to add code to store generated proposiions and use them in later infernces

# Tuesday Apr 16, 2024, 4:11pm PT
Begin session.

For some tactics, calling it on `p` returns `p`, but proven.
For other tactics, calling it on `p` returns a different proposition that is proven.

4:53pm: end session. Will merge functions for tactics with same number of arguments.
Also differentiate between the tactic types above. Separate functions to call tactics that need
to be called from the target.

# Tuesday Apr 16, 2024, 5:51pm PT
Begin session. Will try to see the overall structure of each search function before merging.

7:54pm: end session. The structures of quantified_modus_ponens, modus_ponens and hypothetical_syllogism search
are the same, so will later be merging them.
TODO: Need to check my change of `is_special_case_of` tactic. Consider the case
```
forall x: P(1, 2, 3)
```
to prove `P(x,y,z)`. The variables in the `forall` should get set to the values in the given prop,
but not vice versa.

# Tuesday Apr 16, 2024, 9:20pm PT
Begin session.

10:12pm: break session.

# Wednesday Apr 17, 2024, 9:51am PT
Began session at least 1hr ago.

1:08pm: Learned about `@overload` in typing, from https://adamj.eu/tech/2021/09/06/python-type-hints-how-to-vary-return-type-based-on-an-argument/ 
to return multiple types depending on type of parameters.

1:24pm: Learned about `TypeVarTuple` in typing, from https://stackoverflow.com/questions/46487583/python-3-types-custom-variadic-generic-type-with-arbitrary-number-of-contained 
after a short stupid back-and-forth with ShitGPT (and deciding to google finally).

5:09pm: Break session. I recorded a demo video of two proofs.

# Wednesday Apr 17, 2024, 5:46pm PT
Begin session. Continue work on predicate proof search.

TODO: Need to implement hash for other props besides And, Not, Implies, Or, Proposition.

8:17pm: end session.

2:02am: TODO: add De_morgan as a tactic or method to every proposition.

# Thursday Apr 18, 2024, 7:29am PT
Begin session. Will finish pred proof search today.

8:50am: break session. I've reached satisfactory level for proof search.

# Friday Apr 26, 2024, 5:15pm PT
Begin session. I'll clean up the difference between Symbol and Variable.

Want to implement unification. Recal that `Term = Variable | Symbol | Set | sp.Basic | int | float`.

The rules below are followed (first matching rule from top to bottom is used):

- A `Variable` unifies with any `Term`.
- Two `Term`s unify if they are equal.
- Two atomic propositions unify if they have the same arity and all the arguments unify:
    - If a variable has been unified with a term, the rest of the instantiations of the variable must be compatible (equal) with the term.
- Two propositions unify if they are the same type and all the sub-props unify.

8:50pm: end session. Added unification.

# Saturday Apr 27, 2024, 12:27pm PT
No session. TODO:
- Add De Morgan
- Add Induction
- Add natural language descriptions
- Fix `_is_proven` argument to be more explicit

# Saturday Apr 27, 2024, 8:10pm PT
Begin session. Will add De Morgan.

9:28pm: Added De-Morgan that applies to every part of proposition as much as possible.
Might need to implement De-Morgan to apply to part of a proposition.

9:56pm: will add induction on `Naturals0`.
10:58pm: end session. Added weak induction in `arithmetic.py`. May need to test a bit more.
Should add strong induction.

TODO: cleanup inequality propositions and add more tactics.

# Sunday Apr 28, 2024, 4:46pm PT
Forgot to log in. Worked on graphs, sets, contains. Now have `Symbol`, `Variable` and `Constant`.

TODO: Create classes for Graph, List, Pair, Sequence, etc. Then one can create a
variable graph using either `Variable('G', graph=True)`
or `Graph('G', nodes=n, edges=e)` where `n` and `e` are variable sets themselves.

6:05pm: break session. added strong induction and `LessOrEqual`.

# Monday Apr 29, 2024, 2:23pm PT
Begin session. Will add natural language descriptions.

3:44pm: added natural language descriptions.

TODO: Refactor `replace`, refactor `Ordering` (inequality) propositions.

5:53pm: Need to complete adding `_assumptions=` and `_inference=` to all rules of inference.
Also need to add `**kwargs` to all constructors.

7:45pm: end session. There are errors from me trying to add `_assumptions=` and `_inference=`.
Need to add and verify these attributes on all rules of inference and proposition constructors.

# Tuesday Apr 30, 2024, 10:31am PT
Begin session.

5:14pm: added `_assumptions=` and `_inference=` to all rules of inference.

Will add `ExOr` and modify `resolve` and `definite_clause_resolve` as well as add methods on `Contradiction`.

6:54pm: added `resolve` and `definite_clause_resolve` as well as `unit_` versions of them.

TODO: Add a `_Junction` class that `And`, `Or`, `ExOr` inherit from.

6:55pm: end session.

# Thursday May 02, 2024, 3:17pm PT
Begin session. Will add `_Junction` class and `..InSet` quantifier classes.

6:34pm: end session. Added `_Junction` class and `..InSet` quantifier classes; corrected `in_particular` and added `extract` for `Exists`.

# Friday May 03, 2024, 10:48pm PT
I've been thinking about replacing the `Variable` in `Exists` with a `Constant`.
When we make an exists statement, the thing that exists can only have one (or few) values.

However, consider the code below:
```python
c = Constant('c')
Pc = Proposition('P', args=[c])
exists_c_Qc = Exists(c, Proposition('Q', args=[c]))
```
We are implicitly saying that the `c` in `Pc` is the same as the `c` in `exists_c_Qc`. But this
might not be our intention. At least with
```python
c = Variable('c')
Pc = Proposition('P', args=[c])
Qc = Proposition('Q', args=[c])
```
we can clearly see that `c` is the same object in both `Pc` and `Qc`.

11:21pm: will modify `and_`, `or_`, and add `xor` to remove duplicates. Will change `followed_from` to
remove the assumption.

Saturday May 04, 2024, 1:01am PT
end session. Sympy keeps rearranging my expressions even with `evaluate=False`.
I'm considering writing my own classes to hold expressions until I'm ready to evaluate them.

For now, I started writing some axioms of real numbers before running into the sympy issue.

Also need to fix a type issue with the `and_` overrides; issue seen in `main.py`.

# Sunday May 05, 2024, 3:03pm PT
Began session at least 1hr ago. I added a printing directory with `latex_printer` and `str_printer` to print expressions in order-preserving manner.

3:53pm: I noticed the followind case:
```python
a = Variable('a')
b = Variable('b')
p = Forall(a, Forall(b, Forall(a, Proposition('P', args=[a, b]))))
```
The `a` in the innermost `Forall` should not be the same as the `a` in the outermost `Forall`.

I added a `.bound` attribute to `Variable` to indicate if it isalready bound
to a quantified statement.