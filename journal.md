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
