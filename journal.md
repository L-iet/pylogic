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

