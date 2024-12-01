So, Sympy **is** trying to copy? my expressions, I think.

Ran into this stack trace

```
File c:\Users\joshj\AppData\Local\Programs\Python\Python311\Lib\site-packages\sympy\core\basic.py:1847, in Basic.doit(self, **hints)
   1844 if hints.get('deep', True):
   1845     terms = [term.doit(**hints) if isinstance(term, Basic) else term
   1846                                  for term in self.args]
-> 1847     return self.func(*terms)
   1848 else:
   1849     return self

File d:\Minerva\courses\CP\pylogic\pylogic\sympy_helpers.py:75, in _create_sympy_class.<locals>._new(cls, _pyl_class, _pyl_init_args, _pyl_init_kwargs, *args, **kwargs)
     73     s = f"Must provide _pyl_class for {cls}\nbase: {base}\n"
     74     s += f"args: {args}\nkwargs: {kwargs}"
---> 75     raise ValueError(s)
     76 val._pyl_class = _pyl_class
     77 val._pyl_init_args = _pyl_init_args or ()

ValueError: Must provide _pyl_class for <class 'pylogic.sympy_helpers.PylSympySeqBase'>
base: <class 'sympy.series.sequences.SeqBase'>
args: ('a',)
kwargs: {}
```
it appears it tries to call the expression's class with the arguments
that were passed as `terms`. But my classes need extra data which it cannot
provide.

I need to ensure to avoid calling to_sympy for certain expressions/terms, such as Sequence -> SeqBase.