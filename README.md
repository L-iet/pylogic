
## Logical Tactic

A tactic is a rule of logic we can use to produce proofs.


Could have a Forall Prop type, which represents a completed forall proposition

In it, we save the quantified argument.

forall x: P x

forall _: ( forall x: P x _)
-------------------------

How to tell forall prop

The name is of the pattern

forall {object_name}: {pred_name} ... {object_name} ...

## Tactics

Here, the letters represent props that completely match.

Forall x, P x
Therefore, P x0 - done

Forall x, P
Exists x, P => Q
Therefore, Exists x, Q.

Forall x, P => Q
Exists x, P
Therefore, Exists x, Q.


