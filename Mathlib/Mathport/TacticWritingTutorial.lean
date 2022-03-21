/-!
# A First Pass Tactic Writing Tutorial for Lean 4

Authors: Arthur Paulino

This tutorial covers some basic ideas and tools to write tactics in Lean 4.

But before we start, it's important to state that:

* We shall make use of a lot of syntactic sugars provided by the Lean 4 source
code, which might feel a bit uncomfortable for the reader that prefers a more
detailed bottom-up approach.

* In-depth explanations about monadic programming in Lean 4 are out of the
scope of this document.

## The two ways of writing tactics

Lean 4 offers two ways of creating tactics. One uses macros to expand `Syntax`
terms into other `Syntax` terms. The other gives you enough power to read and
modify the goal state.
-/

macro "assump" : tactic => `(tactic|assumption)

example {P : Prop} (h : P) : P := by assump
