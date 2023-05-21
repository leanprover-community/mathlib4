import Mathlib.Tactic.Explode.Index
import Mathlib.Data.Real.Basic
set_option linter.unusedVariables false
open Lean

elab "#explode_test " theoremStx:ident : command => Elab.Command.liftTermElabM do
  let theoremName : Name ← Elab.resolveGlobalConstNoOverloadWithInfo theoremStx
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!
  let entries ← Mathlib.Explode.explode body
  let md : MessageData ← Mathlib.Explode.entriesToMessageData entries
  let str := toString (← md.format)

  let some ds ← findDocString? (← getEnv) theoremName
    | throwError s!"❌ {theoremName}: no docstring"
  if str == ds then
    Lean.logInfo s!"✅ {theoremName} success"
  else
    Lean.logError s!"❌ {theoremName} in docstring:\n\n{ds}\n❌ {theoremName} actual:\n\n{str}"

/--
0│   │ a  ├ True
1│0,0│ →I │ True → True
-/
theorem lambda : True → True :=
  λ a => a
#explode_test lambda

/--
0│       │ True.intro │ True
1│_,_,0,0│ @And.intro │ True ∧ True
-/
theorem application : True ∧ True :=
  And.intro True.intro True.intro
#explode_test application

/--
0│   │ p  ├ Prop
1│   │ hP ├ p
2│1,1│ →I │ p → p
3│0,2│ ∀I │ ∀ (p : Prop), p → p
-/
theorem theorem_1 : ∀ (p : Prop), p → p :=
  λ (p : Prop) => (λ hP : p => hP)
#explode_test theorem_1

/--
0│       │ p          ├ Prop
1│       │ q          ├ Prop
2│       │ hP         ├ p
3│       │ hQ         ├ q
4│0,1,2,3│ @And.intro │ p ∧ q
5│3,4    │ →I         │ q → p ∧ q
6│2,5    │ →I         │ p → q → p ∧ q
7│1,6    │ ∀I         │ ∀ (q : Prop), p → q → p ∧ q
8│0,7    │ ∀I         │ ∀ (p q : Prop), p → q → p ∧ q
-/
theorem theorem_2 : ∀ (p : Prop) (q : Prop), p → q → p ∧ q :=
  λ p => λ q => λ hP => λ hQ => And.intro hP hQ
#explode_test theorem_2

/--
0│       │ a          ├ Prop
1│       │ h          ├ a
2│       │ hl         │ ┌ a
3│       │ trivial    │ │ True
4│2,3    │ →I         │ a → True
5│       │ hr         │ ┌ True
6│5,1    │ →I         │ True → a
7│0,_,4,6│ @Iff.intro │ a ↔ True
8│1,7    │ →I         │ a → (a ↔ True)
9│0,8    │ ∀I         │ ∀ (a : Prop), a → (a ↔ True)
-/
theorem theorem_3 (a : Prop) (h : a) : a ↔ True :=
  Iff.intro
    (λ hl => trivial)
    (λ hr => h)
#explode_test theorem_3

/--
0 │    │ U           ├ Prop
1 │    │ W           ├ Prop
2 │    │ hPQ         ├ U → W
3 │    │ hNQ         ├ ¬W
4 │    │ hP          ├ U
5 │2,4 │ ∀E          │ W
6 │3,5 │ ∀E          │ False
7 │_,6 │ @False.elim │ False
8 │4,7 │ →I          │ U → False
9 │3,8 │ →I          │ ¬W → U → False
10│2,9 │ →I          │ (U → W) → ¬W → U → False
11│1,10│ ∀I          │ ∀ (W : Prop), (U → W) → ¬W → U → False
12│0,11│ ∀I          │ ∀ (U W : Prop), (U → W) → ¬W → U → False
-/
theorem theorem_4 : ∀ p q : Prop, (p → q) → (¬q → ¬p) :=
  λ U => λ W => λ hPQ => λ hNQ => λ hP => False.elim (hNQ (hPQ hP))
#explode_test theorem_4

/--
0 │            │ p            ├ Prop
1 │            │ q            ├ Prop
2 │            │ hNQNP        ├ ¬q → ¬p
3 │            │ hP           ├ p
4 │1           │ Classical.em │ q ∨ ¬q
5 │            │ hQ           │ ┌ q
6 │5,5         │ →I           │ q → q
7 │            │ hNQ          │ ┌ ¬q
8 │2,7         │ ∀E           │ │ ¬p
10│8,3         │ ∀E           │ │ False
11│1,10        │ @False.elim  │ │ q
12│7,11        │ →I           │ ¬q → q
13│1,_,1,4,6,12│ @Or.elim     │ q
14│3,13        │ →I           │ p → q
15│2,14        │ →I           │ (¬q → ¬p) → p → q
16│1,15        │ ∀I           │ ∀ (q : Prop), (¬q → ¬p) → p → q
17│0,16        │ ∀I           │ ∀ (p q : Prop), (¬q → ¬p) → p → q
-/
lemma lemma_5 : ∀ p q : Prop, (¬q → ¬p) → (p → q) :=
  λ p => λ q =>
  λ hNQNP =>
  λ hP =>
    Or.elim (Classical.em q)
    (λ hQ => hQ)
    (λ hNQ =>
      let hNP := hNQNP hNQ
      False.elim (hNP hP))
#explode_test lemma_5


/--
0│   │ p   ├ Prop
1│   │ h   ├ Prop
2│   │ hpq ├ p → h
3│   │ hp  ├ p
4│2,3│ ∀E  │ h
5│3,4│ →I  │ p → h
6│2,5│ →I  │ (p → h) → p → h
7│1,6│ ∀I  │ ∀ (h : Prop), (p → h) → p → h
8│0,7│ ∀I  │ ∀ (p h : Prop), (p → h) → p → h
-/
lemma lemma_6 : ∀ p q : Prop, (p → q) → p → q :=
  λ p h hpq hp => hpq hp
#explode_test lemma_6
