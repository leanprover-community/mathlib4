import Mathlib.Tactic.Explode.Index
import Mathlib.Data.Real.Basic
set_option linter.unusedVariables false
open Lean Lean.Elab

elab "#explode_test " theoremStx:ident : command => do
  let theoremName : Name ← resolveGlobalConstNoOverloadWithInfo theoremStx
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!
  Elab.Command.liftCoreM do
    Lean.Meta.MetaM.run' do
      let results ← Mathlib.Explode.core body true 0 default { verbose := false }
      let md : MessageData ← Mathlib.Explode.entriesToMD results
      let str := toString (← md.format)

      let docString ← findDocString? (← getEnv) theoremName
      if let some ds := docString then
        if str == ds then
          Lean.logInfo s!"✅ {theoremName} success"
        else
          Lean.logError s!"❌ {theoremName} in docstring:\n\n{ds}\n❌ {theoremName} actual:\n\n{str}"
      else
        Lean.logError s!"❌ {theoremName}: no docstring"

/--
0│   │ a  ├ True
1│0,0│ →I │ True → True
-/
theorem lambda : True → True :=
  λ a => a
#explode_test lambda

/--
0│         │ And.intro   │ ∀ {a b : Prop}, a → b → a ∧ b
1│         │ True        │ Prop
2│         │ True.intro  │ True
3│0,1,1,2,2│ And.intro() │ True ∧ True
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
0│         │ p           ├ Prop
1│         │ q           ├ Prop
2│         │ hP          ├ p
3│         │ hQ          ├ q
4│         │ And.intro   │ ∀ {a b : Prop}, a → b → a ∧ b
5│4,0,1,2,3│ And.intro() │ p ∧ q
6│3,5      │ →I          │ q → p ∧ q
7│2,6      │ →I          │ p → q → p ∧ q
8│1,7      │ ∀I          │ ∀ (q : Prop), p → q → p ∧ q
9│0,8      │ ∀I          │ ∀ (p q : Prop), p → q → p ∧ q
-/
theorem theorem_2 : ∀ (p : Prop) (q : Prop), p → q → p ∧ q :=
  λ p => λ q => λ hP => λ hQ => And.intro hP hQ
#explode_test theorem_2

/--
0 │         │ a           ├ Prop
1 │         │ h           ├ a
2 │         │ Iff.intro   │ ∀ {a b : Prop}, (a → b) → (b → a) → (a ↔ b)
3 │         │ True        │ Prop
4 │         │ hl          │ ┌ a
5 │         │ trivial     │ │ True
6 │4,5      │ →I          │ a → True
7 │         │ hr          │ ┌ True
8 │7,1      │ →I          │ True → a
9 │2,0,3,6,8│ Iff.intro() │ a ↔ True
10│1,9      │ →I          │ a → (a ↔ True)
11│0,10     │ ∀I          │ ∀ (a : Prop), a → (a ↔ True)
-/
theorem theorem_3 (a : Prop) (h : a) : a ↔ True :=
  Iff.intro
    (λ hl => trivial)
    (λ hr => h)
#explode_test theorem_3

/--
0 │     │ U            ├ Prop
1 │     │ W            ├ Prop
2 │     │ hPQ          ├ U → W
3 │     │ hNQ          ├ ¬W
4 │     │ hP           ├ U
5 │     │ False.elim   │ ∀ {C : Prop}, False → C
6 │     │ False        │ Prop
7 │2,4  │ ∀E           │ W
8 │3,7  │ ∀E           │ False
9 │5,6,8│ False.elim() │ False
10│4,9  │ →I           │ U → False
11│3,10 │ →I           │ ¬W → U → False
12│2,11 │ →I           │ (U → W) → ¬W → U → False
13│1,12 │ ∀I           │ ∀ (W : Prop), (U → W) → ¬W → U → False
14│0,13 │ ∀I           │ ∀ (U W : Prop), (U → W) → ¬W → U → False
-/
theorem theorem_4 : ∀ p q : Prop, (p → q) → (¬q → ¬p) :=
  λ U => λ W => λ hPQ => λ hNQ => λ hP => False.elim (hNQ (hPQ hP))
#explode_test theorem_4

/--
0 │            │ p              ├ Prop
1 │            │ q              ├ Prop
2 │            │ hNQNP          ├ ¬q → ¬p
3 │            │ hP             ├ p
4 │            │ Or.elim        │ ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
5 │            │ Classical.em   │ ∀ (p : Prop), p ∨ ¬p
6 │5,1         │ Classical.em() │ q ∨ ¬q
7 │            │ hQ             │ ┌ q
8 │7,7         │ →I             │ q → q
9 │            │ hNQ            │ ┌ ¬q
10│            │ False.elim     │ │ ∀ {C : Prop}, False → C
11│2,9,3       │ ∀E             │ │ False
12│10,1,11     │ False.elim()   │ │ q
13│9,12        │ →I             │ ¬q → q
14│4,1,1,6,8,13│ Or.elim()      │ q
15│3,14        │ →I             │ p → q
16│2,15        │ →I             │ (¬q → ¬p) → p → q
17│1,16        │ ∀I             │ ∀ (q : Prop), (¬q → ¬p) → p → q
18│0,17        │ ∀I             │ ∀ (p q : Prop), (¬q → ¬p) → p → q
-/
lemma lemma_5 : ∀ p q : Prop, (¬q → ¬p) → (p → q) :=
  λ p => λ q =>
  λ hNQNP =>
  λ hP =>
    Or.elim (Classical.em q)
    (λ hQ => hQ)
    (λ hNQ =>
      let hNP := hNQNP hNQ
      False.elim (hNP hP)
    )
#explode_test lemma_5
