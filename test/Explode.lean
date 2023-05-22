import Mathlib.Tactic.Explode
import Mathlib.Data.Real.Basic
set_option linter.unusedVariables false
open Lean

-- See that the explode command itself works
#explode true_iff

elab dc?:docComment ? tk:"#explode_test " stx:term : command => do
  let some msg ← Mathlib.Explode.runExplode stx
    | throwErrorAt tk "❌ failure in #explode"
  if let some dc := dc? then
    let str := toString (← msg.format)
    let ds := (← getDocStringText dc)
    if str.trim == ds.trim then
      logInfoAt tk m!"✅ success"
      logInfoAt tk msg
    else
      logErrorAt tk m!"❌ expected from docstring:\n\n{ds}\n❌ actual:\n\n{msg}"
  else
    logErrorAt tk m!"❌ missing docstring"
    logInfoAt tk msg

theorem lambda : True → True :=
  λ a => a

/--
lambda : True → True

0│   │ a  ├ True
1│0,0│ ∀I │ True → True
-/
#explode_test lambda

theorem application : True ∧ True :=
  And.intro True.intro True.intro

/--
application : True ∧ True

0│   │ True.intro │ True
1│0,0│ And.intro  │ True ∧ True
-/
#explode_test application

theorem theorem_1 : ∀ (p : Prop), p → p :=
  λ (p : Prop) => (λ hP : p => hP)
/--
theorem_1 : ∀ (p : Prop), p → p

0│     │ p  ├ Prop
1│     │ hP ├ p
2│0,1,1│ ∀I │ ∀ (p : Prop), p → p
-/
#explode_test theorem_1

theorem theorem_2 : ∀ (p : Prop) (q : Prop), p → q → p ∧ q :=
  λ p => λ q => λ hP => λ hQ => And.intro hP hQ

/--
theorem_2 : ∀ (p q : Prop), p → q → p ∧ q

0│         │ p         ├ Prop
1│         │ q         ├ Prop
2│         │ hP        ├ p
3│         │ hQ        ├ q
4│2,3      │ And.intro │ p ∧ q
5│0,1,2,3,4│ ∀I        │ ∀ (p q : Prop), p → q → p ∧ q
-/
#explode_test theorem_2

theorem theorem_3 (a : Prop) (h : a) : a ↔ True :=
  Iff.intro
    (λ hl => trivial)
    (λ hr => h)

/--
theorem_3 : ∀ (a : Prop), a → (a ↔ True)

0│     │ a         ├ Prop
1│     │ h         ├ a
2│     │ hl        │ ┌ a
3│     │ trivial   │ │ True
4│2,3  │ ∀I        │ a → True
5│     │ hr        │ ┌ True
6│5,1  │ ∀I        │ True → a
7│4,6  │ Iff.intro │ a ↔ True
8│0,1,7│ ∀I        │ ∀ (a : Prop), a → (a ↔ True)
-/
#explode_test theorem_3


theorem theorem_4 : ∀ p q : Prop, (p → q) → (¬q → ¬p) :=
  λ U => λ W => λ hPQ => λ hNQ => λ hP => False.elim (hNQ (hPQ hP))

/--
theorem_4 : ∀ (p q : Prop), (p → q) → ¬q → ¬p

0│           │ U          ├ Prop
1│           │ W          ├ Prop
2│           │ hPQ        ├ U → W
3│           │ hNQ        ├ ¬W
4│           │ hP         ├ U
5│2,4        │ ∀E         │ W
6│3,5        │ ∀E         │ False
7│6          │ False.elim │ False
8│0,1,2,3,4,7│ ∀I         │ ∀ (U W : Prop), (U → W) → ¬W → U → False
-/
#explode_test theorem_4

lemma lemma_5 : ∀ p q : Prop, (¬q → ¬p) → (p → q) :=
  λ p => λ q =>
  λ hNQNP =>
  λ hP =>
    Or.elim (Classical.em q)
    (λ hQ => hQ)
    (λ hNQ =>
      let hNP := hNQNP hNQ
      False.elim (hNP hP))

/--
lemma_5 : ∀ (p q : Prop), (¬q → ¬p) → p → q

0 │          │ p            ├ Prop
1 │          │ q            ├ Prop
2 │          │ hNQNP        ├ ¬q → ¬p
3 │          │ hP           ├ p
4 │          │ Classical.em │ q ∨ ¬q
5 │          │ hQ           │ ┌ q
6 │5,5       │ ∀I           │ q → q
7 │          │ hNQ          │ ┌ ¬q
8 │2,7       │ ∀E           │ │ ¬p
10│8,3       │ ∀E           │ │ False
11│10        │ False.elim   │ │ q
12│7,11      │ ∀I           │ ¬q → q
13│4,6,12    │ Or.elim      │ q
14│0,1,2,3,13│ ∀I           │ ∀ (p q : Prop), (¬q → ¬p) → p → q
-/
#explode_test lemma_5


lemma lemma_6 : ∀ p q : Prop, (p → q) → p → q :=
  λ p h hpq hp => hpq hp

/--
lemma_6 : ∀ (p q : Prop), (p → q) → p → q

0│         │ p   ├ Prop
1│         │ h   ├ Prop
2│         │ hpq ├ p → h
3│         │ hp  ├ p
4│2,3      │ ∀E  │ h
5│0,1,2,3,4│ ∀I  │ ∀ (p h : Prop), (p → h) → p → h
-/
#explode_test lemma_6

lemma lemma_7 : ∀ p q r : Prop, (p → q) → (p → q → r) → (p → r) :=
  λ p q r hq hqr hp =>
    let hq' := hq hp
    let hqr' := hqr hp
    hqr' hq'

/--
lemma_7 : ∀ (p q r : Prop), (p → q) → (p → q → r) → p → r

0 │              │ p   ├ Prop
1 │              │ q   ├ Prop
2 │              │ r   ├ Prop
3 │              │ hq  ├ p → q
4 │              │ hqr ├ p → q → r
5 │              │ hp  ├ p
6 │3,5           │ ∀E  │ q
8 │4,5           │ ∀E  │ q → r
10│8,6           │ ∀E  │ r
11│0,1,2,3,4,5,10│ ∀I  │ ∀ (p q r : Prop), (p → q) → (p → q → r) → p → r
-/
#explode_test lemma_7

lemma lemma_5' : ∀ p q : Prop, (¬q → ¬p) → (p → q) :=
  λ p => λ q =>
  λ hNQNP =>
    Or.elim (Classical.em q)
    (λ hQ hP => hQ)
    (λ hNQ hP =>
      let hNP := hNQNP hNQ
      False.elim (hNP hP))

/--
lemma_5' : ∀ (p q : Prop), (¬q → ¬p) → p → q

0 │        │ p            ├ Prop
1 │        │ q            ├ Prop
2 │        │ hNQNP        ├ ¬q → ¬p
3 │        │ Classical.em │ q ∨ ¬q
4 │        │ hQ           │ ┌ q
5 │        │ hP           │ ├ p
6 │4,5,4   │ ∀I           │ q → p → q
7 │        │ hNQ          │ ┌ ¬q
8 │        │ hP           │ ├ p
9 │2,7     │ ∀E           │ │ ¬p
11│9,8     │ ∀E           │ │ False
12│11      │ False.elim   │ │ q
13│7,8,12  │ ∀I           │ ¬q → p → q
14│3,6,13  │ Or.elim      │ p → q
15│0,1,2,14│ ∀I           │ ∀ (p q : Prop), (¬q → ¬p) → p → q
-/
#explode_test lemma_5'

section
variable (p q : Prop)

/--
fun hp hnp ↦ hnp hp : p → (p → q) → q

0│     │ hp  ├ p
1│     │ hnp ├ p → q
2│1,0  │ ∀E  │ q
3│0,1,2│ ∀I  │ p → (p → q) → q
-/
#explode_test fun (hp : p) (hnp : p → q) => hnp hp

/--
fun hNQNP ↦
  Or.elim (Classical.em q) (fun hQ hP ↦ hQ) fun hNQ hP ↦
    let hNP := hNQNP hNQ;
    False.elim (hNP hP) : (¬q → ¬p) → p → q

0 │      │ hNQNP        ├ ¬q → ¬p
1 │      │ Classical.em │ q ∨ ¬q
2 │      │ hQ           │ ┌ q
3 │      │ hP           │ ├ p
4 │2,3,2 │ ∀I           │ q → p → q
5 │      │ hNQ          │ ┌ ¬q
6 │      │ hP           │ ├ p
7 │0,5   │ ∀E           │ │ ¬p
9 │7,6   │ ∀E           │ │ False
10│9     │ False.elim   │ │ q
11│5,6,10│ ∀I           │ ¬q → p → q
12│1,4,11│ Or.elim      │ p → q
13│0,12  │ ∀I           │ (¬q → ¬p) → p → q
-/
#explode_test fun (hNQNP : ¬q → ¬p) =>
  Or.elim (Classical.em q)
    (λ hQ hP => hQ)
    (λ hNQ hP =>
      let hNP := hNQNP hNQ
      False.elim (hNP hP))

end
