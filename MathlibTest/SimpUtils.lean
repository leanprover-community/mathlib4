import Mathlib.Tactic


/--
info: dsimproc Lean.Elab.WF.paramProj: _


dsimproc Lean.Elab.WF.paramMatcher: _


dsimproc Lean.Elab.WF.paramLet: _


dsimproc Lean.Elab.WF.paramProj: _


dsimproc Lean.Elab.WF.paramMatcher: _


dsimproc Lean.Elab.WF.paramLet: _
-/
#guard_msgs in
#simprocs ∃ _, _

/--
info: dsimproc Lean.Elab.WF.paramProj: _


dsimproc Lean.Elab.WF.paramMatcher: _


dsimproc Lean.Elab.WF.paramLet: _


dsimproc Lean.Elab.WF.paramProj: _


dsimproc Lean.Elab.WF.paramMatcher: _


dsimproc Lean.Elab.WF.paramLet: _
-/
#guard_msgs in
#dsimprocs ∃ _, _

/--
info: exists_const :  ∀ {b : Prop} (α : Sort u_1) [i : Nonempty α], (∃ x, b) ↔ b

exists_false :  ∀ {α : Sort u_1}, ¬∃ _a, False

exists_eq :  ∀ {α : Sort u_1} {a' : α}, ∃ a, a = a'

exists_eq_left :  ∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∃ a, a = a' ∧ p a) ↔ p a'

exists_eq_right :  ∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∃ a, p a ∧ a = a') ↔ p a'

exists_and_left :  ∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, b ∧ p x) ↔ b ∧ ∃ x, p x

exists_and_right :  ∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, p x ∧ b) ↔ (∃ x, p x) ∧ b

exists_eq_left' :  ∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∃ a, a' = a ∧ p a) ↔ p a'

exists_eq_right' :  ∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∃ a, p a ∧ a' = a) ↔ p a'

exists_prop_eq :  ∀ {α : Sort u_1} {a' : α} {p : (a : α) → a = a' → Prop}, (∃ a h, p a h) ↔ p a' ⋯

exists_prop_eq' :  ∀ {α : Sort u_1} {a' : α} {p : (a : α) → a' = a → Prop}, (∃ a h, p a h) ↔ p a' ⋯

exists_eq_or_imp :  ∀ {α : Sort u_1} {p q : α → Prop} {a' : α}, (∃ a, (a = a' ∨ q a) ∧ p a) ↔ p a' ∨ ∃ a, q a ∧ p a

exists_eq_right_right :  ∀ {α : Sort u_1} {p q : α → Prop} {a' : α}, (∃ a, p a ∧ q a ∧ a = a') ↔ p a' ∧ q a'

exists_eq_right_right' :  ∀ {α : Sort u_1} {p q : α → Prop} {a' : α}, (∃ a, p a ∧ q a ∧ a' = a) ↔ p a' ∧ q a'

exists_or_eq_left :  ∀ {α : Sort u_1} (y : α) (p : α → Prop), ∃ x, x = y ∨ p x

exists_or_eq_right :  ∀ {α : Sort u_1} (y : α) (p : α → Prop), ∃ x, p x ∨ x = y

exists_or_eq_left' :  ∀ {α : Sort u_1} (y : α) (p : α → Prop), ∃ x, y = x ∨ p x

exists_or_eq_right' :  ∀ {α : Sort u_1} (y : α) (p : α → Prop), ∃ x, p x ∨ y = x

exists_prop :  ∀ {b a : Prop}, (∃ _h, b) ↔ a ∧ b

exists_idem :  ∀ {P : Prop} (f : P → P → Prop), (∃ p₁ p₂, f p₁ p₂) ↔ ∃ p, f p p

exists_apply_eq_apply :  ∀ {α : Sort u_2} {β : Sort u_1} (f : α → β) (a' : α), ∃ a, f a = f a'

exists_eq' :  ∀ {α : Sort u_1} {a' : α}, ∃ a, a' = a

Subtype.exists :  ∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop}, (∃ x, q x) ↔ ∃ a b, q ⟨a, b⟩

Nat.exists_ne_zero :  ∀ {P : Nat → Prop}, (∃ n, ¬n = 0 ∧ P n) ↔ ∃ n, P (n + 1)

Nat.exists_eq_add_one :  ∀ {a : Nat}, (∃ n, a = n + 1) ↔ 0 < a

Nat.exists_add_one_eq :  ∀ {a : Nat}, (∃ n, n + 1 = a) ↔ 0 < a

exists_true_left :  ∀ {p : True → Prop}, Exists p ↔ p True.intro

Bool.exists_bool :  ∀ {p : Bool → Prop}, (∃ b, p b) ↔ p false ∨ p true

Prod.exists :  ∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p x) ↔ ∃ a b, p (a, b)
-/
#guard_msgs in
#simp_theorems ∃ _, _

/--
info: dreduceIte:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:
-/
#guard_msgs in
#dsimprocs ite _ _ _

/--
info: reduceIte:



dreduceIte:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:



Lean.Elab.WF.paramProj:



Lean.Elab.WF.paramMatcher:



Lean.Elab.WF.paramLet:
-/
#guard_msgs in
#simprocs ite _ _ _

/--
info: ite_self :  ∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c then a else a) = a

ite_false :  ∀ {α : Sort u_1} (a b : α), (if False then a else b) = b

if_false :  ∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False then t else e) = e

ite_true :  ∀ {α : Sort u_1} (a b : α), (if True then a else b) = a

if_true :  ∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then t else e) = t

ite_not :  ∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if ¬p then x else y) = if p then y else x

Classical.ite_not :  ∀ {α : Sort u_1} (p : Prop) [inst : Decidable ¬p] (x y : α), (if ¬p then x else y) = if p then y else x

ite_then_self :  ∀ {p q : Prop} [h : Decidable p], (if p then p else q) ↔ ¬p → q

ite_else_self :  ∀ {p q : Prop} [h : Decidable p], (if p then q else p) ↔ p ∧ q

if_false_right :  ∀ {p q : Prop} [h : Decidable p], (if p then q else False) ↔ p ∧ q

if_true_right :  ∀ {p q : Prop} [h : Decidable p], (if p then q else True) ↔ p → q

ite_else_not_self :  ∀ {p : Prop} [inst : Decidable p] {q : Prop}, (if p then q else ¬p) ↔ p → q

if_false_left :  ∀ {p q : Prop} [h : Decidable p], (if p then False else q) ↔ ¬p ∧ q

if_true_left :  ∀ {p q : Prop} [h : Decidable p], (if p then True else q) ↔ ¬p → q

ite_then_not_self :  ∀ {p : Prop} [inst : Decidable p] {q : Prop}, (if p then ¬p else q) ↔ ¬p ∧ q

Bool.ite_eq_true_else_eq_false :  ∀ {b : Bool} {q : Prop}, (if b = true then q else b = false) ↔ b = true → q

Bool.ite_eq_false :  ∀ {b : Bool} {p q : Prop}, (if b = false then p else q) ↔ if b = true then q else p

ite_else_decide_not_self :  ∀ (p : Prop) [h : Decidable p] {w : Decidable p} (q : Bool), (if p then q else !decide p) = (!decide p || q)

Bool.if_true_right :  ∀ (p : Prop) [h : Decidable p] (t : Bool), (if p then t else true) = (!decide p || t)

Bool.if_false_right :  ∀ (p : Prop) [h : Decidable p] (t : Bool), (if p then t else false) = (decide p && t)

ite_else_decide_self :  ∀ (p : Prop) [h : Decidable p] {w : Decidable p} (q : Bool), (if p then q else decide p) = (decide p && q)

ite_then_decide_not_self :  ∀ (p : Prop) [h : Decidable p] {w : Decidable p} (q : Bool), (if p then !decide p else q) = (!decide p && q)

Bool.if_true_left :  ∀ (p : Prop) [h : Decidable p] (f : Bool), (if p then true else f) = (decide p || f)

Bool.if_false_left :  ∀ (p : Prop) [h : Decidable p] (f : Bool), (if p then false else f) = (!decide p && f)

ite_then_decide_self :  ∀ (p : Prop) [h : Decidable p] {w : Decidable p} (q : Bool), (if p then decide p else q) = (decide p || q)
-/
#guard_msgs in
#simp_theorems ite _ _ _
