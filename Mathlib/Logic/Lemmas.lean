/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Tactic.SplitIfs

/-!
# More basic logic properties
A few more logic lemmas. These are in their own file, rather than `Logic.Basic`, because it is
convenient to be able to use the `split_ifs` tactic.
## Implementation notes
We spell those lemmas out with `dite` and `ite` rather than the `if then else` notation because this
would result in less delta-reduced statements.
-/


alias heq_iff_eq ↔ HEq.eq Eq.heq

--attribute [protected] HEq.eq Eq.heq

--alias ne_of_eq_of_ne ← Eq.trans_ne

--alias ne_of_ne_of_eq ← Ne.trans_eq

variable {α : Sort _} {p q r : Prop} [Decidable p] [Decidable q] {a b c : α}

theorem dite_dite_distrib_left {a : p → α} {b : ¬p → q → α} {c : ¬p → ¬q → α} :
    (dite p a fun hp => dite q (b hp) (c hp)) =
      dite q (fun hq => (dite p a) fun hp => b hp hq) fun hq => (dite p a) fun hp => c hp hq := by
  split_ifs <;> rfl

theorem dite_dite_distrib_right {a : p → q → α} {b : p → ¬q → α} {c : ¬p → α} :
    dite p (fun hp => dite q (a hp) (b hp)) c =
      dite q (fun hq => dite p (fun hp => a hp hq) c) fun hq => dite p (fun hp => b hp hq) c := by
  split_ifs <;> rfl

theorem ite_dite_distrib_left {a : α} {b : q → α} {c : ¬q → α} :
    ite p a (dite q b c) = dite q (fun hq => ite p a <| b hq) fun hq => ite p a <| c hq :=
  dite_dite_distrib_left

theorem ite_dite_distrib_right {a : q → α} {b : ¬q → α} {c : α} :
    ite p (dite q a b) c = dite q (fun hq => ite p (a hq) c) fun hq => ite p (b hq) c :=
  dite_dite_distrib_right

theorem dite_ite_distrib_left {a : p → α} {b : ¬p → α} {c : ¬p → α} :
    (dite p a fun hp => ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c) :=
  dite_dite_distrib_left

theorem dite_ite_distrib_right {a : p → α} {b : p → α} {c : ¬p → α} :
    dite p (fun hp => ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c) :=
  dite_dite_distrib_right

theorem ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c) :=
  dite_dite_distrib_left

theorem ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c) :=
  dite_dite_distrib_right
