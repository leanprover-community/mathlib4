/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Nodup
import Mathlib.Data.List.Defs
/-!
# Erasing duplicates in a Multiset.
-/

namespace Multiset
open List

variable [DecidableEq α]

/-! ### eraseDup -/
/-- `eraseDup s` removes duplicates from `s`, yielding a `Nodup` multiset. -/
def eraseDup [DecidableEq α] (s : Multiset α) : Multiset α :=
Quotient.liftOn s (λ l => (l.eraseDup : Multiset α))
  (λ s t p => Quotient.sound $ p.eraseDup)

#check instSetoidList
@[simp] theorem nodup_eraseDup (s : Multiset α) : Nodup (eraseDup s) :=
  Quotient.inductionOn (motive := fun s => Nodup (eraseDup s)) s List.nodup_eraseDup

theorem eraseDup_eq_self {s : Multiset α} : eraseDup s = s ↔ Nodup s := by
  constructor
  · exact λ e => e ▸ nodup_eraseDup s
  · exact Quotient.inductionOn
      (motive := fun s => Nodup s → eraseDup s = s)
      s $ λ l h => congr_arg Coe.coe h.eraseDup

theorem Nodup.eraseDup {s : Multiset α} : Nodup s → eraseDup s = s :=
  eraseDup_eq_self.2
