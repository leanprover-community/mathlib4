/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.Lex

#align_import data.finsupp.well_founded from "leanprover-community/mathlib"@"5fd3186f1ec30a75d5f65732e3ce5e623382556f"

/-!
# Well-foundedness of the lexicographic and product orders on `Finsupp`

`Finsupp.Lex.wellFounded` and the two variants that follow it essentially say that if `(· > ·)` is
a well order on `α`, `(· < ·)` is well-founded on `N`, and `0` is a bottom element in `N`, then the
lexicographic `(· < ·)` is well-founded on `α →₀ N`.

`Finsupp.Lex.wellFoundedLT_of_finite` says that if `α` is finite and equipped with a linear order
and `(· < ·)` is well-founded on `N`, then the lexicographic `(· < ·)` is well-founded on `α →₀ N`.

`Finsupp.wellFoundedLT` and `wellFoundedLT_of_finite` state the same results for the product
order `(· < ·)`, but without the ordering conditions on `α`.

All results are transferred from `DFinsupp` via `Finsupp.toDFinsupp`.
-/


variable {α N : Type*}

namespace Finsupp

variable [Zero N] {r : α → α → Prop} {s : N → N → Prop} (hbot : ∀ ⦃n⦄, ¬s n 0)
  (hs : WellFounded s)

/-- Transferred from `DFinsupp.Lex.acc`. See the top of that file for an explanation for the
  appearance of the relation `rᶜ ⊓ (≠)`. -/
theorem Lex.acc (x : α →₀ N) (h : ∀ a ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) a) :
    Acc (Finsupp.Lex r s) x := by
  rw [lex_eq_invImage_dfinsupp_lex]
  classical
    refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) (fun _ => hs) _ ?_)
    simpa only [toDFinsupp_support] using h
#align finsupp.lex.acc Finsupp.Lex.acc

theorem Lex.wellFounded (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (Finsupp.Lex r s) :=
  ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩
#align finsupp.lex.well_founded Finsupp.Lex.wellFounded

theorem Lex.wellFounded' [IsTrichotomous α r] (hr : WellFounded (Function.swap r)) :
    WellFounded (Finsupp.Lex r s) :=
  (lex_eq_invImage_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) (fun _ => hs) hr)
#align finsupp.lex.well_founded' Finsupp.Lex.wellFounded'

instance Lex.wellFoundedLT {α N} [LT α] [IsTrichotomous α (· < ·)] [hα : WellFoundedGT α]
    [CanonicallyOrderedAddCommMonoid N] [hN : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  ⟨Lex.wellFounded' (fun n => (zero_le n).not_lt) hN.wf hα.wf⟩
#align finsupp.lex.well_founded_lt Finsupp.Lex.wellFoundedLT

variable (r)

theorem Lex.wellFounded_of_finite [IsStrictTotalOrder α r] [Finite α]
    (hs : WellFounded s) : WellFounded (Finsupp.Lex r s) :=
  InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun _ => hs)
#align finsupp.lex.well_founded_of_finite Finsupp.Lex.wellFounded_of_finite

theorem Lex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
    [hwf : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩
#align finsupp.lex.well_founded_lt_of_finite Finsupp.Lex.wellFoundedLT_of_finite

protected theorem wellFoundedLT [Preorder N] [WellFoundedLT N] (hbot : ∀ n : N, ¬n < 0) :
    WellFoundedLT (α →₀ N) :=
  ⟨InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a).wf⟩
#align finsupp.well_founded_lt Finsupp.wellFoundedLT

instance wellFoundedLT' {N} [CanonicallyOrderedAddCommMonoid N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  Finsupp.wellFoundedLT fun a => (zero_le a).not_lt
#align finsupp.well_founded_lt' Finsupp.wellFoundedLT'

instance wellFoundedLT_of_finite [Finite α] [Preorder N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩
#align finsupp.well_founded_lt_of_finite Finsupp.wellFoundedLT_of_finite

end Finsupp
