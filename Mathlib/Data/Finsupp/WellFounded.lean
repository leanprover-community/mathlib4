/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Data.Finsupp.Lex

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

@[expose] public section


variable {α N : Type*}

namespace Finsupp

variable [Zero N] {r : α → α → Prop} {s : N → N → Prop}

/-- Transferred from `DFinsupp.Lex.acc`. See the top of that file for an explanation for the
  appearance of the relation `rᶜ ⊓ (≠)`. -/
theorem Lex.acc (hbot : ∀ ⦃n⦄, ¬s n 0) (hs : WellFounded s) (x : α →₀ N)
    (h : ∀ a ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) a) :
    Acc (Finsupp.Lex r s) x := by
  rw [lex_eq_invImage_dfinsupp_lex]
  classical
    refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) _ ?_)
    simpa only [toDFinsupp_support] using h

theorem Lex.wellFounded (hbot : ∀ ⦃n⦄, ¬s n 0) (hs : WellFounded s)
    (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (Finsupp.Lex r s) :=
  ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩

theorem Lex.wellFounded' (hbot : ∀ ⦃n⦄, ¬s n 0) (hs : WellFounded s)
    [Std.Trichotomous r] (hr : WellFounded (Function.swap r)) : WellFounded (Finsupp.Lex r s) :=
  (lex_eq_invImage_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) hr)

instance Lex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [hα : WellFoundedGT α]
    [AddMonoid N] [PartialOrder N] [CanonicallyOrderedAdd N]
    [hN : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  Lex.wellFounded' (fun n => (zero_le n).not_gt) hN hα

instance Colex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [WellFoundedLT α]
    [AddMonoid N] [PartialOrder N] [CanonicallyOrderedAdd N]
    [WellFoundedLT N] : WellFoundedLT (Colex (α →₀ N)) :=
  Lex.wellFoundedLT (α := αᵒᵈ)

variable (r)

theorem Lex.wellFounded_of_finite [IsStrictTotalOrder α r] [Finite α]
    (hs : WellFounded s) : WellFounded (Finsupp.Lex r s) :=
  InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r)

theorem Lex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
    [hwf : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  Finsupp.Lex.wellFounded_of_finite (· < ·) hwf

theorem Colex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
    [WellFoundedLT N] : WellFoundedLT (Colex (α →₀ N)) :=
  Lex.wellFoundedLT_of_finite (α := αᵒᵈ)

protected theorem wellFoundedLT [Preorder N] [WellFoundedLT N] (hbot : ∀ n : N, ¬n < 0) :
    WellFoundedLT (α →₀ N) :=
  InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a)

instance wellFoundedLT' {N}
    [AddMonoid N] [PartialOrder N] [CanonicallyOrderedAdd N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  Finsupp.wellFoundedLT fun a => (zero_le a).not_gt

instance wellFoundedLT_of_finite [Finite α] [Preorder N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  InvImage.wf equivFunOnFinite Function.wellFoundedLT

end Finsupp
