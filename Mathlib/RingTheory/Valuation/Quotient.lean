/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

#align_import ring_theory.valuation.quotient from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# The valuation on a quotient ring

The support of a valuation `v : Valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on `R / J` = `Ideal.Quotient J` is `onQuot v h`.

-/


namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]

variable (v : Valuation R Γ₀)

/-- If `hJ : J ⊆ supp v` then `onQuotVal hJ` is the induced function on `R / J` as a function.
Note: it's just the function; the valuation is `onQuot hJ`. -/
def onQuotVal {J : Ideal R} (hJ : J ≤ supp v) : R ⧸ J → Γ₀ := fun q =>
  Quotient.liftOn' q v fun a b h =>
    calc
      v a = v (b + -(-a + b)) := by simp
                                    -- 🎉 no goals
      _ = v b :=
        v.map_add_supp b <| (Ideal.neg_mem_iff _).2 <| hJ <| QuotientAddGroup.leftRel_apply.mp h
#align valuation.on_quot_val Valuation.onQuotVal

/-- The extension of valuation `v` on `R` to valuation on `R / J` if `J ⊆ supp v`. -/
def onQuot {J : Ideal R} (hJ : J ≤ supp v) : Valuation (R ⧸ J) Γ₀ where
  toFun := v.onQuotVal hJ
  map_zero' := v.map_zero
  map_one' := v.map_one
  map_mul' xbar ybar := Quotient.ind₂' v.map_mul xbar ybar
  map_add_le_max' xbar ybar := Quotient.ind₂' v.map_add xbar ybar
#align valuation.on_quot Valuation.onQuot

@[simp]
theorem onQuot_comap_eq {J : Ideal R} (hJ : J ≤ supp v) :
    (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  ext fun _ => rfl
#align valuation.on_quot_comap_eq Valuation.onQuot_comap_eq

theorem self_le_supp_comap (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) :
    J ≤ (v.comap (Ideal.Quotient.mk J)).supp := by
  rw [comap_supp, ← Ideal.map_le_iff_le_comap]
  -- ⊢ Ideal.map (Ideal.Quotient.mk J) J ≤ supp v
  simp
  -- 🎉 no goals
#align valuation.self_le_supp_comap Valuation.self_le_supp_comap

@[simp]
theorem comap_onQuot_eq (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
  ext <| by
    rintro ⟨x⟩
    -- ⊢ ↑(onQuot (comap (Ideal.Quotient.mk J) v) (_ : J ≤ supp (comap (Ideal.Quotien …
    rfl
    -- 🎉 no goals
#align valuation.comap_on_quot_eq Valuation.comap_onQuot_eq

/-- The quotient valuation on `R / J` has support `(supp v) / J` if `J ⊆ supp v`. -/
theorem supp_quot {J : Ideal R} (hJ : J ≤ supp v) :
    supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) := by
  apply le_antisymm
  -- ⊢ supp (onQuot v hJ) ≤ Ideal.map (Ideal.Quotient.mk J) (supp v)
  · rintro ⟨x⟩ hx
    -- ⊢ Quot.mk Setoid.r x ∈ Ideal.map (Ideal.Quotient.mk J) (supp v)
    apply Ideal.subset_span
    -- ⊢ Quot.mk Setoid.r x ∈ ↑(Ideal.Quotient.mk J) '' ↑(supp v)
    exact ⟨x, hx, rfl⟩
    -- 🎉 no goals
  · rw [Ideal.map_le_iff_le_comap]
    -- ⊢ supp v ≤ Ideal.comap (Ideal.Quotient.mk J) (supp (onQuot v hJ))
    intro x hx
    -- ⊢ x ∈ Ideal.comap (Ideal.Quotient.mk J) (supp (onQuot v hJ))
    exact hx
    -- 🎉 no goals
#align valuation.supp_quot Valuation.supp_quot

theorem supp_quot_supp : supp (v.onQuot le_rfl) = 0 := by
  rw [supp_quot]
  -- ⊢ Ideal.map (Ideal.Quotient.mk (supp v)) (supp v) = 0
  exact Ideal.map_quotient_self _
  -- 🎉 no goals
#align valuation.supp_quot_supp Valuation.supp_quot_supp

end Valuation

namespace AddValuation

variable {R Γ₀ : Type*}

variable [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ₀]

variable (v : AddValuation R Γ₀)

-- attribute [local reducible] AddValuation -- Porting note: reducible not supported

/-- If `hJ : J ⊆ supp v` then `onQuotVal hJ` is the induced function on `R / J` as a function.
Note: it's just the function; the valuation is `onQuot hJ`. -/
def onQuotVal {J : Ideal R} (hJ : J ≤ supp v) : R ⧸ J → Γ₀ :=
  Valuation.onQuotVal v hJ
#align add_valuation.on_quot_val AddValuation.onQuotVal

/-- The extension of valuation `v` on `R` to valuation on `R / J` if `J ⊆ supp v`. -/
def onQuot {J : Ideal R} (hJ : J ≤ supp v) : AddValuation (R ⧸ J) Γ₀ :=
  Valuation.onQuot v hJ
#align add_valuation.on_quot AddValuation.onQuot

@[simp]
theorem onQuot_comap_eq {J : Ideal R} (hJ : J ≤ supp v) :
    (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  Valuation.onQuot_comap_eq v hJ
#align add_valuation.on_quot_comap_eq AddValuation.onQuot_comap_eq

theorem comap_supp {S : Type*} [CommRing S] (f : S →+* R) :
    supp (v.comap f) = Ideal.comap f v.supp :=
  Valuation.comap_supp v f
#align add_valuation.comap_supp AddValuation.comap_supp

theorem self_le_supp_comap (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) :
    J ≤ (v.comap (Ideal.Quotient.mk J)).supp :=
  Valuation.self_le_supp_comap J v
#align add_valuation.self_le_supp_comap AddValuation.self_le_supp_comap

@[simp]
theorem comap_onQuot_eq (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
  Valuation.comap_onQuot_eq J v
#align add_valuation.comap_on_quot_eq AddValuation.comap_onQuot_eq

/-- The quotient valuation on `R / J` has support `(supp v) / J` if `J ⊆ supp v`. -/
theorem supp_quot {J : Ideal R} (hJ : J ≤ supp v) :
    supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) :=
  Valuation.supp_quot v hJ
#align add_valuation.supp_quot AddValuation.supp_quot

theorem supp_quot_supp : supp ((Valuation.onQuot v) le_rfl) = 0 :=
  Valuation.supp_quot_supp v
#align add_valuation.supp_quot_supp AddValuation.supp_quot_supp

end AddValuation
