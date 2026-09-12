/-
Copyright (c) 2026 Zikang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zikang Yu
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of direct limits

This file gives upper and lower bounds for the cardinality of a direct limit of types.

## Main statements

* `DirectLimit.mk_le_sum`: the cardinality of a direct limit is at most the sum of the
  cardinalities of its components.
* `DirectLimit.mk_le_of_aleph0_le`: an infinite common bound for the index type and the
  components is also a bound for the direct limit.
* `DirectLimit.iSup_lift_mk_le_mk`: when the canonical maps are injective, the supremum of the
  component cardinalities is at most the cardinality of the direct limit.
* `DirectLimit.mk_eq_iSup_lift_mk`: when that supremum is greater than the cardinality of the
  index type and the canonical maps are injective, it equals the cardinality of the direct limit.
* `DirectLimit.mk_eq_of_forall_lift_mk_eq`: when all components have the same cardinality, under
  the corresponding bound and injectivity assumptions, so does the direct limit.
-/

@[expose] public section

open Cardinal Function

universe u v w

namespace DirectLimit

variable {ι : Type u} [Preorder ι] {F : ι → Type v}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort w} (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
variable [DirectedSystem F (f · · ·)] [IsDirectedOrder ι]

/-- The cardinality of a direct limit is at most the sum of the cardinalities of its
components. -/
theorem mk_le_sum : #(DirectLimit F (f · · ·)) ≤ Cardinal.sum fun i ↦ #(F i) :=
  mk_quotient_le.trans_eq (mk_sigma F)

/-- An infinite cardinal that bounds the cardinality of the index type and all components also
bounds the cardinality of the direct limit. -/
theorem mk_le_of_aleph0_le (c : Cardinal.{max u v}) (hc : ℵ₀ ≤ c)
    (hι : Cardinal.lift.{v} #ι ≤ c) (hF : ∀ i, Cardinal.lift.{u} #(F i) ≤ c) :
    #(DirectLimit F (f · · ·)) ≤ c :=
  (mk_le_sum f).trans <| (sum_le_lift_mk_mul_iSup_lift _).trans <|
    Cardinal.mul_le_of_le hc hι (ciSup_le' hF)

/-- If all canonical maps into a direct limit are injective, then the supremum of the
cardinalities of the components is at most the cardinality of the direct limit. -/
theorem iSup_lift_mk_le_mk
    (h : ∀ i, Injective fun x ↦ (⟦⟨i, x⟩⟧ : DirectLimit F (f · · ·))) :
    (⨆ i, Cardinal.lift.{u} #(F i)) ≤ #(DirectLimit F (f · · ·)) := by
  refine ciSup_le' fun i ↦ ?_
  have := lift_mk_le_lift_mk_of_injective (h i)
  simp [DirectLimit]
  rwa [Cardinal.lift_umax, Cardinal.lift_id'.{v,u}] at this

/-- If all canonical maps into a direct limit are injective and the supremum of the component
cardinalities is greater than the cardinality of the index type, then it equals the cardinality
of the direct limit. -/
theorem mk_eq_iSup_lift_mk
    (hι : Cardinal.lift.{v} #ι ≤ ⨆ i, Cardinal.lift.{u} #(F i))
    (h : ∀ i, Injective fun x ↦ (⟦⟨i, x⟩⟧ : DirectLimit F (f · · ·))) :
    #(DirectLimit F (f · · ·)) = ⨆ i, Cardinal.lift.{u} #(F i) := by
  refine le_antisymm ?_ (iSup_lift_mk_le_mk f h)
  by_cases! hc : ℵ₀ ≤ ⨆ i, lift.{u, v} #(F i)
  · exact mk_le_of_aleph0_le f _ hc hι fun i ↦ le_ciSup Cardinal.bddAbove_of_small i
  · haveI : Finite ι := mk_lt_aleph0_iff.mp (lift_lt_aleph0.mp (hι.trans_lt hc))
    cases isEmpty_or_nonempty ι with
    | inl hle =>
      simp
    | inr hlne =>
      obtain ⟨m, hm⟩ := Finite.exists_le (id : ι → ι)
      have he := (equivOfForallLE f m hm).lift_cardinal_eq
      rw [Cardinal.lift_id'.{v,u}, Cardinal.lift_umax.{v,u}] at he
      rw [he]
      exact le_ciSup Cardinal.bddAbove_of_small m

/-- If all components have the same cardinality `c`, the cardinality of the index type is at most
`c`, and all canonical maps are injective, then the direct limit also has cardinality `c`. -/
theorem mk_eq_of_forall_lift_mk_eq [Nonempty ι] (c : Cardinal.{max u v})
    (hι : Cardinal.lift.{v} #ι ≤ c) (hF : ∀ i, Cardinal.lift.{u} #(F i) = c)
    (h : ∀ i, Injective fun x ↦ (⟦⟨i, x⟩⟧ : DirectLimit F (f · · ·))) :
    #(DirectLimit F (f · · ·)) = c := by
  simpa only [hF, ciSup_const] using
    mk_eq_iSup_lift_mk f (by simpa only [hF, ciSup_const]) h

end DirectLimit
