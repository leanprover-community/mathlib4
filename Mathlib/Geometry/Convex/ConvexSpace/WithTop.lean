/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finsupp.Option
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Adjoining a top or bottom element to a convex space

Adjoining a top/bottom element to a convex space `X` again gives a convex space, by setting
any convex combination that puts positive weight on `⊤`/`⊥` to `⊤`/`⊥`.

Although this construction is also valid for `Option`, we refrain from adding it as we have no
application in mind. The `WithTop` and `WithBot` versions are useful to talk about convex functions
taking extended values.
-/

public noncomputable section

namespace Convexity
variable {R X : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

namespace StdSimplex

/-- Turn a distribution on `WithTop X` putting no weight on `⊤` into a distribution on `X`.

If `R` were a field, one could relax `w.weights ⊤ = 0` to `w.weights ⊤ ≠ 1`. We do not provide this
version of the operation at this time. -/
@[expose, to_dual (dont_translate := R) (attr := simps)
/-- Turn a distribution on `WithBot X` putting no weight on `⊥` into a distribution on `X`.

If `R` were a field, one could relax `w.weights ⊥ = 0` to `w.weights ⊥ ≠ 1`. We do not provide this
version of the operation at this time. -/]
def untop (w : StdSimplex R (WithTop X)) (hw : w.weights ⊤ = 0) : StdSimplex R X where
  weights := w.weights.withTopSome
  nonneg x := w.weights_nonneg (x : WithTop X)
  total := by rw [← w.total, ← Finsupp.sum_withTopSome_add rfl, hw, add_zero]

@[to_dual (attr := simp) (dont_translate := R)]
lemma map_untop_some (w : StdSimplex R (WithTop X)) (hw) :
    (w.untop hw).map WithTop.some = w := by
  ext b
  induction b with
  | top => rw [weights_map, Finsupp.mapDomain_of_notMem_range _ _ (by simp), hw]
  | coe x =>
    rw [weights_map, Finsupp.mapDomain_apply_of_injective WithTop.coe_injective]
    rfl

@[to_dual (attr := simp) (dont_translate := R)]
lemma untop_map_some (w : StdSimplex R X) (hw) : (w.map WithTop.some).untop hw = w := by
  ext x
  change (w.map WithTop.some).weights (x : WithTop X) = w.weights x
  rw [weights_map, Finsupp.mapDomain_apply_of_injective WithTop.coe_injective]

@[to_dual (dont_translate := R)]
lemma mem_range_map_withTopSome {w : StdSimplex R (WithTop X)} :
    w ∈ Set.range (map WithTop.some) ↔ w.weights ⊤ = 0 where
  mp := by rintro ⟨v, rfl⟩; rw [weights_map, Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  mpr hw := ⟨w.untop hw, map_untop_some w hw⟩

end StdSimplex

open StdSimplex

section ConvexSpace
variable [ConvexSpace R X] {w : StdSimplex R (WithTop X)}

/-- Adjoining a top element to a convex space gives a convex space in which `⊤` is absorbing:
a convex combination putting positive weight on `⊤` is equal to `⊤`. -/
@[to_dual (dont_translate := R)
/-- Adjoining a bottom element to a convex space gives a convex space in which `⊥` is absorbing:
a convex combination putting positive weight on `⊥` is equal to `⊥`. -/]
instance : ConvexSpace R (WithTop X) :=
  let c (w : StdSimplex R (WithTop X)) : WithTop X :=
    open scoped Classical in if hw : w.weights ⊤ = 0 then (w.untop hw).sConvexComb else ⊤
  have hcoe (w : StdSimplex R X) : c (w.map WithTop.some) = w.sConvexComb := by
    simp [c, Finsupp.mapDomain_apply]
  have htop (w : StdSimplex R (WithTop X)) : c w = ⊤ ↔ w.weights ⊤ ≠ 0 := by simp [c]
  .mk
    (sConvexComb := c)
    (single := fun x ↦ by
      induction x with
      | top => simp [htop]
      | coe a => rw [← map_single, hcoe, sConvexComb_single])
    (assoc := fun F ↦ by
      classical
      by_cases hF : ∀ v ∈ F.weights.support, v.weights (⊤ : WithTop X) = 0
      · obtain ⟨G, rfl⟩ : F ∈ Set.range (map (map WithTop.some)) := by
          grind [mem_range_map_iff, mem_range_map_withTopSome]
        simp only [map_map, hcoe]
        rw [← map_map, hcoe, ← map_sConvexComb, hcoe, sConvexComb_sConvexComb]
      · obtain ⟨v₀, hv₀, hv₀'⟩ : ∃ v, F.weights v ≠ 0 ∧ v.weights ⊤ ≠ 0 := by simpa using hF
        have : v₀ ∈ F.weights.support := by simpa using hv₀
        have h₂ : c F.sConvexComb = ⊤ := by
          simp only [htop, weights_sConvexComb, Finsupp.sum, Finsupp.coe_finsetSum,
            Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ne_eq]
          positivity
        simpa [h₂, htop, ← Finsupp.mem_support_iff] using hF)

@[to_dual (dont_translate := R)]
lemma sConvexComb_withTop_eq_some (hw : w.weights ⊤ = 0) :
    sConvexComb w = ↑(w.untop hw).sConvexComb := dite_eq_left hw

@[to_dual (attr := simp) (dont_translate := R)]
lemma sConvexComb_withTop_eq_top : sConvexComb w = ⊤ ↔ w.weights ⊤ ≠ 0 := by
  classical exact dite_eq_right_iff.trans (by simp)

@[to_dual (attr := simp) (dont_translate := R)]
lemma sConvexComb_map_withTopSome (v : StdSimplex R X) :
    sConvexComb (v.map WithTop.some) = ↑v.sConvexComb := by
  rw [sConvexComb_withTop_eq_some (mem_range_map_withTopSome.1 ⟨v, rfl⟩), untop_map_some]

@[to_dual (attr := fun_prop) (dont_translate := R)]
lemma isAffineMap_withTopSome : IsAffineMap R (.some : X → WithTop X) :=
  ⟨fun v ↦ (sConvexComb_map_withTopSome v).symm⟩

end ConvexSpace
end Convexity
