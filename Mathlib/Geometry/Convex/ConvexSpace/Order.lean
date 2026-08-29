/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Ordered convex spaces

This file orders the standard simplex over a partial order by stochastic dominance and defines
ordered convex spaces, namely convex spaces over a partial order in which taking convex
combinations is monotone.

## Main declarations

* `Convexity.StdSimplex.upperMass`: The upper mass function of a distribution `w` over a partial
  order, namely the map sending `x` to the total weight `w` puts on `{y | x ≤ y}`.
* `Convexity.StdSimplex.instPartialOrder`: The stochastic dominance order on `StdSimplex R X`,
  namely the order induced by the pointwise order on upper mass functions.
* `Convexity.IsOrderedConvexSpace`: Typeclass for a convex space over a partial order in which
  `sConvexComb` is monotone for stochastic dominance.
-/

open Finsupp

public section

namespace Convexity
variable {I R X : Type*}

namespace StdSimplex
section PartialOrder
variable [Semiring R] [PartialOrder R] [PartialOrder X] {w w₁ w₂ : StdSimplex R X} {x y : X}

variable (w) in
/-- The upper mass function of a distribution `w` over a partial order: `w.upperMass x` is the
total weight that `w` puts on the up-set of `x`.

This is the (complementary) cumulative distribution function of `w`, and it determines `w`.
See `StdSimplex.upperMass_injective`. -/
noncomputable def upperMass (x : X) : R :=
  open scoped Classical in (w.weights.filter (x ≤ ·)).sum fun _y r ↦ r

lemma upperMass_eq_finsuppSum [DecidableLE X] (w : StdSimplex R X) (x : X) :
    w.upperMass x = (w.weights.filter (x ≤ ·)).sum fun _y r ↦ r := by rw [upperMass]; congr!

lemma upperMass_eq_sum [DecidableLE X] (w : StdSimplex R X) (x : X) :
    w.upperMass x = ∑ y ∈ w.weights.support with x ≤ y, w.weights y := by
  rw [upperMass_eq_finsuppSum, sum_filter_index, support_filter]

/-- If no point of the support of `w` lies strictly between `x` and `y`, then the mass `w` puts
above `x` is the mass it puts on `x` plus the mass it puts above `y`. -/
lemma upperMass_eq_weights_add_upperMass (hxy : x < y) (hm : ∀ z, w.weights z ≠ 0 → x < z → y ≤ z) :
    w.upperMass x = w.weights x + w.upperMass y := by
  classical
  have : w.weights.filter (x ≤ ·) = .single x (w.weights x) + w.weights.filter (y ≤ ·) := by
    ext z; simp [filter_apply]; grind [lt_of_le_of_ne]
  simp [upperMass, this, sum_add_index']

open scoped Classical in
/-- The mass `w` puts above `x` is the mass it puts on `x` plus the mass it puts strictly above
`x`. -/
lemma upperMass_eq_weights_add_sum (w : StdSimplex R X) (x : X) :
    w.upperMass x = w.weights x + ∑ y ∈ w.weights.support with x < y, w.weights y := by
  have : w.weights.filter (x ≤ ·) = .single x (w.weights x) + w.weights.filter (x < ·) := by
    ext z; simp [filter_apply]; grind [lt_of_le_of_ne]
  simp [upperMass, this, sum_add_index', sum_filter_index]

/-- If no point of the support of `w` lies strictly above `x`, then the mass `w` puts above `x` is
exactly the mass it puts on `x`. -/
lemma upperMass_eq_weights (hx : ∀ y, w.weights y ≠ 0 → ¬ x < y) : w.upperMass x = w.weights x := by
  classical
  have : w.weights.filter (x ≤ ·) = .single x (w.weights x) := by
    ext y; simp [filter_apply]; grind [lt_of_le_of_ne]
  rw [upperMass, this, sum_single_index rfl]

@[simp] lemma upperMass_top [OrderTop X] (w : StdSimplex R X) : w.upperMass ⊤ = w.weights ⊤ :=
  upperMass_eq_weights fun _ _ ↦ not_top_lt

variable [IsStrictOrderedRing R]

@[simp] lemma upperMass_nonneg (w : StdSimplex R X) (x : X) : 0 ≤ w.upperMass x := by
  classical rw [upperMass_eq_sum]; exact Finset.sum_nonneg fun _ _ ↦ w.weights_nonneg _

@[simp] lemma upperMass_single [DecidableLE X] (x y : X) :
    (single x : StdSimplex R X).upperMass y = if y ≤ x then 1 else 0 := by
  rw [upperMass_eq_sum, weights_single]; split <;> simp [Finset.filter_singleton, *]

omit [IsStrictOrderedRing R] in
lemma upperMass_add_sum_not [DecidableLE X] (w : StdSimplex R X) (x : X) :
    w.upperMass x + ∑ y ∈ w.weights.support with ¬ x ≤ y, w.weights y = 1 := by
  rw [upperMass_eq_sum, Finset.sum_filter_add_sum_filter_not]
  simpa [Finsupp.sum] using w.total

@[simp] lemma upperMass_le_one (w : StdSimplex R X) (x : X) : w.upperMass x ≤ 1 := by
  classical
  rw [← upperMass_add_sum_not w x]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ w.weights_nonneg _)

/-- `w` puts all of its mass above `x` exactly when its support lies above `x`. -/
lemma upperMass_eq_one_iff : w.upperMass x = 1 ↔ ∀ y, w.weights y ≠ 0 → x ≤ y := by
  classical
  have h := upperMass_add_sum_not w x
  refine ⟨fun h1 y hy ↦ ?_, fun hall ↦ ?_⟩
  · rw [h1] at h
    have hz := add_left_cancel (h.trans (add_zero 1).symm)
    by_contra! hxy
    exact hy <| (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ w.weights_nonneg _).1 hz y <| by
      simp [hy, hxy]
  · rwa [Finset.sum_eq_zero fun y ↦ by simp +contextual [hall], add_zero] at h

/-- A distribution over a partial order is determined by its upper mass function. -/
lemma upperMass_injective : (upperMass : StdSimplex R X → X → R).Injective := by
  classical
  rintro w₁ w₂ h
  ext x
  set S := w₁.weights.support ∪ w₂.weights.support with hS
  -- The mass `w` puts above `x` is the mass it puts on `x` plus the mass it puts on the elements
  -- of `S` strictly above `x`.
  have key (w : StdSimplex R X) (hw : w.weights.support ⊆ S) (x : X) :
      w.upperMass x = w.weights x + ∑ y ∈ S with x < y, w.weights y := by
    rw [upperMass_eq_weights_add_sum]
    congr 1
    exact Finset.sum_subset (by gcongr) <| by simp_all
  have key' (x : X) :
      w₁.weights x + ∑ y ∈ S with x < y, w₁.weights y
        = w₂.weights x + ∑ y ∈ S with x < y, w₂.weights y :=
    (key w₁ Finset.subset_union_left x).symm.trans
      ((congrFun h x).trans (key w₂ Finset.subset_union_right x))
  -- We prove that `w₁` and `w₂` agree at `x` by induction on the number of elements of `S` lying
  -- strictly above `x`.
  have main n x (hx : Finset.card {y ∈ S | x < y} ≤ n) : w₁.weights x = w₂.weights x := by
    induction n generalizing x with
    | zero =>
      have h₀ : {y ∈ S | x < y} = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hx)
      simpa [h₀] using key' x
    | succ n ih =>
      have hsum : ∑ y ∈ S with x < y, w₁.weights y = ∑ y ∈ S with x < y, w₂.weights y := by
        congr! 1 with y hy
        refine ih y ?_
        simp only [Finset.mem_filter] at hy
        -- The elements of `S` strictly above `y` are strictly above `x`, but `y` isn't
        have hss : {z ∈ S | y < z} ⊂ {z ∈ S | x < z} := by
          refine (Finset.ssubset_iff_of_subset fun z hz ↦ ?_).2 ⟨y, by simp [hy.1, hy.2], by simp⟩
          simp only [Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, hy.2.trans hz.2⟩
        exact Nat.lt_succ_iff.1 <| (Finset.card_lt_card hss).trans_le hx
      exact add_right_cancel (hsum ▸ key' x)
  exact main _ x le_rfl

/-- The standard simplex indexed by a partial order is partially ordered by stochastic dominance.
`w₁ ≤ w₂` iff on each lower set the weight of `w₁` is less than that of `w₂`. -/
noncomputable instance instPartialOrder : PartialOrder (StdSimplex R X) :=
  .lift upperMass upperMass_injective

lemma le_def : w₁ ≤ w₂ ↔ ∀ x, w₁.upperMass x ≤ w₂.upperMass x := .rfl

@[gcongr] alias ⟨upperMass_le_upperMass, _⟩ := le_def

lemma forall_le_of_le (h : w₁ ≤ w₂) (h₁ : ∀ ⦃y⦄, w₁.weights y ≠ 0 → x ≤ y) :
    ∀ ⦃y⦄, w₂.weights y ≠ 0 → x ≤ y := by
  rw [← upperMass_eq_one_iff] at h₁ ⊢
  exact le_antisymm (upperMass_le_one _ _) (h₁ ▸ le_def.1 h x)

@[simp] lemma upperMass_map [DecidableLE X] (w : StdSimplex R I) (f : I → X) (x : X) :
    (w.map f).upperMass x = (w.weights.filter fun i ↦ x ≤ f i).sum fun _i r ↦ r := by
  simp [upperMass_eq_finsuppSum, sum_mapDomain_index]

lemma monotone_map {w : StdSimplex R I} : Monotone (w.map : (I → X) → StdSimplex R X) := by
  classical
  rintro f g hfg x
  rw [upperMass_map, upperMass_map, sum_filter_index, sum_filter_index, support_filter,
    support_filter]
  gcongr
  · simp
  · exact hfg _

@[gcongr] lemma map_le_map {w : StdSimplex R I} {f g : I → X} (hfg : f ≤ g) : w.map f ≤ w.map g :=
  monotone_map hfg

@[simp] lemma single_le_single_iff : (single x : StdSimplex R X) ≤ single y ↔ x ≤ y := by
  classical
  refine ⟨fun h ↦ ?_, fun hxm ↦ le_def.2 fun z ↦ ?_⟩
  · have hx := le_def.1 h x
    simp only [upperMass_single, le_refl, ite_true] at hx
    by_contra hxm
    rw [ite_eq_right_iff.2 fun h ↦ absurd h hxm] at hx
    exact absurd hx zero_lt_one.not_ge
  · simp only [upperMass_single]
    split_ifs with hzx hzm hzm
    · exact le_rfl
    · exact absurd (hzx.trans hxm) hzm
    · exact zero_le_one
    · exact le_rfl

@[gcongr] alias ⟨_, single_le_single⟩ := single_le_single_iff

lemma monotone_single : Monotone (single : X → StdSimplex R X) := fun _x _m ↦ single_le_single

end PartialOrder
end StdSimplex

section IsOrderedConvexSpace
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [PartialOrder X] [ConvexSpace R X]

variable (R X) in
/-- A convex space over a partial order is *ordered* if taking convex combinations is monotone for
the stochastic dominance order on the standard simplex.

Equivalently, replacing the points of a convex combination by larger points, or moving weight from
smaller points to larger ones, can only increase the combination. -/
class IsOrderedConvexSpace : Prop where
  /-- Taking convex combinations is monotone for stochastic dominance. -/
  monotone_sConvexComb : Monotone (sConvexComb : StdSimplex R X → X)

export IsOrderedConvexSpace (monotone_sConvexComb)

variable [IsOrderedConvexSpace R X] {v : StdSimplex R I} {w₁ w₂ : StdSimplex R X} {f g : I → X}

@[gcongr]
lemma sConvexComb_le_sConvexComb (h : w₁ ≤ w₂) : w₁.sConvexComb ≤ w₂.sConvexComb :=
  monotone_sConvexComb h

lemma monotone_iConvexComb (v : StdSimplex R I) : Monotone (v.iConvexComb : (I → X) → X) :=
  fun _f _g hfg ↦ monotone_sConvexComb <| StdSimplex.monotone_map hfg

@[gcongr]
lemma iConvexComb_le_iConvexComb (hfg : f ≤ g) : v.iConvexComb f ≤ v.iConvexComb g :=
  monotone_iConvexComb _ hfg

@[gcongr]
lemma convexCombPair_le_convexCombPair {a b : R} (ha hb hab) {x₁ x₂ y₁ y₂ : X} (hx : x₁ ≤ x₂)
    (hy : y₁ ≤ y₂) :
    convexCombPair a b ha hb hab x₁ y₁ ≤ convexCombPair a b ha hb hab x₂ y₂ := by
  simp only [convexCombPair_def]
  exact iConvexComb_le_iConvexComb (Fin.forall_fin_two.2 ⟨by simpa using hx, by simpa using hy⟩)

end IsOrderedConvexSpace
end Convexity
