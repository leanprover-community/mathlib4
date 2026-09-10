/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang, Yaël Dillies
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Interval.Set.Instances
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LSum

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity.Basic

/-!
# Convex spaces

This file defines convex spaces as an algebraic structure supporting finite convex combinations.

## Main definitions

* `Convexity.StdSimplex R X`: A finitely supported probability distribution over elements of `X`
  with coefficients in `R`. The weights are non-negative and sum to 1.
* `Convexity.StdSimplex.map`: Map a function over the support of a standard simplex.
* `Convexity.ConvexSpace R X`: A typeclass for spaces `X` equipped with an operation
  `Convexity.sConvexComb : StdSimplex R X → X` satisfying monadic laws.
* `Convexity.iConvexComb`: Indexed convex combination operator.
* `Convexity.convexCombPair`: Binary convex combinations of two points.

## Design

The design follows a monadic structure where `StdSimplex R` forms a monad and `convexCombination`
is a monadic algebra. This eliminates the need for explicit extensionality axioms and resolves
universe issues with indexed families.

-/

@[expose] public noncomputable section

universe u v w u₁ u₂

open Finsupp

namespace Convexity
variable {R X Y Z I J K : Type*}

/-- The space of nonnegative functions `X → R` which take finitely many non-zero values summing
to 1.

One can interpret this as the standard simplex in `R^⊕X` (`R^X` for finite `X`), with the embedding
being the map `weights : StdSimplex R X → R^⊕X`.

Note in particular that, in the common case where `X := M` is a `R`-module, `StdSimplex R M` is NOT
the standard simplex in `M`. Indeed, the notion of a standard simplex depends on a choice of basis,
and `M` isn't given one. -/
structure StdSimplex (R : Type u) [LE R] [AddCommMonoid R] [One R] (X : Type v) where
  /-- The weights of the `StdSimplex` as a `Finsupp`. -/
  weights : X →₀ R
  /-- All weights are non-negative. -/
  nonneg : 0 ≤ weights
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

attribute [simp] StdSimplex.total
grind_pattern StdSimplex.nonneg => self.weights
grind_pattern StdSimplex.total => self.weights

initialize_simps_projections StdSimplex (as_prefix weights)

namespace StdSimplex
section Semiring
variable {R : Type u} [PartialOrder R] [Semiring R] {w : StdSimplex R X} {x : X}

@[simp] lemma weights_nonneg {w : StdSimplex R X} (i : X) : 0 ≤ w.weights i := w.nonneg i

@[simp] lemma weights_ne_zero [Nontrivial R] : ∀ w : StdSimplex R X, w.weights ≠ 0 := by
  rintro ⟨_, -, total⟩ rfl; simp at total

lemma support_weights_nonempty [Nontrivial R] (w : StdSimplex R X) :
    w.weights.support.Nonempty := by simp

lemma nonempty [Nontrivial R] (w : StdSimplex R X) : Nonempty X :=
  w.support_weights_nonempty.to_type

@[simp] lemma weights_inj {f g : StdSimplex R X} : f.weights = g.weights ↔ f = g := by
  cases f; cases g; simp

@[ext] alias ⟨ext, _⟩ := weights_inj

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by aesop

variable [IsStrictOrderedRing R]

/-- The point mass distribution concentrated at `x`. -/
@[simps weights]
def single (x : X) : StdSimplex R X where
  weights := .single x 1
  nonneg := by simp
  total := by simp

theorem mk_single (x : X) {nonneg total} : (mk (.single x (1 : R)) nonneg total) = single x := rfl

@[simp] lemma support_weights_eq_singleton : w.weights.support = {x} ↔ w = single x where
  mp := by
    rw [support_eq_singleton']
    rintro ⟨a, ha, hwa⟩
    ext : 1
    simp only [hwa, weights_single]
    congr
    simpa [hwa] using w.total
  mpr := by rintro rfl; simp

lemma single_injective : Function.Injective (single (R := R) (X := X)) :=
  fun _ _ h ↦ by simpa using congr_arg (Finsupp.support ∘ weights) h

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total]
    exact Finset.single_le_sum (by simp) (by simpa)

instance [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance [Nontrivial X] : Nontrivial (StdSimplex R X) := by
  obtain ⟨x, y, h⟩ := exists_pair_ne X
  exact ⟨.single x, .single y, single_injective.ne h⟩

instance [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

/-- A probability distribution with weight `s` on `x` and weight `t` on `y`. -/
@[simps weights]
def duple (x y : X) {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) : StdSimplex R X where
  weights := .single x s + .single y t
  nonneg := add_nonneg (by simpa) (by simpa)
  total := by classical simpa [sum_add_index]

/--
Map a function over the support of a standard simplex.
For each n : Y, the weight is the sum of weights of all m : X with g m = n.
-/
@[simps weights]
def map {X : Type v} {Y : Type w} (g : X → Y) (f : StdSimplex R X) : StdSimplex R Y where
  weights := f.weights.mapDomain g
  nonneg := f.weights.mapDomain_nonneg f.nonneg
  total := by simp [sum_mapDomain_index]

@[simp]
lemma map_const (f : StdSimplex R X) (x : Y) : f.map (fun _ ↦ x) = .single x := by
  ext a; by_cases x = a <;> simp [*, mapDomain]

@[simp]
lemma map_single (x : X) (f : X → Y) : (single (R := R) x).map f = .single (f x) := by
  ext; simp

@[simp]
lemma map_duple {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) (f : X → Y) :
    (duple x y hs ht h).map f = duple (f x) (f y) hs ht h := by
  ext; simp [mapDomain_add]

@[simp]
lemma map_id (f : StdSimplex R X) : f.map id = f := by
  ext; simp

lemma map_id' : map (R := R) (id : X → X) = id := by aesop

lemma map_comp (f : StdSimplex R X) (g₁ : X → Y) (g₂ : Y → Z) :
    f.map (g₂ ∘ g₁) = (f.map g₁).map g₂ := by
  ext; simp [← mapDomain_comp]

lemma map_comp' (g₁ : X → Y) (g₂ : Y → Z) :
    map (R := R) (g₂ ∘ g₁) = map g₂ ∘ map g₁ := by
  ext : 1
  simp [map_comp]

lemma map_map (f : StdSimplex R X) (g₁ : X → Y) (g₂ : Y → Z) :
    (f.map g₁).map g₂ = f.map (fun x ↦ g₂ (g₁ x)) :=
  (map_comp ..).symm

lemma mem_range_map_iff
    (f : X → Y) (s : StdSimplex R Y) :
    s ∈ Set.range (map f) ↔ ∀ (x : Y), x ∉ Set.range f → s.weights x = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    intro x hx
    simpa using Finsupp.mapDomain_of_notMem_range s.weights x hx
  · have (i : s.weights.support) : ∃ (m : X), f m = i := by grind
    choose m hm using this
    refine ⟨{
      weights := ∑ (y : s.weights.support), .single (m y) (s.weights y)
      nonneg x := by
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.coe_zero, Pi.zero_apply]
        refine Finset.sum_nonneg fun y ↦ ?_
        obtain rfl | hy := eq_or_ne (m y) x <;> simp [*]
      total := by
        rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp), ← s.total]
        conv_rhs => dsimp [Finsupp.sum]; rw [← Finset.sum_attach]
        congr
        ext
        simp }, ?_⟩
    ext y
    by_cases hy : y ∈ s.weights.support
    · simp only [Finset.univ_eq_attach, weights_map, Finsupp.mapDomain, Finsupp.sum_apply]
      rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp),
        Finset.sum_eq_single ⟨y, hy⟩ ?_ (by simp)]
      · simp [hm]
      · intro z hz hz'
        simp only [hm, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.sum_single_index]
        aesop
    · rw [Finsupp.notMem_support_iff] at hy
      rw [hy]
      refine Finsupp.mapDomain_of_not_mem_image_support ?_
      simp only [Finset.univ_eq_attach, Set.mem_image, SetLike.mem_coe, Finsupp.mem_support_iff,
        Finsupp.coe_finsetSum, Finset.sum_apply, ne_eq, not_exists, not_and]
      intro x hx rfl
      refine hx (Finset.sum_eq_zero (fun z hz ↦ Finsupp.single_eq_of_ne ?_))
      intro rfl
      simp only [hm, ← Finsupp.notMem_support_iff] at hy
      exact hy z.prop

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']
/-- The bijection between the one dimensional standard simplex
and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, by simp⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (by grind) (by grind) (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · simp [sub_eq_iff_eq_add]
    · simp
  right_inv t := by simp

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by aesop

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by aesop

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

/--
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.

Use `ConvexSpace.sConvexComb` instead.
-/
@[simps weights]
def join (f : StdSimplex R (StdSimplex R X)) : StdSimplex R X where
  weights := f.weights.sum (fun d r => r • d.weights)
  nonneg := f.weights.sum_nonneg fun d _ ↦ smul_nonneg (f.nonneg d) d.nonneg
  total := by simp [sum_sum_index, sum_smul_index, ← mul_sum]

private lemma join_join (f : StdSimplex R (StdSimplex R (StdSimplex R X))) :
    f.join.join = (f.map (·.join)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum, mul_smul]

private lemma map_join (f : StdSimplex R (StdSimplex R X)) (g : X → Y) :
    f.join.map g = (f.map (·.map g)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum]

@[simp] private lemma join_single (x : StdSimplex R X) : join (.single x) = x := by
  ext; simp [join, ← mk_single]

end Semiring

section Semifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

private lemma restrict_nonneg_aux {w : StdSimplex K X} {p : X → Prop} [DecidablePred p] :
    0 ≤ (filter p w.weights).sum fun _x k ↦ k :=
  sum_nonneg <| by simp [filter_apply, apply_ite]

private lemma restrict_ne_zero_aux {w : StdSimplex K X} {p : X → Prop} [DecidablePred p]
    (hp : ∃ a, p a ∧ w.weights a ≠ 0) :
    (filter p w.weights).sum (fun _x k ↦ k) ≠ 0 :=
  (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by simpa [ne_iff, filter_apply]).ne'

/-- Project an element of the standard simplex to a lower-dimensional standard simplex,
assuming at least one non-zero weight subsists. -/
def restrict (w : StdSimplex K X) (s : Set X) (hs : ∃ x ∈ s, w.weights x ≠ 0) : StdSimplex K X where
  weights := open scoped Classical in
    ((w.weights.filter (· ∈ s)).sum fun x k ↦ k)⁻¹ • w.weights.filter (· ∈ s)
  nonneg := by
    classical
    exact smul_nonneg (inv_nonneg.2 restrict_nonneg_aux) fun _ ↦ by simp [filter_apply, apply_ite]
  total := by classical simp [sum_smul_index, ← mul_sum, restrict_ne_zero_aux hs]

lemma weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· ∈ s)] :
    (w.restrict s hs).weights =
      ((w.weights.filter (· ∈ s)).sum fun _x k ↦ k)⁻¹ • w.weights.filter (· ∈ s) := by
  simp [restrict]; congr

variable [IsDomain K]

@[simp]
lemma support_weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· ∈ s)] :
    (w.restrict s hs).weights.support = w.weights.support.filter (· ∈ s) := by
  have : (w.weights.filter (· ∈ s)).sum (fun x k ↦ k) ≠ 0 :=
    (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by
      simpa [ne_iff, filter_apply]).ne'
  rw [weights_restrict, support_smul_eq (by convert inv_ne_zero this)]
  simp

@[simp] lemma restrict_singleton (w : StdSimplex K X) (x : X) (hx) :
    w.restrict {x} hx = single x := by
  classical
  simp only [← support_weights_eq_singleton, support_weights_restrict, Set.mem_singleton_iff]
  ext
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.mem_singleton, and_iff_right_iff_imp]
  rintro rfl
  simpa using hx

end Semifield
end StdSimplex

/--
A set equipped with an operation of finite convex combinations,
where the coefficients must be non-negative and sum to 1.
-/
class ConvexSpace (R : Type u) (X : Type v)
    [inst₁ : PartialOrder R] [inst₂ : Semiring R] [inst₃ : IsStrictOrderedRing R] where
  /-- Use `mk` instead. -/
  mk' ::
  /-- Take a convex combination with the given probability distribution over points. -/
  /- FIXME: Lean makes `inst₁`, `inst₂`, `inst₃` implicit by default, which renders `sConvexComb`
  unusable without these manual `[inst]` binders. Why is this so? Shouldn't typeclass arguments to
  a `structure` also be typeclass arguments to its fields? -/
  sConvexComb [inst₁] [inst₂] [inst₃] (f : StdSimplex R X) : X
  /-- A convex combination of a single point is that point. -/
  sConvexComb_single (x : X) : sConvexComb (.single x) = x
  /-- Associativity of convex combination (monadic join law).

  Use `sConvexComb_sConvexComb` instead. -/
  assoc (f : StdSimplex R (StdSimplex R X)) :
    sConvexComb (f.map sConvexComb) = sConvexComb f.join

open ConvexSpace StdSimplex

variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace R Z]

export ConvexSpace (sConvexComb sConvexComb_single)

attribute [simp] sConvexComb_single

@[deprecated (since := "2026-05-04")] alias ConvexSpace.convexCombination := sConvexComb

@[deprecated (since := "2026-05-04")]
alias ConvexSpace.convexCombination_single := sConvexComb_single

/-- Take a convex combination with the given weight distribution of an indexed family of points. -/
def iConvexComb (s : StdSimplex R I) (f : I → X) : X := sConvexComb (s.map f)

/-- Take a convex combination of two points. -/
def convexCombPair (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (x y : X) : X :=
  sConvexComb (.duple x y hs ht hst)

@[deprecated (since := "2026-05-15")] alias convexComboPair := convexCombPair

namespace StdSimplex

-- We export `sConvexComb` and `iConvexComb` to allow dot notation on the `StdSimplex` argument.
export ConvexSpace (sConvexComb)
export Convexity (iConvexComb)

instance : ConvexSpace R (StdSimplex R I) where
  sConvexComb σ := σ.join
  assoc f := by exact (join_join f).symm
  sConvexComb_single := by exact join_single

@[simp] lemma weights_sConvexComb (f : StdSimplex R (StdSimplex R I)) :
    f.sConvexComb.weights = f.weights.sum (fun d r => r • d.weights) :=
  StdSimplex.weights_join _

@[simp] lemma weights_iConvexComb (w : StdSimplex R I) (f : I → StdSimplex R I) :
    (iConvexComb w f).weights = w.weights.sum (fun i r => r • (f i).weights) := by
  simp [iConvexComb, sum_mapDomain_index, add_smul]

@[simp] lemma weights_convexCombPair (w w' : StdSimplex R I) (s t : R) (hs ht hst) :
    (convexCombPair s t hs ht hst w w').weights = s • w.weights + t • w'.weights := by
  classical simp [convexCombPair, sum_add_index, add_smul]

lemma map_sConvexComb (s : StdSimplex R (StdSimplex R I)) (f : I → J) :
    s.sConvexComb.map f = (s.map (map f)).sConvexComb :=
  StdSimplex.map_join s f

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  aesop

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

lemma convexCombPair_restrict_restrict_compl (w : StdSimplex K I) (s : Set I) (hs hs')
    [DecidablePred (· ∈ s)] :
    convexCombPair
      ((w.weights.filter (· ∈ s)).sum fun _x k ↦ k)
      ((w.weights.filter (· ∉ s)).sum fun _x k ↦ k)
      (by exact restrict_nonneg_aux) (by exact restrict_nonneg_aux) (by simp)
      (w.restrict s hs) (w.restrict sᶜ hs') = w := by
  ext : 1
  simp only [Set.mem_compl_iff] at hs'
  simp [weights_restrict, smul_inv_smul₀, restrict_ne_zero_aux, hs, hs']

end StdSimplex

lemma sConvexComb_sConvexComb (f : StdSimplex R (StdSimplex R X)) :
    f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvexComb :=
  (ConvexSpace.assoc f).symm

lemma sConvexComb_convexCombPair (s t : R) (hs ht hst) (w w' : StdSimplex R X) :
    (convexCombPair s t hs ht hst w w').sConvexComb =
      convexCombPair s t hs ht hst w.sConvexComb w'.sConvexComb := by
  simp [convexCombPair, sConvexComb_sConvexComb]

/-- The public constructor for `ConvexSpace`. -/
abbrev ConvexSpace.mk {X : Type*} (sConvexComb : StdSimplex R X → X)
    (single : ∀ x : X, sConvexComb (.single x) = x)
    (assoc : ∀ f : StdSimplex R (StdSimplex R X),
      sConvexComb (f.map sConvexComb) = sConvexComb f.sConvexComb) : ConvexSpace R X :=
  ⟨sConvexComb, single, assoc⟩

variable (R) in
/-- A map between convex spaces is affine if it preserves convex combinations.

TODO: Show that this generalises affine maps between affine spaces, see `AffineMap`. -/
@[fun_prop]
structure IsAffineMap (f : X → Y) : Prop where
  map_sConvexComb (s : StdSimplex R X) : f s.sConvexComb = (s.map f).sConvexComb

@[fun_prop]
protected lemma IsAffineMap.id : IsAffineMap R (id : X → X) where
  map_sConvexComb s := by simp

@[fun_prop]
lemma IsAffineMap.comp {g : Y → Z} (hg : IsAffineMap R g) {f : X → Y} (hf : IsAffineMap R f) :
    IsAffineMap R (g ∘ f) where
  map_sConvexComb s := by
    simp [StdSimplex.map_comp, hf.map_sConvexComb, hg.map_sConvexComb]

@[fun_prop]
lemma IsAffineMap.const (x : Y) :
    IsAffineMap R (fun (_ : X) ↦ x) where
  map_sConvexComb _ := by simp

variable (R) in
@[fun_prop]
lemma StdSimplex.isAffineMap_map (f : I → J) : IsAffineMap R (StdSimplex.map (R := R) f) :=
  ⟨(map_sConvexComb · f)⟩

section iConvexComb

lemma sConvexComb_map (w : StdSimplex R I) (f : I → X) :
    sConvexComb (w.map f) = iConvexComb w f := rfl

@[simp] lemma iConvexComb_const (s : StdSimplex R I) (m : X) :
    s.iConvexComb (fun _ ↦ m) = m := by simp [iConvexComb]

@[simp] lemma iConvexComb_single (i : I) (f : I → X) :
    (single (R := R) i).iConvexComb f = f i := by simp [iConvexComb]

lemma iConvexComb_id (w : StdSimplex R X) : w.iConvexComb id = w.sConvexComb := by
  simp [iConvexComb]

@[simp] lemma iConvexComb_id' (w : StdSimplex R X) :
    w.iConvexComb (fun x ↦ x) = w.sConvexComb := iConvexComb_id _

@[simp] lemma iConvexComb_map (s : StdSimplex R I) (f : I → J) (g : J → X) :
    (s.map f).iConvexComb g = s.iConvexComb (fun i ↦ g (f i)) := by
  simp only [iConvexComb, map_map]

@[congr] lemma iConvexComb_congr {w : StdSimplex R I} {f g : I → X}
    (hfg : ∀ i, w.weights i ≠ 0 → f i = g i) :
    w.iConvexComb f = w.iConvexComb g := by
  refine congr(sConvexComb $(?_))
  ext i
  simp only [weights_map]
  -- TODO: This should just be `congr! 2 with i hi`.
  congr 1
  refine Finsupp.mapDomain_congr fun i hi ↦ ?_
  exact hfg i (by simpa using hi)

lemma iConvexComb_reindex (s : StdSimplex R I) (f : I ≃ J) (g : I → X) :
    s.iConvexComb g = (s.map f).iConvexComb (g ∘ f.symm) := by
  simp [iConvexComb_map]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'` and `iConvexComb_assoc` for non-dependent versions. -/
lemma iConvexComb_assoc''
    {J : I → Type*} (s : StdSimplex R I) (f : Π i, StdSimplex R (J i)) (g : Π i, J i → X) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb (g i)) =
      (s.iConvexComb fun i ↦ (f i).map (⟨i, ·⟩)).iConvexComb (Sigma.uncurry g) := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Sigma.uncurry]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc''` for a more dependent version, and `iConvexComb_assoc`
for a less dependent one. -/
lemma iConvexComb_assoc' {J : Type*} (s : StdSimplex R I) (f : I → StdSimplex R J)
    (g : I → J → X) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb (g i)) =
      (s.iConvexComb fun i ↦ (f i).map (⟨i, ·⟩)).iConvexComb g.uncurry := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Function.uncurry]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'`, `iConvexComb_assoc''` for more dependent versions. -/
lemma iConvexComb_assoc {J : Type*} (s : StdSimplex R I) (f : I → StdSimplex R J)
    (g : J → X) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb g) = (s.iConvexComb f).iConvexComb g := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  simp [map_sConvexComb, map_map]

variable {R X I J : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R X] in
lemma iConvexComb_comm (f : StdSimplex R I) (g : StdSimplex R J)
    (e : I → J → X) :
    f.iConvexComb (fun i ↦ g.iConvexComb (e i)) =
      g.iConvexComb fun j ↦ f.iConvexComb fun i ↦ e i j := by
  rw [iConvexComb_assoc', iConvexComb_assoc', iConvexComb_reindex _ (.prodComm ..)]
  congr
  suffices (f.map fun x ↦ g.map (Prod.mk · x)).sConvexComb =
      (g.map (f.map ∘ Prod.mk)).sConvexComb by
    simpa [iConvexComb, map_sConvexComb, map_map, Function.comp_def]
  ext1
  simp [mapDomain, sum_sum_index, add_smul, smul_sum, mul_comm, sum_comm f.weights g.weights]

lemma IsAffineMap.map_iConvexComb {f : X → Y} (hf : IsAffineMap R f)
    (s : StdSimplex R I) (g : I → X) : f (s.iConvexComb g) = s.iConvexComb (f ∘ g) := by
  simp [iConvexComb, hf.map_sConvexComb, map_comp]

lemma map_iConvexComb {f : J → K}
    (s : StdSimplex R I) (g : I → StdSimplex R J) :
    (s.iConvexComb g).map f = s.iConvexComb (map f ∘ g) :=
  (isAffineMap_map R f).map_iConvexComb s g

@[simp]
lemma sConvexComb_map_iConvexComb (f : I → X) (s : StdSimplex R (StdSimplex R I)) :
    sConvexComb (map (fun s ↦ iConvexComb s f) s) = iConvexComb (sConvexComb s) f :=
  calc
    _ = iConvexComb s fun s ↦ sConvexComb (map f s) := sConvexComb_map _ _
    _ = sConvexComb (map f (sConvexComb s)) := by
        rw [StdSimplex.map_sConvexComb, sConvexComb_sConvexComb, sConvexComb_map,
          iConvexComb_map]

end iConvexComb

variable {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)
variable {s' t' : R} (hs' : 0 ≤ s') (ht' : 0 ≤ t') (h' : s' + t' = 1)
variable {s'' t'' : R} (hs'' : 0 ≤ s'') (ht'' : 0 ≤ t'') (h'' : s'' + t'' = 1)

lemma convexCombPair_def (p q : X) :
    convexCombPair s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexComb ![p, q] := by
  simp [StdSimplex.iConvexComb, convexCombPair]

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
@[simp]
theorem convexCombPair_zero {x y : X} :
    convexCombPair (0 : R) 1 (by simp) (by simp) (by simp) x y = y := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_zero := convexCombPair_zero

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
@[simp]
theorem convexCombPair_one {x y : X} :
    convexCombPair (1 : R) 0 (by simp) (by simp) (by simp) x y = x := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_one := convexCombPair_one

/-- A convex combination of a point with itself is that point. -/
@[simp]
theorem convexCombPair_same {x : X} :
    convexCombPair s t hs ht h x x = x := by
  unfold convexCombPair
  convert sConvexComb_single x
  simp only [StdSimplex.duple, StdSimplex.single, ← single_add, h]

@[deprecated (since := "2026-05-15")] alias convexComboPair_symm := convexCombPair_same

theorem convexCombPair_symm {x y : X} :
    convexCombPair s t hs ht h x y = convexCombPair t s ht hs ((add_comm _ _).trans h) y x := by
  unfold convexCombPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]

lemma IsAffineMap.map_convexCombPair {f : X → Y} (hf : IsAffineMap R f)
    {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    f (convexCombPair s t hs ht h x y) = convexCombPair s t hs ht h (f x) (f y) := by
  simp [hf.map_sConvexComb, convexCombPair]

set_option backward.isDefEq.respectTransparency.types false in
/-- Flattening with the outer combination specialized to `convexCombPair`. -/
lemma convexCombPair_iConvexComb_iConvexComb {J₁ : Type u₁} {J₂ : Type u₂}
    (g₁ : StdSimplex R J₁) (g₂ : StdSimplex R J₂)
    (m₁ : J₁ → X) (m₂ : J₂ → X) :
    convexCombPair s t hs ht h (g₁.iConvexComb m₁) (g₂.iConvexComb m₂) =
      (convexCombPair s t hs ht h (g₁.map m₁) (g₂.map m₂)).sConvexComb := by
  have := iConvexComb_assoc'' (I := Fin 2) (.duple 0 1 hs ht h)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (X := X) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexComb, map_sConvexComb, map_map, Sigma.uncurry] at this
  simpa [convexCombPair, ← convexCombPair_def]

/-- Flattening with the inner combination specialized to `convexCombPair`. -/
lemma iConvexComb_convexCombPair
    (s t : I → R) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i) (h : ∀ i, s i + t i = 1)
    (f : StdSimplex R I) (m₁ m₂ : I → X) :
    f.iConvexComb (fun i ↦ convexCombPair (s i) (t i) (hs i) (ht i) (h i) (m₁ i) (m₂ i)) =
    (f.iConvexComb fun i ↦ duple (m₁ i) (m₂ i) (hs i) (ht i) (h i)).sConvexComb := by
  have := iConvexComb_assoc' (I := I) (J := Fin 2) (R := R) (X := X) f
    (fun i ↦ .duple 0 1 (hs i) (ht i) (h i)) (fun i ↦ ![m₁ i, m₂ i])
  simp [iConvexComb, map_sConvexComb, map_map] at this
  simp only [← convexCombPair.eq_def] at this
  simp only [← iConvexComb.eq_def] at this
  simpa [convexCombPair, ← convexCombPair_def]

lemma convexCombPair_iConvexComb_left (g : StdSimplex R J) (e : J → X) (m : X) :
    convexCombPair s t hs ht h (g.iConvexComb e) m =
      (convexCombPair s t hs ht h (g.map e) (single m)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g e (fun _ ↦ m)

lemma convexCombPair_iConvexComb_right (m : X) (g : StdSimplex R J) (e : J → X) :
    convexCombPair s t hs ht h m (g.iConvexComb e) =
      (convexCombPair s t hs ht h (.single m) (g.map e)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g (fun _ ↦ m) e

/-- Flattening nested binary convex combination into a single convex combination. -/
lemma convexCombPair_convexCombPair_left_eq_sConvexComb (m₁ m₂ m₃ : X) :
    convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ =
      (convexCombPair s t hs ht h (duple m₁ m₂ hs' ht' h') (single m₃)).sConvexComb := by
  simpa using! convexCombPair_iConvexComb_left hs ht h (.duple m₁ m₂ hs' ht' h') id m₃

/-- Flattening nested binary convex combination into a single convex combination. -/
lemma convexCombPair_convexCombPair_right_eq_sConvexComb (m₁ m₂ m₃ : X) :
    convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) =
      (convexCombPair s t hs ht h (.single m₁) (duple m₂ m₃ hs' ht' h')).sConvexComb := by
  simpa using! convexCombPair_iConvexComb_right hs ht h m₁ (.duple m₂ m₃ hs' ht' h') id

lemma convexCombPair_convexCombPair_assoc_left (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : X) :
    convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ =
      convexCombPair (s * s') (s * t' + t) (by positivity) (by positivity)
        (by rw [← add_assoc, ← mul_add, h', mul_one, h]) m₁
        (convexCombPair s'' t'' hs'' ht'' h'' m₂ m₃) := by
  classical
  rw [convexCombPair_convexCombPair_left_eq_sConvexComb,
    convexCombPair_convexCombPair_right_eq_sConvexComb]
  congr 1
  ext1
  have : s * (t' * t'') + t * t'' = t := by rw [← mul_assoc, ← H, ← mul_add, h'', mul_one]
  simp [convexCombPair, sum_add_index, add_smul, ← single_add, H, mul_assoc, ← mul_add, h'',
    add_assoc, this]

lemma convexCombPair_convexCombPair_assoc_right (H : s * t'' = t * s' * s'') (m₁ m₂ m₃ : X) :
    convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) =
      convexCombPair (s + t * s') (t * t') (by positivity) (by positivity)
        (by rw [add_assoc, ← mul_add, h', mul_one, h])
        (convexCombPair s'' t'' hs'' ht'' h'' m₁ m₂) m₃ := by
  simp only [add_comm s]
  rw [convexCombPair_symm, convexCombPair_symm (x := m₂),
    convexCombPair_convexCombPair_assoc_left (hs'' := ht'') (ht'' := hs'')
      (h'' := (add_comm _ _).trans h'') (H := H),
    convexCombPair_symm, convexCombPair_symm (x := m₂)]

section CommSemiring

variable {R X I : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R X] {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)

lemma iConvexComb_convexCombPair_comm (f : StdSimplex R I) (e₁ e₂ : I → X) :
    f.iConvexComb (fun x ↦ convexCombPair s t hs ht h (e₁ x) (e₂ x)) =
      convexCombPair s t hs ht h (f.iConvexComb e₁) (f.iConvexComb e₂) := by
  simp only [convexCombPair_def]
  convert (iConvexComb_comm (.duple 0 1 hs ht h) f ![e₁, e₂]).symm with i _ j _ j
  · fin_cases j <;> simp
  · fin_cases j <;> simp

lemma iConvexComb_convexCombPair_comm_left (f : StdSimplex R I) (m : X) (e : I → X) :
    f.iConvexComb (fun x ↦ convexCombPair s t hs ht h (e x) m) =
    convexCombPair s t hs ht h (f.iConvexComb e) m := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f e (fun _ ↦ m)

lemma iConvexComb_convexCombPair_comm_right (f : StdSimplex R I) (m : X) (e : I → X) :
    f.iConvexComb (convexCombPair s t hs ht h m <| e ·) =
    convexCombPair s t hs ht h m (f.iConvexComb e) := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f (fun _ ↦ m) e

lemma isAffineMap_convexCombPair (m : X) :
    IsAffineMap R (convexCombPair s t hs ht h m) :=
  ⟨fun f ↦ by simpa using! (iConvexComb_convexCombPair_comm_right hs ht h f m id).symm⟩

end CommSemiring

end Convexity
