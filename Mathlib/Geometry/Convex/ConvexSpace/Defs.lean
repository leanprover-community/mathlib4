/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang, Yaël Dillies
-/
module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LSum

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity.Basic

/-!
# Convex spaces

This file defines convex spaces as an algebraic structure supporting finite convex combinations.

## Main definitions

* `Convexity.StdSimplex R M`: A finitely supported probability distribution over elements of `M`
  with coefficients in `R`. The weights are non-negative and sum to 1.
* `Convexity.StdSimplex.map`: Map a function over the support of a standard simplex.
* `Convexity.ConvexSpace R M`: A typeclass for spaces `M` equipped with an operation
  `Convexity.sConvexComb : StdSimplex R M → M` satisfying monadic laws.
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
variable {R X M N P I J K : Type*}

/--
A finitely supported probability distribution over elements of `M` with coefficients in `R`.
The weights are non-negative and sum to 1.
-/
structure StdSimplex (R : Type u) [LE R] [AddCommMonoid R] [One R] (M : Type v) where
  /-- The weights of the `StdSimplex` as a `Finsupp`. -/
  weights : M →₀ R
  /-- All weights are non-negative. -/
  nonneg : 0 ≤ weights
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

attribute [simp] StdSimplex.total
grind_pattern StdSimplex.nonneg => self.weights
grind_pattern StdSimplex.total => self.weights

initialize_simps_projections StdSimplex (as_prefix weights)

namespace StdSimplex
variable {R : Type u} [PartialOrder R] [Semiring R] {M N P : Type*} {w : StdSimplex R M} {x : M}

@[simp] lemma weights_nonneg {w : StdSimplex R M} (i : M) : 0 ≤ w.weights i := w.nonneg i

@[simp] lemma weights_ne_zero [Nontrivial R] : ∀ w : StdSimplex R M, w.weights ≠ 0 := by
  rintro ⟨_, -, total⟩ rfl; simp at total

lemma support_weights_nonempty [Nontrivial R] (w : StdSimplex R M) :
    w.weights.support.Nonempty := by simp

lemma nonempty [Nontrivial R] (w : StdSimplex R M) : Nonempty M :=
  w.support_weights_nonempty.to_type

@[simp] lemma weights_inj {f g : StdSimplex R M} : f.weights = g.weights ↔ f = g := by
  cases f; cases g; simp

@[ext] alias ⟨ext, _⟩ := weights_inj

variable [IsStrictOrderedRing R]

/-- The point mass distribution concentrated at `x`. -/
@[simps weights]
def single (x : M) : StdSimplex R M where
  weights := .single x 1
  nonneg := by simp
  total := by simp

theorem mk_single (x : M) {nonneg total} : (mk (.single x (1 : R)) nonneg total) = single x := rfl

@[simp] lemma support_weights_eq_singleton : w.weights.support = {x} ↔ w = single x where
  mp := by
    classical
    rw [support_eq_singleton']
    rintro ⟨a, ha, hwa⟩
    ext : 1
    simp only [hwa, weights_single]
    congr
    simpa [hwa] using w.total
  mpr := by rintro rfl; simp

/-- A probability distribution with weight `s` on `x` and weight `t` on `y`. -/
@[simps weights]
def duple (x y : M) {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) : StdSimplex R M where
  weights := .single x s + .single y t
  nonneg := add_nonneg (by simpa) (by simpa)
  total := by classical simpa [sum_add_index]

/--
Map a function over the support of a standard simplex.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
@[simps weights]
def map {M : Type v} {N : Type w} (g : M → N) (f : StdSimplex R M) : StdSimplex R N where
  weights := f.weights.mapDomain g
  nonneg := f.weights.mapDomain_nonneg f.nonneg
  total := by simp [sum_mapDomain_index]

@[simp]
lemma map_const (f : StdSimplex R M) (x : N) : f.map (fun _ ↦ x) = .single x := by
  ext a; by_cases x = a <;> simp [*, mapDomain]

@[simp]
lemma map_single (x : M) (f : M → N) : (single (R := R) x).map f = .single (f x) := by
  ext; simp

@[simp]
lemma map_duple {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) (f : M → N) :
    (duple x y hs ht h).map f = duple (f x) (f y) hs ht h := by
  ext; simp [mapDomain_add]

@[simp]
lemma map_id (f : StdSimplex R M) : f.map id = f := by
  ext; simp

lemma map_comp (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    f.map (g₂ ∘ g₁) = (f.map g₁).map g₂ := by
  ext; simp [mapDomain_comp]

lemma map_map (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    (f.map g₁).map g₂ = f.map (fun x ↦ g₂ (g₁ x)) :=
  (map_comp ..).symm

/--
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.

Use `ConvexSpace.sConvexComb` instead.
-/
@[simps weights]
def join (f : StdSimplex R (StdSimplex R M)) : StdSimplex R M where
  weights := f.weights.sum (fun d r => r • d.weights)
  nonneg := f.weights.sum_nonneg fun d _ ↦ smul_nonneg (f.nonneg d) d.nonneg
  total := by simp [sum_sum_index, sum_smul_index, ← mul_sum]

private lemma join_join (f : StdSimplex R (StdSimplex R (StdSimplex R M))) :
    f.join.join = (f.map (·.join)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum, mul_smul]

private lemma map_join (f : StdSimplex R (StdSimplex R M)) (g : M → N) :
    f.join.map g = (f.map (·.map g)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum]

@[simp] private lemma join_single (x : StdSimplex R M) : join (.single x) = x := by
  ext; simp [join, ← mk_single]

end StdSimplex

/--
A set equipped with an operation of finite convex combinations,
where the coefficients must be non-negative and sum to 1.
-/
class ConvexSpace (R : Type u) (M : Type v)
    [inst₁ : PartialOrder R] [inst₂ : Semiring R] [inst₃ : IsStrictOrderedRing R] where
  /-- Use `mk` instead. -/
  mk' ::
  /-- Take a convex combination with the given probability distribution over points. -/
  /- FIXME: Lean makes `inst₁`, `inst₂`, `inst₃` implicit by default, which renders `sConvexComb`
  unusable without these manual `[inst]` binders. Why is this so? Shouldn't typeclass arguments to
  a `structure` also be typeclass arguments to its fields? -/
  sConvexComb [inst₁] [inst₂] [inst₃] (f : StdSimplex R M) : M
  /-- A convex combination of a single point is that point. -/
  sConvexComb_single (x : M) : sConvexComb (.single x) = x
  /-- Associativity of convex combination (monadic join law).

  Use `sConvexComb_sConvexComb` instead. -/
  assoc (f : StdSimplex R (StdSimplex R M)) :
    sConvexComb (f.map sConvexComb) = sConvexComb f.join

open ConvexSpace StdSimplex

variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] [ConvexSpace R N] [ConvexSpace R P]

export ConvexSpace (sConvexComb sConvexComb_single)

attribute [simp] sConvexComb_single

@[deprecated (since := "2026-05-04")] alias ConvexSpace.convexCombination := sConvexComb

@[deprecated (since := "2026-05-04")]
alias ConvexSpace.convexCombination_single := sConvexComb_single

/-- Take a convex combination with the given weight distribution of an indexed family of points. -/
def iConvexComb (s : StdSimplex R I) (f : I → M) : M := sConvexComb (s.map f)

/-- Take a convex combination of two points. -/
def convexCombPair (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (x y : M) : M :=
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

end StdSimplex

lemma sConvexComb_sConvexComb (f : StdSimplex R (StdSimplex R M)) :
    f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvexComb :=
  (ConvexSpace.assoc f).symm

lemma sConvexComb_convexCombPair (s t : R) (hs ht hst) (w w' : StdSimplex R M) :
    (convexCombPair s t hs ht hst w w').sConvexComb =
      convexCombPair s t hs ht hst w.sConvexComb w'.sConvexComb := by
  simp [convexCombPair, sConvexComb_sConvexComb]

/-- The public constructor for `ConvexSpace`. -/
abbrev ConvexSpace.mk {M : Type*} (sConvexComb : StdSimplex R M → M)
    (single : ∀ x : M, sConvexComb (.single x) = x)
    (assoc : ∀ f : StdSimplex R (StdSimplex R M),
      sConvexComb (f.map sConvexComb) = sConvexComb f.sConvexComb) : ConvexSpace R M :=
  ⟨sConvexComb, single, assoc⟩

variable (R) in
/-- A map between convex spaces is affine if it preserves convex combinations. -/
@[fun_prop]
structure IsAffineMap (f : M → N) : Prop where
  map_sConvexComb (s : StdSimplex R M) : f s.sConvexComb = (s.map f).sConvexComb

@[fun_prop]
protected lemma IsAffineMap.id : IsAffineMap R (id : M → M) where
  map_sConvexComb s := by simp

@[fun_prop]
lemma IsAffineMap.comp {g : N → P} (hg : IsAffineMap R g) {f : M → N} (hf : IsAffineMap R f) :
    IsAffineMap R (g ∘ f) where
  map_sConvexComb s := by
    simp [StdSimplex.map_comp, hf.map_sConvexComb, hg.map_sConvexComb]

variable (R) in
@[fun_prop]
lemma StdSimplex.isAffineMap_map (f : I → J) : IsAffineMap R (StdSimplex.map (R := R) f) :=
  ⟨(map_sConvexComb · f)⟩

section iConvexComb

lemma sConvexComb_map (w : StdSimplex R I) (f : I → M) :
    sConvexComb (w.map f) = iConvexComb w f := rfl

@[simp] lemma iConvexComb_const (s : StdSimplex R I) (m : M) :
    s.iConvexComb (fun _ ↦ m) = m := by simp [iConvexComb]

@[simp] lemma iConvexComb_single (i : I) (f : I → M) :
    (single (R := R) i).iConvexComb f = f i := by simp [iConvexComb]

@[simp] lemma iConvexComb_id (s : StdSimplex R M) :
    s.iConvexComb id = s.sConvexComb := by simp [iConvexComb]

@[simp] lemma iConvexComb_id' (s : StdSimplex R M) :
    s.iConvexComb (fun x ↦ x) = s.sConvexComb := iConvexComb_id s

@[simp] lemma iConvexComb_map (s : StdSimplex R I) (f : I → J) (g : J → M) :
    (s.map f).iConvexComb g = s.iConvexComb (g ∘ f) := by
  simp only [iConvexComb, map_comp]

lemma iConvexComb_congr (s : StdSimplex R I) (f : I ≃ J) (g : I → M) :
    s.iConvexComb g = (s.map f).iConvexComb (g ∘ f.symm) := by
  simp [iConvexComb_map, Function.comp_def]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'` and `iConvexComb_assoc` for non-dependent versions. -/
lemma iConvexComb_assoc''
    {J : I → Type*} (s : StdSimplex R I) (f : Π i, StdSimplex R (J i)) (g : Π i, J i → M) :
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
    (g : I → J → M) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb (g i)) =
      (s.iConvexComb fun i ↦ (f i).map (⟨i, ·⟩)).iConvexComb g.uncurry := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Function.uncurry]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'`, `iConvexComb_assoc''` for more dependent versions. -/
lemma iConvexComb_assoc {J : Type*} (s : StdSimplex R I) (f : I → StdSimplex R J)
    (g : J → M) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb g) = (s.iConvexComb f).iConvexComb g := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  simp [map_sConvexComb, map_map]

variable {R M I J : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] in
lemma iConvexComb_comm (f : StdSimplex R I) (g : StdSimplex R J)
    (e : I → J → M) :
    f.iConvexComb (fun i ↦ g.iConvexComb (e i)) =
      g.iConvexComb fun j ↦ f.iConvexComb fun i ↦ e i j := by
  rw [iConvexComb_assoc', iConvexComb_assoc', iConvexComb_congr _ (.prodComm ..)]
  congr
  suffices (f.map fun x ↦ g.map (Prod.mk · x)).sConvexComb =
      (g.map (f.map ∘ Prod.mk)).sConvexComb by
    simpa [iConvexComb, map_sConvexComb, map_map, Function.comp_def]
  ext1
  simp [mapDomain, sum_sum_index, add_smul, smul_sum, mul_comm, sum_comm f.weights g.weights]

lemma IsAffineMap.map_iConvexComb {f : M → N} (hf : IsAffineMap R f)
    (s : StdSimplex R I) (g : I → M) : f (s.iConvexComb g) = s.iConvexComb (f ∘ g) := by
  simp [iConvexComb, hf.map_sConvexComb, map_comp]

lemma map_iConvexComb {f : J → K}
    (s : StdSimplex R I) (g : I → StdSimplex R J) :
    (s.iConvexComb g).map f = s.iConvexComb (map f ∘ g) :=
  (isAffineMap_map R f).map_iConvexComb s g

end iConvexComb

variable {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)
variable {s' t' : R} (hs' : 0 ≤ s') (ht' : 0 ≤ t') (h' : s' + t' = 1)
variable {s'' t'' : R} (hs'' : 0 ≤ s'') (ht'' : 0 ≤ t'') (h'' : s'' + t'' = 1)

lemma convexCombPair_def (p q : M) :
    convexCombPair s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexComb ![p, q] := by
  simp [StdSimplex.iConvexComb, convexCombPair]

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
@[simp]
theorem convexCombPair_zero {x y : M} :
    convexCombPair (0 : R) 1 (by simp) (by simp) (by simp) x y = y := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_zero := convexCombPair_zero

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
@[simp]
theorem convexCombPair_one {x y : M} :
    convexCombPair (1 : R) 0 (by simp) (by simp) (by simp) x y = x := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_one := convexCombPair_one

/-- A convex combination of a point with itself is that point. -/
@[simp]
theorem convexCombPair_same {x : M} :
    convexCombPair s t hs ht h x x = x := by
  unfold convexCombPair
  convert sConvexComb_single x
  simp only [StdSimplex.duple, StdSimplex.single, ← single_add, h]

@[deprecated (since := "2026-05-15")] alias convexComboPair_symm := convexCombPair_same

theorem convexCombPair_symm {x y : M} :
    convexCombPair s t hs ht h x y = convexCombPair t s ht hs ((add_comm _ _).trans h) y x := by
  unfold convexCombPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]

lemma IsAffineMap.map_convexCombPair {f : M → N} (hf : IsAffineMap R f)
    {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) :
    f (convexCombPair s t hs ht h x y) = convexCombPair s t hs ht h (f x) (f y) := by
  simp [hf.map_sConvexComb, convexCombPair]

/-- Flattening with the outer combination specialized to `convexCombPair`. -/
lemma convexCombPair_iConvexComb_iConvexComb {J₁ : Type u₁} {J₂ : Type u₂}
    (g₁ : StdSimplex R J₁) (g₂ : StdSimplex R J₂)
    (m₁ : J₁ → M) (m₂ : J₂ → M) :
    convexCombPair s t hs ht h (g₁.iConvexComb m₁) (g₂.iConvexComb m₂) =
      (convexCombPair s t hs ht h (g₁.map m₁) (g₂.map m₂)).sConvexComb := by
  have := iConvexComb_assoc'' (I := Fin 2) (.duple 0 1 hs ht h)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (M := M) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexComb, map_sConvexComb, map_map, Sigma.uncurry] at this
  simpa [convexCombPair, ← convexCombPair_def]

/-- Flattening with the inner combination specialized to `convexCombPair`. -/
lemma iConvexComb_convexCombPair
    (s t : I → R) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i) (h : ∀ i, s i + t i = 1)
    (f : StdSimplex R I) (m₁ m₂ : I → M) :
    f.iConvexComb (fun i ↦ convexCombPair (s i) (t i) (hs i) (ht i) (h i) (m₁ i) (m₂ i)) =
    (f.iConvexComb fun i ↦ duple (m₁ i) (m₂ i) (hs i) (ht i) (h i)).sConvexComb := by
  have := iConvexComb_assoc' (I := I) (J := Fin 2) (R := R) (M := M) f
    (fun i ↦ .duple 0 1 (hs i) (ht i) (h i)) (fun i ↦ ![m₁ i, m₂ i])
  simp [iConvexComb, map_sConvexComb, map_map] at this
  simp only [← convexCombPair.eq_def] at this
  simp only [← iConvexComb.eq_def] at this
  simpa [convexCombPair, ← convexCombPair_def]

lemma convexCombPair_iConvexComb_left (g : StdSimplex R J) (e : J → M) (m : M) :
    convexCombPair s t hs ht h (g.iConvexComb e) m =
      (convexCombPair s t hs ht h (g.map e) (single m)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g e (fun _ ↦ m)

lemma convexCombPair_iConvexComb_right (m : M) (g : StdSimplex R J) (e : J → M) :
    convexCombPair s t hs ht h m (g.iConvexComb e) =
      (convexCombPair s t hs ht h (.single m) (g.map e)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g (fun _ ↦ m) e

/-- Flattening nested binary convex combination into a single convex combination. -/
lemma convexCombPair_convexCombPair_left_eq_sConvexComb (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ =
      (convexCombPair s t hs ht h (duple m₁ m₂ hs' ht' h') (single m₃)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_left hs ht h (.duple m₁ m₂ hs' ht' h') id m₃

/-- Flattening nested binary convex combination into a single convex combination. -/
lemma convexCombPair_convexCombPair_right_eq_sConvexComb (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) =
      (convexCombPair s t hs ht h (.single m₁) (duple m₂ m₃ hs' ht' h')).sConvexComb := by
  simpa using convexCombPair_iConvexComb_right hs ht h m₁ (.duple m₂ m₃ hs' ht' h') id

lemma convexCombPair_convexCombPair_assoc_left (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : M) :
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

lemma convexCombPair_convexCombPair_assoc_right (H : s * t'' = t * s' * s'') (m₁ m₂ m₃ : M) :
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

variable {R M I : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)

lemma iConvexComb_convexCombPair_comm (f : StdSimplex R I) (e₁ e₂ : I → M) :
    f.iConvexComb (fun x ↦ convexCombPair s t hs ht h (e₁ x) (e₂ x)) =
      convexCombPair s t hs ht h (f.iConvexComb e₁) (f.iConvexComb e₂) := by
  simp only [convexCombPair_def]
  convert (iConvexComb_comm (.duple 0 1 hs ht h) f ![e₁, e₂]).symm with i j j
  · fin_cases j <;> simp
  · fin_cases j <;> simp

lemma iConvexComb_convexCombPair_comm_left (f : StdSimplex R I) (m : M) (e : I → M) :
    f.iConvexComb (fun x ↦ convexCombPair s t hs ht h (e x) m) =
    convexCombPair s t hs ht h (f.iConvexComb e) m := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f e (fun _ ↦ m)

lemma iConvexComb_convexCombPair_comm_right (f : StdSimplex R I) (m : M) (e : I → M) :
    f.iConvexComb (convexCombPair s t hs ht h m <| e ·) =
    convexCombPair s t hs ht h m (f.iConvexComb e) := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f (fun _ ↦ m) e

lemma isAffineMap_convexCombPair (m : M) :
    IsAffineMap R (convexCombPair s t hs ht h m) :=
  ⟨fun f ↦ by simpa using (iConvexComb_convexCombPair_comm_right hs ht h f m id).symm⟩

end CommSemiring

end Convexity
