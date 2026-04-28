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
  `Convexity.sConvexCombo : StdSimplex R M → M` satisfying monadic laws.
* `Convexity.iConvexCombo`: Indexed convex combination operator.
* `Convexity.convexComboPair`: Binary convex combinations of two points.

## Design

The design follows a monadic structure where `StdSimplex R` forms a monad and `convexCombination`
is a monadic algebra. This eliminates the need for explicit extensionality axioms and resolves
universe issues with indexed families.

-/

@[expose] public noncomputable section

universe u v w u₁ u₂

open Finsupp

namespace Convexity


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

namespace StdSimplex

variable {R : Type u} [PartialOrder R] [Semiring R] {M N P : Type*}

@[simp] lemma weights_nonneg {f : StdSimplex R M} (i : M) : 0 ≤ f.weights i := f.nonneg i

lemma nonempty [Nontrivial R] (f : StdSimplex R M) : Nonempty M := by
  by_contra!
  simpa [Subsingleton.elim f.weights 0, -total] using f.total

@[ext]
theorem ext {f g : StdSimplex R M} (h : f.weights = g.weights) : f = g := by
  cases f; cases g; simp_all

variable [IsStrictOrderedRing R]

/-- The point mass distribution concentrated at `x`. -/
@[simps weights]
def single (x : M) : StdSimplex R M where
  weights := Finsupp.single x 1
  nonneg := by simp
  total := by simp

theorem mk_single (x : M) {nonneg total} :
    (StdSimplex.mk (Finsupp.single x (1 : R)) nonneg total) = single x := rfl

/-- A probability distribution with weight `s` on `x` and weight `t` on `y`. -/
@[simps weights]
def duple (x y : M) {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) : StdSimplex R M where
  weights := Finsupp.single x s + Finsupp.single y t
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
  ext; simp [Finsupp.mapDomain_comp]

lemma map_map (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    (f.map g₁).map g₂ = f.map (fun x ↦ g₂ (g₁ x)) :=
  (map_comp ..).symm

/--
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.

Use `ConvexSpace.sConvexCombo` instead.
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
  /- FIXME: Lean makes `inst₁`, `inst₂`, `inst₃` implicit by default, which renders `sConvexCombo`
  unusable. Why is this so? Shouldn't typeclass arguments to a `structure` also be typeclass
  arguments to its fields? -/
  sConvexCombo [inst₁] [inst₂] [inst₃] (f : StdSimplex R M) : M
  /-- Associativity of convex combination (monadic join law). -/
  assoc (f : StdSimplex R (StdSimplex R M)) :
    sConvexCombo (f.map sConvexCombo) = sConvexCombo f.join
  /-- A convex combination of a single point is that point. -/
  sConvexCombo_single (x : M) : sConvexCombo (.single x) = x

open ConvexSpace StdSimplex

variable {R M N P I J K : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] [ConvexSpace R N] [ConvexSpace R P]

section sConvexCombo

export ConvexSpace (sConvexCombo sConvexCombo_single)

attribute [simp] sConvexCombo_single

namespace StdSimplex

export ConvexSpace (sConvexCombo)

instance : ConvexSpace R (StdSimplex R I) where
  sConvexCombo σ := σ.join
  assoc f := by exact (join_join f).symm
  sConvexCombo_single := by exact join_single

@[simp] lemma weights_sConvexCombo (f : StdSimplex R (StdSimplex R I)) :
    f.sConvexCombo.weights = f.weights.sum (fun d r => r • d.weights) :=
  StdSimplex.join_weights _

lemma map_sConvexCombo (s : StdSimplex R (StdSimplex R I)) (f : I → J) :
    s.sConvexCombo.map f = (s.map (map f)).sConvexCombo :=
  StdSimplex.map_join s f

end StdSimplex

lemma sConvexCombo_sConvexCombo (f : StdSimplex R (StdSimplex R M)) :
    f.sConvexCombo.sConvexCombo = (f.map sConvexCombo).sConvexCombo :=
  (ConvexSpace.assoc f).symm

/-- The public constructor for `ConvexSpace`. -/
abbrev ConvexSpace.mk {M : Type*} (sConvexCombo : StdSimplex R M → M)
    (assoc : ∀ f : StdSimplex R (StdSimplex R M),
      sConvexCombo (f.map sConvexCombo) = sConvexCombo f.sConvexCombo)
    (single : ∀ x : M, sConvexCombo (.single x) = x) : ConvexSpace R M :=
  ⟨sConvexCombo, assoc, single⟩

end sConvexCombo

variable (R) in
/-- A map between convex spaces is affine if it preserves convex combinations. -/
@[fun_prop]
structure IsAffineMap (f : M → N) : Prop where
  map_sConvexCombo (s : StdSimplex R M) : f s.sConvexCombo = (s.map f).sConvexCombo

@[fun_prop]
protected lemma IsAffineMap.id : IsAffineMap R (id : M → M) where
  map_sConvexCombo s := by simp

@[fun_prop]
lemma IsAffineMap.comp {g : N → P} (hg : IsAffineMap R g) {f : M → N} (hf : IsAffineMap R f) :
    IsAffineMap R (g ∘ f) where
  map_sConvexCombo s := by
    simp [StdSimplex.map_comp, hf.map_sConvexCombo, hg.map_sConvexCombo]

variable (R) in
@[fun_prop]
lemma StdSimplex.isAffineMap_map (f : I → J) : IsAffineMap R (StdSimplex.map (R := R) f) :=
  ⟨(map_sConvexCombo · f)⟩

section iConvexCombo

/-- Take a convex combination with the given weight distribution of an indexed family of points. -/
def iConvexCombo (s : StdSimplex R I) (f : I → M) : M := (s.map f).sConvexCombo

namespace StdSimplex

-- We export `iConvexCombo` to allow dot notation on the `StdSimplex` argument.
export Convexity (iConvexCombo)

end StdSimplex

@[simp] lemma iConvexCombo_const (s : StdSimplex R I) (m : M) :
    s.iConvexCombo (fun _ ↦ m) = m := by simp [iConvexCombo]

@[simp] lemma iConvexCombo_single (i : I) (f : I → M) :
    (single (R := R) i).iConvexCombo f = f i := by simp [iConvexCombo]

@[simp] lemma iConvexCombo_id (s : StdSimplex R M) :
    s.iConvexCombo id = s.sConvexCombo := by simp [iConvexCombo]

@[simp] lemma iConvexCombo_id' (s : StdSimplex R M) :
    s.iConvexCombo (fun x ↦ x) = s.sConvexCombo := iConvexCombo_id s

lemma iConvexCombo_map (s : StdSimplex R I) (f : I → J) (g : J → M) :
  (s.map f).iConvexCombo g = s.iConvexCombo (g ∘ f) := by
  simp only [iConvexCombo, map_comp]

lemma iConvexCombo_congr (s : StdSimplex R I) (f : I ≃ J) (g : I → M) :
  s.iConvexCombo g = (s.map f).iConvexCombo (g ∘ f.symm) := by
  simp [iConvexCombo_map, Function.comp_def]

/-- Flattening nested `iConvexCombo`s. -/
lemma iConvexCombo_iConvexCombo
    {J : I → Type*} (s : StdSimplex R I) (f : Π i, StdSimplex R (J i)) (g : Π i, J i → M) :
    s.iConvexCombo (fun i ↦ (f i).iConvexCombo (g i)) =
      (s.iConvexCombo fun i ↦ (f i).map (⟨i, ·⟩)).iConvexCombo (Sigma.uncurry g) := by
  simp only [iConvexCombo]
  rw [← map_map, ← sConvexCombo_sConvexCombo]
  congr 1
  simp [map_sConvexCombo, map_map, Sigma.uncurry]

variable {R M I J : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] in
lemma iConvexCombo_comm (f : StdSimplex R I) (g : StdSimplex R J)
    (e : I → J → M) :
    f.iConvexCombo (fun x ↦ g.iConvexCombo (e x)) =
      g.iConvexCombo fun x ↦ f.iConvexCombo fun y ↦ e y x := by
  rw [iConvexCombo_iConvexCombo, iConvexCombo_iConvexCombo, iConvexCombo_congr _
    (((Equiv.sigmaEquivProd I J).trans (Equiv.prodComm _ _)).trans (Equiv.sigmaEquivProd _ _).symm)]
  congr
  suffices (f.map fun x ↦ g.map (Sigma.mk · x)).sConvexCombo =
      (g.map (f.map ∘ Sigma.mk)).sConvexCombo by
    simpa [iConvexCombo, map_sConvexCombo, map_map, Function.comp_def]
  ext1
  simp [mapDomain, sum_sum_index, add_smul, smul_sum, mul_comm, sum_comm f.weights g.weights]

lemma IsAffineMap.map_iConvexCombo {f : M → N} (hf : IsAffineMap R f)
    (s : StdSimplex R I) (g : I → M) : f (s.iConvexCombo g) = s.iConvexCombo (f ∘ g) := by
  simp [iConvexCombo, hf.map_sConvexCombo, map_comp]

lemma map_iConvexCombo {f : J → K}
    (s : StdSimplex R I) (g : I → StdSimplex R J) :
    (s.iConvexCombo g).map f = s.iConvexCombo (map f ∘ g) :=
  (isAffineMap_map R f).map_iConvexCombo s g

end iConvexCombo

variable {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)
variable {s' t' : R} (hs' : 0 ≤ s') (ht' : 0 ≤ t') (h' : s' + t' = 1)
variable {s'' t'' : R} (hs'' : 0 ≤ s'') (ht'' : 0 ≤ t'') (h'' : s'' + t'' = 1)

/-- Take a convex combination of two points. -/
def convexComboPair (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) : M :=
  sConvexCombo (.duple x y hs ht h)

lemma convexComboPair_def (p q : M) :
    convexComboPair s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexCombo ![p, q] := by
  simp [StdSimplex.iConvexCombo, convexComboPair]

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
@[simp]
theorem convexComboPair_zero {x y : M} :
    convexComboPair (0 : R) 1 (by simp) (by simp) (by simp) x y = y := by
  simp [convexComboPair, StdSimplex.duple, StdSimplex.mk_single]

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
@[simp]
theorem convexComboPair_one {x y : M} :
    convexComboPair (1 : R) 0 (by simp) (by simp) (by simp) x y = x := by
  simp [convexComboPair, StdSimplex.duple, StdSimplex.mk_single]

/-- A convex combination of a point with itself is that point. -/
@[simp]
theorem convexComboPair_same {x : M} :
    convexComboPair s t hs ht h x x = x := by
  unfold convexComboPair
  convert ConvexSpace.sConvexCombo_single x
  simp only [StdSimplex.duple, StdSimplex.single, ← Finsupp.single_add, h]

theorem convexComboPair_symm {x y : M} :
    convexComboPair s t hs ht h x y = convexComboPair t s ht hs ((add_comm _ _).trans h) y x := by
  unfold convexComboPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]

lemma IsAffineMap.map_convexComboPair {f : M → N} (hf : IsAffineMap R f)
    {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) :
    f (convexComboPair s t hs ht h x y) = convexComboPair s t hs ht h (f x) (f y) := by
  simp [hf.map_sConvexCombo, convexComboPair]

/-- Flattening with the outer combination specialized to `convexComboPair`. -/
lemma convexComboPair_iConvexCombo_iConvexCombo {J₁ : Type u₁} {J₂ : Type u₂}
    (g₁ : StdSimplex R J₁) (g₂ : StdSimplex R J₂)
    (m₁ : J₁ → M) (m₂ : J₂ → M) :
    convexComboPair s t hs ht h (g₁.iConvexCombo m₁) (g₂.iConvexCombo m₂) =
      (convexComboPair s t hs ht h (g₁.map m₁) (g₂.map m₂)).sConvexCombo := by
  have := iConvexCombo_iConvexCombo (I := Fin 2) (.duple 0 1 hs ht h)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (M := M) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexCombo, map_sConvexCombo, map_map, Sigma.uncurry] at this
  simpa [convexComboPair, ← convexComboPair_def]

/-- Flattening with the inner combination specialized to `convexComboPair`. -/
lemma iConvexCombo_convexComboPair
    (s t : I → R) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i) (h : ∀ i, s i + t i = 1)
    (f : StdSimplex R I) (m₁ m₂ : I → M) :
    f.iConvexCombo (fun i ↦ convexComboPair (s i) (t i) (hs i) (ht i) (h i) (m₁ i) (m₂ i)) =
    (f.iConvexCombo fun i ↦ duple (m₁ i) (m₂ i) (hs i) (ht i) (h i)).sConvexCombo := by
  have := iConvexCombo_iConvexCombo (I := I) (J := fun _ ↦ Fin 2) (R := R) (M := M) f
    (fun i ↦ .duple 0 1 (hs i) (ht i) (h i)) (fun i ↦ ![m₁ i, m₂ i])
  simp [iConvexCombo, map_sConvexCombo, map_map, Sigma.uncurry] at this
  simp only [← convexComboPair.eq_def] at this
  simp only [← iConvexCombo.eq_def] at this
  simpa [convexComboPair, ← convexComboPair_def]

lemma convexComboPair_iConvexCombo_left (g : StdSimplex R J) (e : J → M) (m : M) :
    convexComboPair s t hs ht h (g.iConvexCombo e) m =
      (convexComboPair s t hs ht h (g.map e) (single m)).sConvexCombo := by
  simpa using convexComboPair_iConvexCombo_iConvexCombo hs ht h g g e (fun _ ↦ m)

lemma convexComboPair_iConvexCombo_right (m : M) (g : StdSimplex R J) (e : J → M) :
    convexComboPair s t hs ht h m (g.iConvexCombo e) =
      (convexComboPair s t hs ht h (.single m) (g.map e)).sConvexCombo := by
  simpa using convexComboPair_iConvexCombo_iConvexCombo hs ht h g g (fun _ ↦ m) e

/-- Flattening nested binary convex combination into a single convex combination. -/
lemma convexComboPair_convexComboPair_left_eq_sConvexCombo (m₁ m₂ m₃ : M) :
    convexComboPair s t hs ht h (convexComboPair s' t' hs' ht' h' m₁ m₂) m₃ =
      (convexComboPair s t hs ht h (duple m₁ m₂ hs' ht' h') (single m₃)).sConvexCombo := by
  simpa using convexComboPair_iConvexCombo_left hs ht h (.duple m₁ m₂ hs' ht' h') id m₃

/-- Flattening nested binary convex combination into a single convex combination. -/
lemma convexComboPair_convexComboPair_right_eq_sConvexCombo (m₁ m₂ m₃ : M) :
    convexComboPair s t hs ht h m₁ (convexComboPair s' t' hs' ht' h' m₂ m₃) =
      (convexComboPair s t hs ht h (.single m₁) (duple m₂ m₃ hs' ht' h')).sConvexCombo := by
  simpa using convexComboPair_iConvexCombo_right hs ht h m₁ (.duple m₂ m₃ hs' ht' h') id

lemma convexComboPair_convexComboPair_assoc_left (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : M) :
    convexComboPair s t hs ht h (convexComboPair s' t' hs' ht' h' m₁ m₂) m₃ =
      convexComboPair (s * s') (s * t' + t) (by positivity) (by positivity)
        (by rw [← add_assoc, ← mul_add, h', mul_one, h]) m₁
        (convexComboPair s'' t'' hs'' ht'' h'' m₂ m₃) := by
  classical
  rw [convexComboPair_convexComboPair_left_eq_sConvexCombo,
    convexComboPair_convexComboPair_right_eq_sConvexCombo]
  congr 1
  ext1
  have : s * (t' * t'') + t * t'' = t := by rw [← mul_assoc, ← H, ← mul_add, h'', mul_one]
  simp [convexComboPair, Finsupp.sum_add_index, add_smul, ← Finsupp.single_add,
    H, mul_assoc, ← mul_add, h'', add_assoc, this]

lemma convexComboPair_convexComboPair_assoc_right (H : s * t'' = t * s' * s'') (m₁ m₂ m₃ : M) :
    convexComboPair s t hs ht h m₁ (convexComboPair s' t' hs' ht' h' m₂ m₃) =
      convexComboPair (s + t * s') (t * t') (by positivity) (by positivity)
        (by rw [add_assoc, ← mul_add, h', mul_one, h])
        (convexComboPair s'' t'' hs'' ht'' h'' m₁ m₂) m₃ := by
  simp only [add_comm s]
  rw [convexComboPair_symm, convexComboPair_symm (x := m₂),
    convexComboPair_convexComboPair_assoc_left (hs'' := ht'') (ht'' := hs'')
      (h'' := (add_comm _ _).trans h'') (H := H),
    convexComboPair_symm, convexComboPair_symm (x := m₂)]

section CommSemiring

variable {R M I : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)

lemma iConvexCombo_convexComboPair_comm (f : StdSimplex R I) (e₁ e₂ : I → M) :
    f.iConvexCombo (fun x ↦ convexComboPair s t hs ht h (e₁ x) (e₂ x)) =
      convexComboPair s t hs ht h (f.iConvexCombo e₁) (f.iConvexCombo e₂) := by
  simp only [convexComboPair_def]
  convert (iConvexCombo_comm (.duple 0 1 hs ht h) f ![e₁, e₂]).symm with i j j
  · fin_cases j <;> simp
  · fin_cases j <;> simp

lemma iConvexCombo_convexComboPair_comm_left (f : StdSimplex R I) (m : M) (e : I → M) :
    f.iConvexCombo (fun x ↦ convexComboPair s t hs ht h (e x) m) =
    convexComboPair s t hs ht h (f.iConvexCombo e) m := by
  simpa using iConvexCombo_convexComboPair_comm hs ht h f e (fun _ ↦ m)

lemma iConvexCombo_convexComboPair_comm_right (f : StdSimplex R I) (m : M) (e : I → M) :
    f.iConvexCombo (convexComboPair s t hs ht h m <| e ·) =
    convexComboPair s t hs ht h m (f.iConvexCombo e) := by
  simpa using iConvexCombo_convexComboPair_comm hs ht h f (fun _ ↦ m) e

lemma isAffineMap_convexComboPair (m : M) :
    IsAffineMap R (convexComboPair s t hs ht h m) :=
  ⟨fun f ↦ by simpa using (iConvexCombo_convexComboPair_comm_right hs ht h f m id).symm⟩

end CommSemiring

end Convexity
