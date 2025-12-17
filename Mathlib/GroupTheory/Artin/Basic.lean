/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Artin groups

This file defines Artin groups associated to Coxeter matrices.

## Main definitions

* `CoxeterMatrix.ArtinGroup`: The Artin group associated to a Coxeter matrix `M`.
* `CoxeterMatrix.artinGenerator`: The generators of the Artin group.
* `CoxeterMatrix.artinLift`: The universal property of Artin groups.

## Overview

An Artin group (also called Artin-Tits group) associated to a Coxeter matrix `M` is the group
with presentation:
* Generators: `{s_i}_{i ∈ B}`
* Relations: `s_i s_j s_i ... = s_j s_i s_j ...` (alternating products of length `M i j`)

This differs from Coxeter groups which additionally have the relation `s_i² = 1`.

The braid group `B_n` is the Artin group of type `A_{n-1}`.

## References

* [Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*]
-/

@[expose] public section

noncomputable section

open FreeGroup List

variable {B : Type*}

namespace CoxeterMatrix

variable (M : CoxeterMatrix B)

/-! ### Alternating words -/

/-- The word of length `m` that alternates between `i` and `j`, ending with `i`.
For example, `alternatingWord i j 3 = [i, j, i]` and `alternatingWord i j 4 = [j, i, j, i]`. -/
def alternatingWord (i j : B) : ℕ → List B
  | 0 => []
  | m + 1 => (alternatingWord j i m).concat i

@[simp]
theorem alternatingWord_zero (i j : B) : alternatingWord i j 0 = [] := rfl

@[simp]
theorem alternatingWord_succ (i j : B) (m : ℕ) :
    alternatingWord i j (m + 1) = (alternatingWord j i m).concat i := rfl

theorem alternatingWord_one (i j : B) : alternatingWord i j 1 = [i] := rfl

theorem alternatingWord_two (i j : B) : alternatingWord i j 2 = [j, i] := rfl

theorem alternatingWord_three (i j : B) : alternatingWord i j 3 = [i, j, i] := rfl

@[simp]
theorem length_alternatingWord (i j : B) (m : ℕ) : (alternatingWord i j m).length = m := by
  induction m generalizing i j with
  | zero => rfl
  | succ m ih => simp [alternatingWord_succ, ih]

/-! ### Free group product of a word -/

/-- Convert a list of indices to an element of the free group by taking the product. -/
def freeGroupProd (l : List B) : FreeGroup B := (l.map FreeGroup.of).prod

@[simp]
theorem freeGroupProd_nil : freeGroupProd ([] : List B) = 1 := by simp [freeGroupProd]

@[simp]
theorem freeGroupProd_singleton (i : B) : freeGroupProd [i] = FreeGroup.of i := by
  simp [freeGroupProd]

theorem freeGroupProd_cons (i : B) (l : List B) :
    freeGroupProd (i :: l) = FreeGroup.of i * freeGroupProd l := by simp [freeGroupProd]

theorem freeGroupProd_concat (l : List B) (i : B) :
    freeGroupProd (l.concat i) = freeGroupProd l * FreeGroup.of i := by
  simp [freeGroupProd]

theorem freeGroupProd_append (l₁ l₂ : List B) :
    freeGroupProd (l₁ ++ l₂) = freeGroupProd l₁ * freeGroupProd l₂ := by
  simp [freeGroupProd]

/-! ### Artin relations -/

/-- The Artin relation for indices `i` and `j`: the two alternating words of length `M i j`
are equal. This is encoded as
`freeGroupProd (alternatingWord i j m) * freeGroupProd (alternatingWord j i m)⁻¹ = 1`. -/
def artinRelation (i j : B) : FreeGroup B :=
  freeGroupProd (alternatingWord i j (M i j)) * (freeGroupProd (alternatingWord j i (M i j)))⁻¹

/-- The set of all Artin relations associated to the Coxeter matrix `M`. -/
def artinRelationsSet : Set (FreeGroup B) :=
  Set.range fun p : B × B => M.artinRelation p.1 p.2

theorem artinRelation_mem (i j : B) : M.artinRelation i j ∈ M.artinRelationsSet :=
  ⟨(i, j), rfl⟩

theorem artinRelation_symmetric_mem (i j : B) :
    (M.artinRelation j i)⁻¹ ∈ Subgroup.normalClosure M.artinRelationsSet := by
  have h : M.artinRelation j i ∈ M.artinRelationsSet := artinRelation_mem M j i
  exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure h)

/-! ### The Artin group -/

/-- The Artin group associated to a Coxeter matrix `M`. This is the group with presentation:
* Generators: `{s_i}_{i ∈ B}`
* Relations: alternating products of length `M i j` are equal -/
protected def ArtinGroup : Type _ := PresentedGroup M.artinRelationsSet

instance : Group M.ArtinGroup := QuotientGroup.Quotient.group _

/-- An Artin group with no generators is trivial. -/
instance instUniqueArtinGroupOfIsEmpty [IsEmpty B] : Unique M.ArtinGroup :=
  PresentedGroup.instUniqueOfIsEmpty _

/-- The `i`-th generator of the Artin group. -/
def artinGenerator (i : B) : M.ArtinGroup := PresentedGroup.of i

-- TODO: Prove injectivity of generators (requires more theory about Artin groups)

/-! ### Universal property -/

/-- Compute the alternating product of `f` applied to `i` and `j`, of length `m`. -/
def alternatingProd {G : Type*} [Monoid G] (f : B → G) (i j : B) : ℕ → G
  | 0 => 1
  | m + 1 => alternatingProd f j i m * f i

@[simp]
theorem alternatingProd_zero {G : Type*} [Monoid G] (f : B → G) (i j : B) :
    alternatingProd f i j 0 = 1 := rfl

theorem alternatingProd_succ {G : Type*} [Monoid G] (f : B → G) (i j : B) (m : ℕ) :
    alternatingProd f i j (m + 1) = alternatingProd f j i m * f i := rfl

theorem freeGroupProd_alternatingWord_eq_lift_alternatingProd {G : Type*} [Group G] (f : B → G)
    (i j : B) (m : ℕ) :
    FreeGroup.lift f (freeGroupProd (alternatingWord i j m)) = alternatingProd f i j m := by
  induction m generalizing i j with
  | zero => simp [freeGroupProd, alternatingProd]
  | succ m ih =>
    rw [alternatingWord_succ, freeGroupProd_concat]
    rw [MonoidHom.map_mul, ih, FreeGroup.lift_apply_of, alternatingProd_succ]

/-- A function `f : B → G` is liftable to the Artin group if it satisfies the braid relations:
for all `i, j`, the alternating products of length `M i j` are equal. -/
def IsArtinLiftable {G : Type*} [Monoid G] (f : B → G) : Prop :=
  ∀ i j, alternatingProd f i j (M i j) = alternatingProd f j i (M i j)

theorem isArtinLiftable_iff_artinRelation_eq_one {G : Type*} [Group G] (f : B → G) :
    M.IsArtinLiftable f ↔ ∀ i j, FreeGroup.lift f (M.artinRelation i j) = 1 := by
  constructor
  · intro h i j
    unfold artinRelation
    rw [MonoidHom.map_mul, MonoidHom.map_inv,
      freeGroupProd_alternatingWord_eq_lift_alternatingProd,
      freeGroupProd_alternatingWord_eq_lift_alternatingProd, h, mul_inv_cancel]
  · intro h i j
    have := h i j
    unfold artinRelation at this
    rw [MonoidHom.map_mul, MonoidHom.map_inv,
      freeGroupProd_alternatingWord_eq_lift_alternatingProd,
      freeGroupProd_alternatingWord_eq_lift_alternatingProd, mul_inv_eq_one] at this
    exact this

/-- The universal property of Artin groups: lift a function satisfying braid relations
to a group homomorphism. -/
def artinLift {G : Type*} [Group G] (f : B → G) (hf : M.IsArtinLiftable f) : M.ArtinGroup →* G :=
  PresentedGroup.toGroup (by
    intro r hr
    obtain ⟨⟨i, j⟩, rfl⟩ := hr
    exact (isArtinLiftable_iff_artinRelation_eq_one M f).mp hf i j)

@[simp]
theorem artinLift_artinGenerator {G : Type*} [Group G] (f : B → G) (hf : M.IsArtinLiftable f)
    (i : B) : M.artinLift f hf (M.artinGenerator i) = f i :=
  PresentedGroup.toGroup.of _

theorem artinLift_unique {G : Type*} [Group G] (f : B → G) (hf : M.IsArtinLiftable f)
    (φ : M.ArtinGroup →* G) (hφ : ∀ i, φ (M.artinGenerator i) = f i) :
    φ = M.artinLift f hf :=
  MonoidHom.ext fun _ => PresentedGroup.toGroup.unique _ φ hφ

/-- Two homomorphisms from an Artin group are equal if they agree on generators. -/
theorem artinLift_ext {G : Type*} [Group G] (φ ψ : M.ArtinGroup →* G)
    (h : ∀ i, φ (M.artinGenerator i) = ψ (M.artinGenerator i)) : φ = ψ :=
  PresentedGroup.ext h

/-! ### Generators generate -/

theorem closure_range_artinGenerator : Subgroup.closure (Set.range M.artinGenerator) = ⊤ :=
  PresentedGroup.closure_range_of _

theorem artinGenerator_generates (S : Subgroup M.ArtinGroup)
    (h : ∀ i, M.artinGenerator i ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact PresentedGroup.generated_by _ S h x

/-! ### Homomorphism to Coxeter group -/

/-- The alternating product of simple reflections equals the word product of the
alternating word. -/
theorem alternatingProd_simple_eq_wordProd (i j : B) (m : ℕ) :
    alternatingProd M.simple i j m = M.toCoxeterSystem.wordProd (alternatingWord i j m) := by
  induction m generalizing i j with
  | zero => simp [alternatingProd, CoxeterSystem.wordProd]
  | succ m ih =>
    rw [alternatingProd_succ, ih]
    simp only [alternatingWord_succ, CoxeterSystem.wordProd, List.map_concat, List.prod_concat]
    rfl

/-- The alternating word defined in `CoxeterMatrix` equals the one in `CoxeterSystem`
with swapped arguments. -/
theorem alternatingWord_eq_coxeterSystem_alternatingWord (i j : B) (m : ℕ) :
    alternatingWord i j m = CoxeterSystem.alternatingWord j i m := by
  induction m generalizing i j with
  | zero => rfl
  | succ m ih =>
    rw [alternatingWord_succ, CoxeterSystem.alternatingWord_succ, ih]

/-- The simple reflections in the Coxeter group satisfy the Artin relations. -/
theorem simple_isArtinLiftable : M.IsArtinLiftable M.simple := fun i j => by
  rw [alternatingProd_simple_eq_wordProd, alternatingProd_simple_eq_wordProd,
      alternatingWord_eq_coxeterSystem_alternatingWord,
      alternatingWord_eq_coxeterSystem_alternatingWord]
  convert M.toCoxeterSystem.wordProd_braidWord_eq j i using 2
  all_goals (unfold CoxeterSystem.braidWord; congr 1; exact (M.symmetric j i).symm)

/-- The canonical homomorphism from the Artin group to the Coxeter group. -/
def artinToCoxeter : M.ArtinGroup →* M.Group :=
  M.artinLift M.simple M.simple_isArtinLiftable

@[simp]
theorem artinToCoxeter_artinGenerator (i : B) :
    M.artinToCoxeter (M.artinGenerator i) = M.simple i :=
  M.artinLift_artinGenerator M.simple M.simple_isArtinLiftable i

/-- The homomorphism from the Artin group to the Coxeter group is surjective. -/
theorem artinToCoxeter_surjective : Function.Surjective M.artinToCoxeter := by
  rw [← MonoidHom.range_eq_top]
  rw [eq_top_iff, ← M.toCoxeterSystem.subgroup_closure_range_simple, Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨M.artinGenerator i, M.artinToCoxeter_artinGenerator i⟩

end CoxeterMatrix
