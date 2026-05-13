/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.GroupTheory.Artin.Basic
public import Mathlib.GroupTheory.Coxeter.Perm
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Braid groups

This file defines the braid groups as Artin groups of type A.

## Main definitions

* `BraidGroup`: The braid group $B_n$ on $n$ strands.
* `BraidGroup.σ`: The standard Artin generators $σ_i$ of the braid group.
* `BraidGroup.toPermHom`: The canonical surjection from $B_n$ to $S_n$.

## Overview

The braid group $B_n$ is the group with presentation:
* Generators: $σ_1, \ldots, σ_{n-1}$
* Relations:
  - $σ_i σ_j = σ_j σ_i$ for $|i - j| ≥ 2$ (far commutativity)
  - $σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}$ (braid relation)

This is the Artin group associated to the Coxeter matrix of type $A_{n-1}$.

There is a canonical surjection from $B_n$ to the symmetric group $S_n$ sending $σ_i$ to
the adjacent transposition $(i, i+1)$.

## Next steps

There are many things we should do from here, e.g.
* Prove injectivity of generators.
* Prove that the braid group is the fundamental group of the configuration space of n points in the
  plane.
* Construct the injection of the braid group into automorphisms of the free group.
* Identify `BraidGroup 3` with PSL(2, ℤ).

## References

* [Artin, *Theorie der Zöpfe*](artin1925)
-/

@[expose] public section

noncomputable section

open Equiv Fin

/-! ### The braid group -/

/-- The braid group `B_n` on `n` strands. This is the Artin group of type $A_{n-1}$. -/
def BraidGroup : ℕ → Type
| 0 => Unit
| n + 1 => (CoxeterMatrix.A n).ArtinGroup

namespace BraidGroup

variable {n : ℕ}

instance : Group (BraidGroup n) :=
  match n with
  | 0 => inferInstanceAs (Group Unit)
  | n + 1 => inferInstanceAs (Group (CoxeterMatrix.A n).ArtinGroup)

/-- The $i$-th standard Artin generator $σ_i$ of the braid group $B_n$.
This corresponds to crossing strand $i$ over strand $i+1$. -/
def σ (i : Fin n) : BraidGroup (n + 1) :=
  (CoxeterMatrix.A n).artinGenerator i

end BraidGroup

/-! ### The surjection to the symmetric group -/

namespace BraidGroup

/-- The canonical surjection from the braid group $B_{n+1}$ to the symmetric group $S_{n+1}$,
sending $σ_i$ to the adjacent transposition $(i, i+1)$.

This is defined as the composition of `artinToCoxeter` and `typeAToPermHom`. -/
def toPermHom (n : ℕ) : BraidGroup n →* Perm (Fin n) :=
  match n with
  | 0 => MulAction.toPermHom Unit (Fin 0)
  | n + 1 => (CoxeterMatrix.typeAToPermHom n).comp (CoxeterMatrix.A n).artinToCoxeter

@[simp]
theorem toPermHom_σ (n : ℕ) (i : Fin n) :
    toPermHom (n + 1) (σ i) = CoxeterMatrix.swapFun n i := by
  -- This proof is strangely fragile
  -- e.g. changing the `rw` to `simp only` results in a timeout,
  -- and while `simp only [CoxeterMatrix.artinToCoxeter_artinGenerator]`
  -- should work before the `exact`, it doesn't, nor does `rw`, while `erw` times out.
  simp only [toPermHom, σ]
  rw [MonoidHom.coe_comp, Function.comp_apply]
  exact CoxeterMatrix.typeAToPermHom_simple _ _

/-- The surjection from $B_{n+1}$ to $S_{n+1}$ is surjective. -/
theorem toPermHom_surjective (n : ℕ) : Function.Surjective (toPermHom n) :=
  match n with
  | 0 => Function.surjective_to_subsingleton ⇑(toPermHom 0)
  | n + 1 =>
    (CoxeterMatrix.typeAToPermHom_surjective n).comp (CoxeterMatrix.A n).artinToCoxeter_surjective

/-! ### Small braid groups -/

/-- The braid group $B_0$ is trivial (no generators). -/
instance : Unique (BraidGroup 0) :=
  inferInstanceAs (Unique Unit)

/-- The braid group $B_1$ is trivial (no generators). -/
instance : Unique (BraidGroup 1) :=
  inferInstanceAs (Unique (CoxeterMatrix.A 0).ArtinGroup)

/-- The Artin relations for `A 1` are all trivial.
When $i = j$, the relation is `of i * (of i)⁻¹ = 1`. -/
theorem artinRelationsSet_A_one_eq_one :
    (CoxeterMatrix.A 1).artinRelationsSet = {1} := by
  ext r
  simp only [CoxeterMatrix.artinRelationsSet, Set.mem_range, Prod.exists, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, j, rfl⟩
    -- i, j : Fin 1, so i = j = 0
    fin_cases i; fin_cases j
    -- artinRelation 0 0 with M 0 0 = 1
    simp only [CoxeterMatrix.artinRelation, CoxeterMatrix.diagonal,
      CoxeterSystem.alternatingWord, mul_inv_cancel]
  · intro hr
    use 0, 0
    simp only [CoxeterMatrix.artinRelation, CoxeterMatrix.diagonal,
      CoxeterSystem.alternatingWord, mul_inv_cancel, hr]

/-- The braid group $B_2$ is isomorphic to $ℤ$ (one generator, no non-trivial relations).
The isomorphism sends the unique generator $σ_0$ to $1 ∈ ℤ$. -/
def braidGroupTwoEquivInt : BraidGroup 2 ≃* Multiplicative ℤ := by
  -- BraidGroup 2 = (A 1).ArtinGroup = PresentedGroup (A 1).artinRelationsSet
  -- The relations are all trivial, so this equals FreeGroup (Fin 1) / ⊥ ≃ FreeGroup (Fin 1)
  -- First, show the quotient is by the trivial subgroup
  have h : Subgroup.normalClosure (CoxeterMatrix.A 1).artinRelationsSet = ⊥ := by
    rw [artinRelationsSet_A_one_eq_one, Subgroup.normalClosure_singleton_one]
  -- Chain: PresentedGroup rels ≃* FreeGroup (Fin 1) ⧸ ⊥ ≃*
  --        FreeGroup (Fin 1) ≃* FreeGroup Unit ≃* Multiplicative ℤ
  exact (QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientBot.trans
      ((FreeGroup.freeGroupCongr (Equiv.equivPUnit (Fin 1))).trans
        FreeGroup.freeGroupUnitMulEquivInt))

/-- The generator $σ_0$ of $B_2$ maps to $1$ under the isomorphism with $ℤ$. -/
@[simp]
theorem braidGroupTwoEquivInt_σ :
    braidGroupTwoEquivInt (σ 0) = Multiplicative.ofAdd 1 := by
  simp only [braidGroupTwoEquivInt, FreeGroup.freeGroupUnitMulEquivInt]
  rfl

end BraidGroup
