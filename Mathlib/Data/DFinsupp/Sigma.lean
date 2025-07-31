/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.Data.DFinsupp.Module
import Mathlib.Data.Fintype.Quotient

/-!
# `DFinsupp` on `Sigma` types

## Main definitions

* `DFinsupp.sigmaCurry`: turn a `DFinsupp` indexed by a `Sigma` type into a `DFinsupp` with two
  parameters.
* `DFinsupp.sigmaUncurry`: turn a `DFinsupp` with two parameters into a `DFinsupp` indexed by a
  `Sigma` type. Inverse of `DFinsupp.sigmaCurry`.
* `DFinsupp.sigmaCurryEquiv`: `DFinsupp.sigmaCurry` and `DFinsupp.sigmaUncurry` bundled into a
  bijection.

-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Equiv

open Finset

variable {κ : Type*}

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

variable [DecidableEq ι]

/-- The natural map between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`. -/
def sigmaCurry [∀ i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    Π₀ (i) (j), δ i j where
  toFun := fun i ↦
  { toFun := fun j ↦ f ⟨i, j⟩,
    support' := f.support'.map (fun ⟨m, hm⟩ ↦
      ⟨m.filterMap (fun ⟨i', j'⟩ ↦ if h : i' = i then some <| h.rec j' else none),
        fun j ↦ (hm ⟨i, j⟩).imp_left (fun h ↦ (m.mem_filterMap _).mpr ⟨⟨i, j⟩, h, dif_pos rfl⟩)⟩) }
  support' := f.support'.map (fun ⟨m, hm⟩ ↦
    ⟨m.map Sigma.fst, fun i ↦ Decidable.or_iff_not_imp_left.mpr (fun h ↦ DFinsupp.ext
      (fun j ↦ (hm ⟨i, j⟩).resolve_left (fun H ↦ (Multiset.mem_map.not.mp h) ⟨⟨i, j⟩, H, rfl⟩)))⟩)

@[simp]
theorem sigmaCurry_apply [∀ i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  rfl

@[simp]
theorem sigmaCurry_zero [∀ i j, Zero (δ i j)] :
    sigmaCurry (0 : Π₀ (i : Σ _, _), δ i.1 i.2) = 0 :=
  rfl

@[simp]
theorem sigmaCurry_add [∀ i j, AddZeroClass (δ i j)] (f g : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (f + g) = (sigmaCurry f + sigmaCurry g : Π₀ (i) (j), δ i j) := by
  ext (i j)
  rfl

@[simp]
theorem sigmaCurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)] [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (r • f) = (r • sigmaCurry f : Π₀ (i) (j), δ i j) := by
  ext (i j)
  rfl

@[simp]
theorem sigmaCurry_single [∀ i, DecidableEq (α i)] [∀ i j, Zero (δ i j)]
    (ij : Σ i, α i) (x : δ ij.1 ij.2) :
    sigmaCurry (single ij x) = single ij.1 (single ij.2 x : Π₀ j, δ ij.1 j) := by
  obtain ⟨i, j⟩ := ij
  ext i' j'
  dsimp only
  rw [sigmaCurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
  · rw [single_eq_of_ne, single_eq_of_ne hi, zero_apply]
    simp [hi]

/-- The natural map between `Π₀ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`. -/
def sigmaUncurry [∀ i j, Zero (δ i j)] [DecidableEq ι] (f : Π₀ (i) (j), δ i j) :
    Π₀ i : Σ _, _, δ i.1 i.2 where
  toFun i := f i.1 i.2
  support' :=
    f.support'.bind fun s =>
      (Trunc.finChoice (fun i : ↥s.val.toFinset => (f i).support')).map fun fs =>
        ⟨s.val.toFinset.attach.val.bind fun i => (fs i).val.map (Sigma.mk i.val), by
          rintro ⟨i, a⟩
          cases s.prop i with
          | inl hi =>
            cases (fs ⟨i, Multiset.mem_toFinset.mpr hi⟩).prop a with
            | inl ha =>
              left; rw [Multiset.mem_bind]
              use ⟨i, Multiset.mem_toFinset.mpr hi⟩
              constructor
              case right => simp [ha]
              case left => apply Multiset.mem_attach
            | inr ha => right; simp [toFun_eq_coe (f i) ▸ ha]
          | inr hi => right; simp [toFun_eq_coe f ▸ hi]⟩

@[simp]
theorem sigmaUncurry_apply [∀ i j, Zero (δ i j)]
    (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  rfl

@[simp]
theorem sigmaUncurry_zero [∀ i j, Zero (δ i j)] :
    sigmaUncurry (0 : Π₀ (i) (j), δ i j) = 0 :=
  rfl

@[simp]
theorem sigmaUncurry_add [∀ i j, AddZeroClass (δ i j)] (f g : Π₀ (i) (j), δ i j) :
    sigmaUncurry (f + g) = sigmaUncurry f + sigmaUncurry g :=
  DFunLike.coe_injective rfl

@[simp]
theorem sigmaUncurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • f) = r • sigmaUncurry f :=
  DFunLike.coe_injective rfl

@[simp]
theorem sigmaUncurry_single [∀ i j, Zero (δ i j)] [∀ i, DecidableEq (α i)]
    (i) (j : α i) (x : δ i j) :
    sigmaUncurry (single i (single j x : Π₀ j : α i, δ i j)) = single ⟨i, j⟩ (by exact x) := by
  ext ⟨i', j'⟩
  dsimp only
  rw [sigmaUncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
  · rw [single_eq_of_ne hi, single_eq_of_ne, zero_apply]
    simp [hi]

/-- The natural bijection between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.

This is the dfinsupp version of `Equiv.piCurry`. -/
def sigmaCurryEquiv [∀ i j, Zero (δ i j)] [DecidableEq ι] :
    (Π₀ i : Σ _, _, δ i.1 i.2) ≃ Π₀ (i) (j), δ i j where
  toFun := sigmaCurry
  invFun := sigmaUncurry
  left_inv f := by
    ext ⟨i, j⟩
    rw [sigmaUncurry_apply, sigmaCurry_apply]
  right_inv f := by
    ext i j
    rw [sigmaCurry_apply, sigmaUncurry_apply]

end SigmaCurry

end Equiv

end DFinsupp
