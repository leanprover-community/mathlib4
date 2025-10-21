/-
Copyright (c) 2025 Antoine Chambert-Loir and María-Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos Fernández
-/

import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Adjoin.FG

/-! # Tensor products and finitely generated submodules

Various results about how tensor products of arbitrary modules are direct limits of
tensor products of finitely-generated modules.

## Main definitions

* `Submodule.FG.directedSystem`, the directed system of finitely generated submodules of a module.

* `Submodule.FG.directLimit` proves that a module is the direct limit
  of its finitely generated submodules, with respect to the inclusion maps

* `DirectedSystem.rTensor`, the directed system deduced from a directed system of modules
  by applying `rTensor`.

* `Submodule.FG.rTensor.directSystem`, the directed system of
  modules `P ⊗[R] N`, for all finitely generated
  submodules `P`, with respect to the maps deduced from the inclusions

* `Submodule.FG.rTensor.directLimit` : a tensor product `M ⊗[R] N` is the direct limit
  of the modules `P ⊗[R] N`, where `P` ranges over all finitely generated submodules of `M`,
  as a linear equivalence.

* `DirectedSystem.lTensor`, the directed system deduced from a directed system of modules
  by applying `lTensor`.

* `Submodule.FG.lTensor.directSystem`, the directed system of
  modules `M ⊗[R] Q`, for all finitely generated
  submodules `Q`, with respect to the maps deduced from the inclusions

* `Submodule.FG.lTensor.directLimit` : a tensor product `M ⊗[R] N` is the direct limit
  of the modules `M ⊗[R] Q`, where `Q` ranges over all finitely generated submodules of `N`,
  as a linear equivalence.
-/

open Submodule LinearMap

section Semiring

universe u v
variable {R : Type u} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- The directed system of finitely generated submodules of `M` -/
instance Submodule.FG.directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (F := fun P ↦ P.val)
    (f := fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) where
  map_self := fun _ _ ↦ rfl
  map_map  := fun _ _ _ _ _ _ ↦ rfl

variable (R M) in
/-- Any module is the direct limit of its finitely generated submodules -/
noncomputable def Submodule.FG.directLimit [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (ι := {P : Submodule R M // P.FG}) (G := fun P ↦ P.val)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) ≃ₗ[R] M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P ↦ P.val.subtype) (fun _ _ _ _ ↦ rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P ↦ Submodule.injective_subtype P.val),
      fun x ↦ ⟨Module.DirectLimit.of _ {P : Submodule R M // P.FG} _ _
          ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩
          ⟨x, Submodule.mem_span_singleton_self x⟩,
         by simp⟩⟩

end Semiring

section TensorProducts

open TensorProduct

universe u v

variable (R : Type u) (M N : Type*)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Given a directed system of `R`-modules, tensoring it on the right gives a directed system -/
theorem DirectedSystem.rTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ (F i) ⊗[R] N) (fun _ _ h ↦ rTensor N (f h)) where
  map_self i t := by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply, ← rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/-- When `P` ranges over finitely generated submodules of `M`,
  the modules of the form `P ⊗[R] N` form a directed system. -/
theorem Submodule.FG.rTensor.directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
    (fun ⦃_ _⦄ h ↦ rTensor N (Submodule.inclusion h)) :=
  Submodule.FG.directedSystem.rTensor R N

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all finitely generated submodules of `M`, as a linear equivalence. -/
noncomputable def Submodule.FG.rTensor.directLimit [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (R := R) (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ (Submodule.inclusion h).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodule.FG.directLimit R M).rTensor N)

theorem Submodule.FG.rTensor.directLimit_apply [DecidableEq {P : Submodule R M // P.FG}]
    {P : {P : Submodule R M // P.FG}} (u : P ⊗[R] N) :
    (Submodule.FG.rTensor.directLimit R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ (Submodule.inclusion h).rTensor N) P) u)
      = (rTensor N (Submodule.subtype P)) u := by
  suffices (Submodule.FG.rTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun _ _ hPQ ↦ rTensor N (Submodule.inclusion hPQ)) P)
      = rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [Submodule.FG.rTensor.directLimit, Submodule.FG.directLimit]

/-- An alternative version to `Submodule.FG.rTensor.directLimit_apply`. -/
theorem Submodule.FG.rTensor.directLimit_apply' [DecidableEq {P : Submodule R M // P.FG}]
    {P : Submodule R M} (hP : Submodule.FG P) (u : P ⊗[R] N) :
    (Submodule.FG.rTensor.directLimit R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ rTensor N (Submodule.inclusion h)) ⟨P, hP⟩) u)
      = (rTensor N (Submodule.subtype P)) u := by
  apply Submodule.FG.rTensor.directLimit_apply

/-- Given a directed system of `R`-modules, tensoring it on the left gives a directed system -/
theorem DirectedSystem.lTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ M ⊗[R] (F i)) (fun _ _ h ↦ lTensor M (f h)) where
  map_self i t := by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply, ← lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/-- When `Q` ranges over finitely generated submodules of `N`,
  the modules of the form `M ⊗[R] Q` form a directed system. -/
theorem Submodule.FG.lTensor.directedSystem :
    DirectedSystem (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ lTensor M (Submodule.inclusion hPQ)) :=
  Submodule.FG.directedSystem.lTensor R M

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `M ⊗[R] Q`,
where `Q` ranges over all finitely generated submodules of `N`, as a linear equivalence. -/
noncomputable def Submodule.FG.lTensor.directLimit [DecidableEq {Q : Submodule R N // Q.FG}] :
    Module.DirectLimit (R := R) (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ (inclusion hPQ).lTensor M) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitRight _ M).symm.trans ((Submodule.FG.directLimit R N).lTensor M)

theorem Submodule.FG.lTensor.directLimit_apply [DecidableEq {P : Submodule R N // P.FG}]
    (Q : {Q : Submodule R N // Q.FG}) (u : M ⊗[R] Q.val) :
    (Submodule.FG.lTensor.directLimit R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ (inclusion hPQ).lTensor M) Q) u)
      = (lTensor M (Submodule.subtype Q.val)) u := by
  suffices (Submodule.FG.lTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ lTensor M (inclusion hPQ)) Q)
      = lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [Submodule.FG.lTensor.directLimit, Submodule.FG.directLimit]

theorem Submodule.FG.lTensor.directLimit_apply' [DecidableEq {Q : Submodule R N // Q.FG}]
    (Q : Submodule R N) (hQ : Q.FG) (u : M ⊗[R] Q) :
    (Submodule.FG.lTensor.directLimit R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ lTensor M (inclusion hPQ)) ⟨Q, hQ⟩) u)
      = (lTensor M (Submodule.subtype Q)) u :=
  Submodule.FG.lTensor.directLimit_apply R M N ⟨Q, hQ⟩ u

variable {R M N} (u : M ⊗[R] N)
    {P : Submodule R M} (hP : Submodule.FG P) {t : P ⊗[R] N}
    {P' : Submodule R M} (hP' : Submodule.FG P') {t' : P' ⊗[R] N}

theorem TensorProduct.exists_of_fg :
    ∃ (P : Submodule R M), P.FG ∧ u ∈ range (rTensor N P.subtype) := by
  classical
  let ⟨P, t, ht⟩ := Module.DirectLimit.exists_of ((Submodule.FG.rTensor.directLimit R M N).symm u)
  use P.val, P.property, t
  rw [← Submodule.FG.rTensor.directLimit_apply, ht, LinearEquiv.apply_symm_apply]

include hP in
theorem TensorProduct.eq_of_fg_of_subtype_eq {t' : P ⊗[R] N}
    (h : rTensor N P.subtype t = rTensor N P.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      rTensor N (inclusion hPQ) t = rTensor N (inclusion hPQ) t' := by
  classical
  simp only [← Submodule.FG.rTensor.directLimit_apply' R M N hP, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property

include hP in
theorem TensorProduct.eq_zero_of_fg_of_subtype_eq_zero (h : rTensor N P.subtype t = 0) :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧ rTensor N (inclusion hPQ) t = 0 := by
  rw [← (rTensor N P.subtype).map_zero] at h
  simpa only [map_zero] using TensorProduct.eq_of_fg_of_subtype_eq hP h

include hP hP' in
theorem TensorProduct.eq_of_fg_of_subtype_eq'
    (h : rTensor N P.subtype t = rTensor N P'.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q) (hP'Q : P' ≤ Q), Q.FG ∧
      rTensor N (inclusion hPQ) t = rTensor N (inclusion hP'Q) t' := by
  simp only [← subtype_comp_inclusion _ _ (le_sup_left : _ ≤ P ⊔ P'),
    ← subtype_comp_inclusion _ _ (le_sup_right : _ ≤ P ⊔ P'),
    rTensor_comp, coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq (hP.sup hP') h
  use Q, le_trans le_sup_left hQ_le, le_trans le_sup_right hQ_le, hQ
  simpa [← comp_apply, ← rTensor_comp] using h

end TensorProducts

section Algebra

open TensorProduct

variable {R S M N : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (u : S ⊗[R] N)
  {A : Subalgebra R S} (hA : A.FG) {t t' : A ⊗[R] N}
  {A' : Subalgebra R S} (hA' : A'.FG)

theorem TensorProduct.Algebra.exists_of_fg :
    ∃ (A : Subalgebra R S), Subalgebra.FG A ∧ u ∈ range (rTensor N A.val.toLinearMap) := by
  obtain ⟨P, ⟨s, hs⟩, hu⟩ := TensorProduct.exists_of_fg u
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P ≤ (Algebra.adjoin R (s : Set S)).toSubmodule := by
    simp only [← hs, span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← subtype_comp_inclusion P _ this, rTensor_comp] at hu
  exact range_comp_le_range _ _ hu

include hA in
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (h : rTensor N A.val.toLinearMap t = rTensor N A.val.toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B), Subalgebra.FG B
      ∧ rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t' := by
  classical
  let ⟨P, hP, u, hu⟩ := TensorProduct.exists_of_fg t
  let ⟨P', hP', u', hu'⟩ := TensorProduct.exists_of_fg t'
  let P₁ := Submodule.map A.toSubmodule.subtype (P ⊔ P')
  have hP₁ : Submodule.FG P₁ := Submodule.FG.map _ (Submodule.FG.sup hP hP')
  -- the embeddings from P and P' to P₁
  let j : P →ₗ[R] P₁ := (Subalgebra.toSubmodule A).subtype.restrict
      (fun p hp ↦ by
        simp only [coe_subtype, Submodule.map_sup, P₁]
        exact Submodule.mem_sup_left ⟨p, hp, rfl⟩)
  let j' : P' →ₗ[R] P₁ := (Subalgebra.toSubmodule A).subtype.restrict
      (fun p hp ↦ by
        simp only [coe_subtype, Submodule.map_sup, P₁]
        exact Submodule.mem_sup_right ⟨p, hp, rfl⟩)
  -- we map u and u' to P₁ ⊗[R] N, getting u₁ and u'₁
  set u₁ := rTensor N j u with hu₁
  set u'₁ := rTensor N j' u' with hu'₁
  -- u₁ and u'₁ are equal in S ⊗[R] N
  have : rTensor N P₁.subtype u₁ = rTensor N P₁.subtype u'₁ := by
    rw [hu₁, hu'₁]
    simp only [← comp_apply, ← rTensor_comp]
    have hj₁ : P₁.subtype ∘ₗ j = A.val.toLinearMap ∘ₗ P.subtype := rfl
    have hj'₁ : P₁.subtype ∘ₗ j' = A.val.toLinearMap ∘ₗ P'.subtype := rfl
    rw [hj₁, hj'₁]
    simp only [rTensor_comp, comp_apply]
    rw [hu, hu', h]
  let ⟨P'₁, hP₁_le, hP'₁, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq hP₁ this
  let ⟨s, hs⟩ := hP'₁
  let ⟨w, hw⟩ := hA
  let B := Algebra.adjoin R ((s ∪ w : Finset S) : Set S)
  have hBA : A ≤ B := by
    simp only [B, ← hw]
    apply Algebra.adjoin_mono
    simp only [Finset.coe_union, Set.subset_union_right]
  use B, hBA, Subalgebra.fg_adjoin_finset _
  rw [← hu, ← hu']
  simp only [← comp_apply, ← rTensor_comp]
  have hP'₁_le : P'₁ ≤ B.toSubmodule := by
    simp only [← hs, Finset.coe_union, Submodule.span_le, Subalgebra.coe_toSubmodule, B]
    exact subset_trans Set.subset_union_left Algebra.subset_adjoin
  have k : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P.subtype
    = inclusion hP'₁_le ∘ₗ inclusion hP₁_le ∘ₗ j := by ext; rfl
  have k' : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P'.subtype
    = inclusion hP'₁_le ∘ₗ inclusion hP₁_le ∘ₗ j' := by ext; rfl
  rw [k, k']
  simp only [rTensor_comp, comp_apply]
  rw [← hu₁, ← hu'₁, h]

include hA hA' in
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq' {t' : A' ⊗[R] N}
    (h : rTensor N A.val.toLinearMap t = rTensor N A'.val.toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B) (hA'B : A' ≤ B), Subalgebra.FG B
      ∧ rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = rTensor N (Subalgebra.inclusion hA'B).toLinearMap t' := by
  have hj : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_left) = A.val := by ext; rfl
  have hj' : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_right) = A'.val := by ext; rfl
  simp only [← hj, ← hj', AlgHom.comp_toLinearMap, rTensor_comp, comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (Subalgebra.FG.sup hA hA') h
  use B, le_trans le_sup_left hB_le, le_trans le_sup_right hB_le, hB
  simpa only [← rTensor_comp, ← comp_apply] using h

/-- Lift an element that maps to 0 -/
theorem Submodule.exists_fg_of_baseChange_eq_zero
    (f : M →ₗ[R] N) {t : S ⊗[R] M} (ht : f.baseChange S t = 0) :
    ∃ (A : Subalgebra R S) (_ : A.FG) (u : A ⊗[R] M),
      f.baseChange A u = 0 ∧ A.val.toLinearMap.rTensor M u = t := by
  classical
  obtain ⟨A, hA, ht_memA⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨u, hu⟩ := _root_.id ht_memA
  have := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hA (t := f.baseChange _ u) (t' := 0)
  simp only [map_zero, exists_and_left] at this
  have hu' : (A.val.toLinearMap.rTensor N) (f.baseChange (↥A) u) = 0 := by
    rw [← ht, ← hu, rTensor_baseChange]
  obtain ⟨B, hB, hAB, hu'⟩ := this hu'
  use B, hB, rTensor M (Subalgebra.inclusion hAB).toLinearMap u
  constructor
  · rw [← rTensor_baseChange, hu']
  · rw [← comp_apply, ← rTensor_comp, ← hu]
    congr

end Algebra
