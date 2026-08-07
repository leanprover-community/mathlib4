/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Module.Submodule.EqLocus

/-! # Decomposition of tensor product

In this file, we describe the properties of decomposition under tensor product. Suppose `ℳ` is a
decomposition of an `R`-module `M` indexed by a type `ι`. Given an `R`-module `N`, the `R`-module
`M ⊗[R] N` has a decomposition into pieces `fun i ↦ (ℳ i) ⊗[R] N`. Given a commutative `R`-algebra
`S`, the `S`-module `S ⊗[R] M` has a decomposition `fun i ↦ (ℳ i).baseChange S`.
Given decompositions `ℳ`, `𝒩` of `M` and `N` and a degree function `f : ι × κ → μ`, the
`R`-module `M ⊗[R] N` has a decomposition `TensorProduct.gradeBy f ℳ 𝒩`, placing the image of
`(ℳ p) ⊗[R] (𝒩 q)` in degree `f (p, q)`; `TensorProduct.grade` is the total-degree case
`f (p, q) = p + q`.

-/

public section

open TensorProduct LinearMap

namespace DirectSum

variable {ι R M S : Type*}
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M)

section BaseChange

variable [DecidableEq ι] [Decomposition ℳ] [CommSemiring S] [Algebra R S]

instance Decomposition.baseChange : Decomposition fun i ↦ (ℳ i).baseChange S := by
  refine .ofLinearMap _ (lmap (ℳ · |>.toBaseChange S) ∘ₗ
    (directSumRight R S S fun i ↦ ℳ i).toLinearMap ∘ₗ
    ((decomposeLinearEquiv ℳ).baseChange R S)) ?_ ?_
  · simp_rw [← comp_assoc]
    rw [← LinearEquiv.eq_comp_toLinearMap_symm]
    ext
    simp
  · ext : 1
    rw [← LinearMap.cancel_right ((ℳ _).toBaseChange_surjective S)]
    ext : 3
    simp

theorem toBaseChange_injective (i : ι) : Function.Injective ((ℳ i).toBaseChange S) := fun x y h ↦ by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ · |>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S ⊗[R] M) fun i ↦ (ℳ i).baseChange S).bijective
  refine of_injective (β := fun i ↦ S ⊗[R] ℳ i) i <| this.injective ?_
  simpa using congr(of (fun i ↦ (ℳ i).baseChange S) i $h)

theorem toBaseChange_bijective (i : ι) : Function.Bijective ((ℳ i).toBaseChange S) :=
  ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

end BaseChange

section TensorModule

variable (N : Type*) [AddCommMonoid N] [Module R N]

/-- The submodule of a tensor product corresponding to a decomposition on the left. -/
def decomposeTensor (i : ι) : Submodule R (M ⊗[R] N) :=
  ((ℳ i).subtype.rTensor N).range

lemma decomposeTensor_apply {i : ι} :
    decomposeTensor ℳ N i = ((ℳ i).subtype.rTensor N).range :=
  Submodule.toSubMulAction_inj.mp rfl

variable [DecidableEq ι] [Decomposition ℳ]

lemma subtype_rTensor_injective (i : ι) :
    Function.Injective ((ℳ i).subtype.rTensor N) :=
  injective_of_comp_eq_id ((ℳ i).subtype.rTensor N)
    ((component R ι (fun i ↦ ℳ i) i ∘ₗ DirectSum.decomposeLinearEquiv ℳ).rTensor N)
    (by ext; simp)

/-- The linear isomorphism to the submodule from the tensor product with a summand. -/
noncomputable def decomposeTensorEquiv (i : ι) :
    (ℳ i) ⊗[R] N ≃ₗ[R] decomposeTensor ℳ N i :=
  LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)

lemma decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    decomposeTensorEquiv ℳ N i x =
      ⟨(ℳ i).subtype.rTensor N x, by convert (decomposeTensorEquiv ℳ N i x).property; rfl⟩ := by
  rfl

@[simp]
lemma val_decomposeTensorEquiv_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    decomposeTensorEquiv ℳ N i x = (ℳ i).subtype.rTensor N x := by rfl

lemma decomposeTensorEquiv_of_apply {i : ι} (x : (ℳ i) ⊗[R] N) :
    congrLinearEquiv (fun i ↦ decomposeTensorEquiv ℳ N i) (of (fun i ↦ ↥(ℳ i) ⊗[R] N) i x) =
      of (fun i ↦ decomposeTensor ℳ N i) i (decomposeTensorEquiv ℳ N i x) := by
  ext; simp [coe_congrLinearEquiv]

lemma decomposeLinearEquiv_comp_subtype {i : ι} :
    decomposeLinearEquiv ℳ ∘ₗ (ℳ i).subtype = lof R ι (fun i ↦ ℳ i) i := by
  ext; simp

lemma coe_decomposeTensor_apply (x : (⨁ i, decomposeTensor ℳ N i)) :
    DirectSum.coeAddMonoidHom (decomposeTensor ℳ N) x =
    (DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N
    ((TensorProduct.directSumLeft R R (fun i ↦ ℳ i) N).symm <|
      (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N).symm x) := by
  rw [← LinearEquiv.symm_rTensor, LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    obtain ⟨-, y, rfl⟩ := x
    have : (rTensor N (lof R ι (fun i ↦ ℳ i) i)) y =
        (directSumLeft R R (fun i ↦ ℳ i) N).symm ((of (fun i ↦ ℳ i ⊗[R] N) i) y) :=
      (TensorProduct.directSumLeft_symm_of R R (M₁ := fun i ↦ ℳ i) y).symm
    rw [coeAddMonoidHom_of, LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply,
      ← (LinearEquiv.rTensor N _).coe_coe, LinearEquiv.coe_rTensor, ← rTensor_comp_apply,
      decomposeLinearEquiv_comp_subtype, this, LinearEquiv.apply_symm_apply,
      decomposeTensorEquiv_of_apply, decomposeTensorEquiv_apply]
  | add x y hx hy => simp [hx, hy]

/-- The decomposition of a tensor product induced by a decomposition of the left module. -/
@[reducible]
noncomputable def tensorDecomposition (N : Type*) [AddCommGroup N] [Module R N] :
    DirectSum.Decomposition (decomposeTensor ℳ N) where
  decompose' x := (DirectSum.congrLinearEquiv <| decomposeTensorEquiv ℳ N)
    (directSumLeft R R (fun i ↦ ℳ i) N <| (DirectSum.decomposeLinearEquiv ℳ).rTensor N x)
  left_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]
  right_inv x := by simp [coe_decomposeTensor_apply ℳ N _, ← LinearEquiv.symm_rTensor]

end TensorModule

namespace IsInternal

variable [DecidableEq ι] [CommSemiring S] [Algebra R S]

theorem baseChange (hm : IsInternal ℳ) : IsInternal fun i ↦ (ℳ i).baseChange S :=
  haveI := hm.chooseDecomposition
  Decomposition.isInternal _

theorem toBaseChange_bijective (hm : IsInternal ℳ) (i : ι) :
    Function.Bijective ((ℳ i).toBaseChange S) :=
  haveI := hm.chooseDecomposition
  DirectSum.toBaseChange_bijective ℳ i

theorem toBaseChange_injective (hm : IsInternal ℳ) (i : ι) :
    Function.Injective ((ℳ i).toBaseChange S) :=
  (toBaseChange_bijective ℳ hm i).injective

end IsInternal

end DirectSum

namespace TensorProduct

variable {ι κ μ R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The submodule of `M ⊗[R] N` corresponding to each grade, given by the degree function `f`
on pairs of degrees. -/
def gradeBy (f : ι × κ → μ) (ℳ : ι → Submodule R M) (𝒩 : κ → Submodule R N) (m : μ) :
    Submodule R (M ⊗[R] N) :=
  ⨆ (pq) (_ : f pq = m), Submodule.map₂ (mk R M N) (ℳ pq.1) (𝒩 pq.2)

section GradeBy

variable (f : ι × κ → μ) {ℳ : ι → Submodule R M} {𝒩 : κ → Submodule R N}

theorem map₂_le_gradeBy (p : ι) (q : κ) :
    Submodule.map₂ (mk R M N) (ℳ p) (𝒩 q) ≤ gradeBy f ℳ 𝒩 (f (p, q)) :=
  le_iSup₂_of_le (p, q) rfl le_rfl

theorem tmul_mem_gradeBy {p : ι} {q : κ} {x : M} {y : N} (hx : x ∈ ℳ p) (hy : y ∈ 𝒩 q) :
    x ⊗ₜ[R] y ∈ gradeBy f ℳ 𝒩 (f (p, q)) :=
  map₂_le_gradeBy f p q (Submodule.apply_mem_map₂ _ hx hy)

theorem gradeBy_le {m : μ} {P : Submodule R (M ⊗[R] N)} :
    gradeBy f ℳ 𝒩 m ≤ P ↔ ∀ p q, f (p, q) = m → ∀ x ∈ ℳ p, ∀ y ∈ 𝒩 q, x ⊗ₜ[R] y ∈ P := by
  simp [gradeBy, iSup_le_iff, Submodule.map₂_le, Prod.forall]

open DirectSum

variable (ℳ 𝒩) [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]
  [Decomposition ℳ] [Decomposition 𝒩]

/-- The decomposition of a tensor product induced by decompositions of the two factors. -/
@[no_expose] instance gradeBy.decomposition : Decomposition (gradeBy f ℳ 𝒩) :=
  .ofLinearMap _ ((toModule R (ι × κ) _ fun pq ↦
      lof R μ (gradeBy f ℳ 𝒩 ·) (f pq) ∘ₗ mapInclOfLE (map₂_le_gradeBy f pq.1 pq.2)) ∘ₗ
      ↑(congr (decomposeLinearEquiv ℳ) (decomposeLinearEquiv 𝒩) ≪≫ₗ
        TensorProduct.directSum R R (ℳ ·) (𝒩 ·)))
    (by rw [← comp_assoc, ← LinearEquiv.eq_comp_toLinearMap_symm]; ext ⟨p, q⟩ x y; simp)
    (by
      refine linearMap_ext _ fun m ↦ LinearMap.ext fun z ↦ ?_
      rw [id_comp, comp_apply, comp_apply, coeLinearMap_lof]
      refine DFinsupp.eq_single_iff.2 ⟨fun m' hm ↦ ?_, ?_⟩ <;> rw [apply_eq_component R]
      · refine (gradeBy_le f (P := ker (component R μ (gradeBy f ℳ 𝒩 ·) m' ∘ₗ _))).2 ?_ z.2
        rintro p q rfl x hx y hy; lift x to ℳ p using hx; lift y to 𝒩 q using hy
        simp [mem_ker, component.of, Ne.symm hm]
      · refine Subtype.ext ((gradeBy_le f (P := eqLocus
          ((gradeBy f ℳ 𝒩 m).subtype ∘ₗ component R μ (gradeBy f ℳ 𝒩 ·) m ∘ₗ _) .id)).2 ?_ z.2)
        rintro p q rfl x hx y hy; lift x to ℳ p using hx; lift y to 𝒩 q using hy
        simp)

theorem gradeBy.decompose_tmul {p : ι} {q : κ} {x : M} {y : N} (hx : x ∈ ℳ p) (hy : y ∈ 𝒩 q) :
    decompose (gradeBy f ℳ 𝒩) (x ⊗ₜ[R] y) = .of _ (f (p, q)) ⟨x ⊗ₜ y, tmul_mem_gradeBy f hx hy⟩ :=
  decompose_of_mem _ (tmul_mem_gradeBy f hx hy)

/-- `M ⊗[R] N` is the internal direct sum of the graded pieces. -/
theorem gradeBy.isInternal : IsInternal (gradeBy f ℳ 𝒩) :=
  Decomposition.isInternal _

end GradeBy

/-- The submodule of `M ⊗[R] N` corresponding to each total degree. -/
@[expose] def grade [Add ι] (ℳ : ι → Submodule R M) (𝒩 : ι → Submodule R N) (n : ι) :
    Submodule R (M ⊗[R] N) :=
  gradeBy (fun pq ↦ pq.1 + pq.2) ℳ 𝒩 n

section Grade

variable [Add ι] (ℳ : ι → Submodule R M) (𝒩 : ι → Submodule R N)

theorem grade_eq_gradeBy : grade ℳ 𝒩 = gradeBy (fun pq ↦ pq.1 + pq.2) ℳ 𝒩 :=
  rfl

variable {ℳ 𝒩}

theorem tmul_mem_grade {p q : ι} {x : M} {y : N} (hx : x ∈ ℳ p) (hy : y ∈ 𝒩 q) :
    x ⊗ₜ[R] y ∈ grade ℳ 𝒩 (p + q) :=
  tmul_mem_gradeBy _ hx hy

theorem grade_le {n : ι} {P : Submodule R (M ⊗[R] N)} :
    grade ℳ 𝒩 n ≤ P ↔ ∀ i j, i + j = n → ∀ x ∈ ℳ i, ∀ y ∈ 𝒩 j, x ⊗ₜ[R] y ∈ P :=
  gradeBy_le _

open DirectSum

variable (ℳ 𝒩) [DecidableEq ι] [Decomposition ℳ] [Decomposition 𝒩]

@[no_expose] instance grade.decomposition : Decomposition (grade ℳ 𝒩) :=
  inferInstanceAs <| Decomposition (gradeBy (fun pq ↦ pq.1 + pq.2) ℳ 𝒩)

theorem grade.decompose_tmul {p q : ι} {x : M} {y : N} (hx : x ∈ ℳ p) (hy : y ∈ 𝒩 q) :
    decompose (grade ℳ 𝒩) (x ⊗ₜ[R] y) = .of _ (p + q) ⟨x ⊗ₜ y, tmul_mem_grade hx hy⟩ :=
  decompose_of_mem _ (tmul_mem_grade hx hy)

/-- `M ⊗[R] N` is the internal direct sum of the total-degree pieces. -/
theorem grade.isInternal : IsInternal (grade ℳ 𝒩) :=
  Decomposition.isInternal _

end Grade

end TensorProduct
