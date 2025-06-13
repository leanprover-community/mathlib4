/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle
-/
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Trace of a linear map

This file defines the trace of a linear map.

See also `LinearAlgebra/Matrix/Trace.lean` for the trace of a matrix.

## Tags

linear_map, trace, diagonal
-/

noncomputable section

universe u v w

namespace LinearMap

open scoped Matrix
open Module TensorProduct

section

variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [DecidableEq ι] [Fintype ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ]
variable (b : Basis ι R M) (c : Basis κ R M)

/-- The trace of an endomorphism given a basis. -/
def traceAux : (M →ₗ[R] M) →ₗ[R] R :=
  Matrix.traceLinearMap ι R R ∘ₗ ↑(LinearMap.toMatrix b b)

-- Can't be `simp` because it would cause a loop.
theorem traceAux_def (b : Basis ι R M) (f : M →ₗ[R] M) :
    traceAux R b f = Matrix.trace (LinearMap.toMatrix b b f) :=
  rfl

theorem traceAux_eq : traceAux R b = traceAux R c :=
  LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix b b f) =
          Matrix.trace (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) := by
        rw [LinearMap.id_comp, LinearMap.comp_id]
      _ = Matrix.trace (LinearMap.toMatrix c b LinearMap.id * LinearMap.toMatrix c c f *
          LinearMap.toMatrix b c LinearMap.id) := by
        rw [LinearMap.toMatrix_comp _ c, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f * LinearMap.toMatrix b c LinearMap.id *
          LinearMap.toMatrix c b LinearMap.id) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.toMatrix_comp _ b, LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f) := by rw [LinearMap.comp_id, LinearMap.comp_id]

variable (M) in
open Classical in
/-- Trace of an endomorphism independent of basis. -/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
  if H : ∃ s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0

open Classical in
/-- Auxiliary lemma for `trace_eq_matrix_trace`. -/
theorem trace_eq_matrix_trace_of_finset {s : Finset M} (b : Basis s R M) (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace, dif_pos this, ← traceAux_def]
  congr 1
  apply traceAux_eq

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  classical
  rw [trace_eq_matrix_trace_of_finset R b.reindexFinsetRange, ← traceAux_def, ← traceAux_def,
    traceAux_eq R b b.reindexFinsetRange]

theorem trace_mul_comm (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Basis s R M)
  · let ⟨s, ⟨b⟩⟩ := H
    simp_rw [trace_eq_matrix_trace R b, LinearMap.toMatrix_mul]
    apply Matrix.trace_mul_comm
  · rw [trace, dif_neg H, LinearMap.zero_apply, LinearMap.zero_apply]

lemma trace_mul_cycle (f g h : M →ₗ[R] M) :
    trace R M (f * g * h) = trace R M (h * f * g) := by
  rw [LinearMap.trace_mul_comm, ← mul_assoc]

lemma trace_mul_cycle' (f g h : M →ₗ[R] M) :
    trace R M (f * (g * h)) = trace R M (h * (f * g)) := by
  rw [← mul_assoc, LinearMap.trace_mul_comm]

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
theorem trace_conj (g : M →ₗ[R] M) (f : (M →ₗ[R] M)ˣ) :
    trace R M (↑f * g * ↑f⁻¹) = trace R M g := by
  rw [trace_mul_comm]
  simp

@[simp]
lemma trace_lie {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f g : Module.End R M) :
    trace R M ⁅f, g⁆ = 0 := by
  rw [Ring.lie_def, map_sub, trace_mul_comm]
  exact sub_self _

end

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable (N P : Type*) [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {ι : Type*}

/-- The trace of a linear map correspond to the contraction pairing under the isomorphism
`End(M) ≃ M* ⊗ M` -/
theorem trace_eq_contract_of_basis [Finite ι] (b : Basis ι R M) :
    LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M := by
  classical
    cases nonempty_fintype ι
    apply Basis.ext (Basis.tensorProduct (Basis.dualBasis b) b)
    rintro ⟨i, j⟩
    simp only [Function.comp_apply, Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp]
    rw [trace_eq_matrix_trace R b, toMatrix_dualTensorHom]
    obtain rfl | hij := eq_or_ne i j
    · simp
    rw [Matrix.trace_single_eq_of_ne j i (1 : R) hij.symm]
    simp [Finsupp.single_eq_pi_single, hij]

/-- The trace of a linear map corresponds to the contraction pairing under the isomorphism
`End(M) ≃ M* ⊗ M`. -/
theorem trace_eq_contract_of_basis' [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquivOfBasis b).symm.toLinearMap := by
  simp [LinearEquiv.eq_comp_toLinearMap_symm, trace_eq_contract_of_basis b]

section
variable (R M)
variable [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]

/-- When `M` is finite free, the trace of a linear map corresponds to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`. -/
@[simp]
theorem trace_eq_contract : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M :=
  trace_eq_contract_of_basis (Module.Free.chooseBasis R M)

@[simp]
theorem trace_eq_contract_apply (x : Module.Dual R M ⊗[R] M) :
    (LinearMap.trace R M) ((dualTensorHom R M M) x) = contractLeft R M x := by
  rw [← comp_apply, trace_eq_contract]

/-- When `M` is finite free, the trace of a linear map corresponds to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`. -/
theorem trace_eq_contract' :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap :=
  trace_eq_contract_of_basis' (Module.Free.chooseBasis R M)

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
theorem trace_one : trace R M 1 = (finrank R M : R) := by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b, toMatrix_one, finrank_eq_card_chooseBasisIndex]
  simp

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
theorem trace_id : trace R M id = (finrank R M : R) := by rw [← Module.End.one_eq_id, trace_one]

@[simp]
theorem trace_transpose : trace R (Module.Dual R M) ∘ₗ Module.Dual.transpose = trace R M := by
  let e := dualTensorHomEquiv R M M
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f m; simp [e]

theorem trace_prodMap :
    trace R (M × N) ∘ₗ prodMapLinear R M N M N R =
      (coprod id id : R × R →ₗ[R] R) ∘ₗ prodMap (trace R M) (trace R N) := by
  let e := (dualTensorHomEquiv R M M).prodCongr (dualTensorHomEquiv R N N)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext
  · simp only [dualTensorHomEquiv, LinearEquiv.coe_prodCongr,
      dualTensorHomEquivOfBasis_toLinearMap, AlgebraTensorModule.curry_apply, restrictScalars_comp,
      curry_apply, coe_comp, coe_restrictScalars, coe_inl, Function.comp_apply, prodMap_apply,
      map_zero, prodMapLinear_apply, dualTensorHom_prodMap_zero, trace_eq_contract_apply,
      contractLeft_apply, coe_fst, coprod_apply, id_coe, id_eq, add_zero, e]
  · simp only [dualTensorHomEquiv, LinearEquiv.coe_prodCongr,
      dualTensorHomEquivOfBasis_toLinearMap, AlgebraTensorModule.curry_apply, restrictScalars_comp,
      curry_apply, coe_comp, coe_restrictScalars, coe_inr, Function.comp_apply, prodMap_apply,
      map_zero, prodMapLinear_apply, zero_prodMap_dualTensorHom, trace_eq_contract_apply,
      contractLeft_apply, coe_snd, coprod_apply, id_coe, id_eq, zero_add, e]

variable {R M N P}

theorem trace_prodMap' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M × N) (prodMap f g) = trace R M f + trace R N g := by
  have h := LinearMap.ext_iff.1 (trace_prodMap R M N) (f, g)
  simp only [coe_comp, Function.comp_apply, prodMap_apply, coprod_apply, id_coe, id,
    prodMapLinear_apply] at h
  exact h

variable (R M N P)

open TensorProduct Function

theorem trace_tensorProduct : compr₂ (mapBilinear R M N M N) (trace R (M ⊗ N)) =
    compl₁₂ (lsmul R R : R →ₗ[R] R →ₗ[R] R) (trace R M) (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R M M) from (dualTensorHomEquiv R M M).surjective)
        (show Surjective (dualTensorHom R N N) from (dualTensorHomEquiv R N N).surjective)).1
  ext f m g n
  simp only [AlgebraTensorModule.curry_apply, toFun_eq_coe, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, mapBilinear_apply,
    trace_eq_contract_apply, contractLeft_apply, lsmul_apply, Algebra.id.smul_eq_mul,
    map_dualTensorHom, dualDistrib_apply]

theorem trace_comp_comm :
    compr₂ (llcomp R M N M) (trace R M) = compr₂ (llcomp R N M N).flip (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R N M) from (dualTensorHomEquiv R N M).surjective)
        (show Surjective (dualTensorHom R M N) from (dualTensorHomEquiv R M N).surjective)).1
  ext g m f n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, flip_apply, llcomp_apply',
    comp_dualTensorHom, LinearMapClass.map_smul, trace_eq_contract_apply,
    contractLeft_apply, smul_eq_mul, mul_comm]

variable {R M N P}

@[simp]
theorem trace_transpose' (f : M →ₗ[R] M) :
    trace R _ (Module.Dual.transpose (R := R) f) = trace R M f := by
  rw [← comp_apply, trace_transpose]

theorem trace_tensorProduct' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M ⊗ N) (map f g) = trace R M f * trace R N g := by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_tensorProduct R M N) f) g
  simp only [compr₂_apply, mapBilinear_apply, compl₁₂_apply, lsmul_apply,
    Algebra.id.smul_eq_mul] at h
  exact h

theorem trace_comp_comm' (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g) := by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_comp_comm R M N) g) f
  simp only [llcomp_apply', compr₂_apply, flip_apply] at h
  exact h

end

variable {N P}

variable [Module.Free R N] [Module.Finite R N] [Module.Free R P] [Module.Finite R P] in
lemma trace_comp_cycle (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] M) :
    trace R P (g ∘ₗ f ∘ₗ h) = trace R N (f ∘ₗ h ∘ₗ g) := by
  rw [trace_comp_comm', comp_assoc]

variable [Module.Free R M] [Module.Finite R M] [Module.Free R P] [Module.Finite R P] in
lemma trace_comp_cycle' (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] M) :
    trace R P ((g ∘ₗ f) ∘ₗ h) = trace R M ((h ∘ₗ g) ∘ₗ f) := by
  rw [trace_comp_comm', ← comp_assoc]

@[simp]
theorem trace_conj' (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) : trace R N (e.conj f) = trace R M f := by
  classical
  by_cases hM : ∃ s : Finset M, Nonempty (Basis s R M)
  · obtain ⟨s, ⟨b⟩⟩ := hM
    haveI := Module.Finite.of_basis b
    haveI := (Module.free_def R M).mpr ⟨_, ⟨b⟩⟩
    haveI := Module.Finite.of_basis (b.map e)
    haveI := (Module.free_def R N).mpr ⟨_, ⟨(b.map e).reindex (e.toEquiv.image _)⟩⟩
    rw [e.conj_apply, trace_comp_comm', ← comp_assoc, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, id_comp]
  · rw [trace, trace, dif_neg hM, dif_neg ?_, zero_apply, zero_apply]
    rintro ⟨s, ⟨b⟩⟩
    exact hM ⟨s.image e.symm, ⟨(b.map e.symm).reindex
      ((e.symm.toEquiv.image s).trans (Equiv.setCongr Finset.coe_image.symm))⟩⟩

theorem IsProj.trace {p : Submodule R M} {f : M →ₗ[R] M} (h : IsProj p f) [Module.Free R p]
    [Module.Finite R p] [Module.Free R (ker f)] [Module.Finite R (ker f)] :
    trace R M f = (finrank R p : R) := by
  rw [h.eq_conj_prodMap, trace_conj', trace_prodMap', trace_id, map_zero, add_zero]

lemma isNilpotent_trace_of_isNilpotent {f : M →ₗ[R] M} (hf : IsNilpotent f) :
    IsNilpotent (trace R M f) := by
  by_cases H : ∃ s : Finset M, Nonempty (Basis s R M)
  swap
  · rw [LinearMap.trace, dif_neg H]
    exact IsNilpotent.zero
  obtain ⟨s, ⟨b⟩⟩ := H
  classical
  rw [trace_eq_matrix_trace R b]
  apply Matrix.isNilpotent_trace_of_isNilpotent
  simpa

lemma trace_comp_eq_mul_of_commute_of_isNilpotent [IsReduced R] {f g : Module.End R M}
    (μ : R) (h_comm : Commute f g) (hg : IsNilpotent (g - algebraMap R _ μ)) :
    trace R M (f ∘ₗ g) = μ * trace R M f := by
  set n := g - algebraMap R _ μ
  replace hg : trace R M (f ∘ₗ n) = 0 := by
    rw [← isNilpotent_iff_eq_zero, ← Module.End.mul_eq_comp]
    refine isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_right ?_ hg)
    exact h_comm.sub_right (Algebra.commute_algebraMap_right μ f)
  have hμ : g = algebraMap R _ μ + n := eq_add_of_sub_eq' rfl
  have : f ∘ₗ algebraMap R _ μ = μ • f := by ext; simp -- TODO Surely exists?
  rw [hμ, comp_add, map_add, hg, add_zero, this, LinearMap.map_smul, smul_eq_mul]

-- This result requires `Mathlib/RingTheory/TensorProduct/Free.lean`.
-- Maybe it should move elsewhere?
@[simp]
lemma trace_baseChange [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (A : Type*) [CommRing A] [Algebra R A] :
    trace A _ (f.baseChange A) = algebraMap R A (trace R _ f) := by
  let b := Module.Free.chooseBasis R M
  let b' := Algebra.TensorProduct.basis A b
  change _ = (algebraMap R A : R →+ A) _
  simp [b', trace_eq_matrix_trace R b, trace_eq_matrix_trace A b', AddMonoidHom.map_trace]

end

end LinearMap
