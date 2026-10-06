/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Trace of a linear map

This file defines the trace of an endomorphism of a finite projective module.
It is the contraction pairing under the canonical tensor-Hom equivalence.
For a finite free module it agrees with the matrix trace in any basis.

See also `Mathlib/LinearAlgebra/Matrix/Trace.lean` for the trace of a matrix.

## Tags

linear map, trace, diagonal
-/

@[expose] public section

noncomputable section

universe u v w

namespace LinearMap

open scoped Matrix
open Module TensorProduct

section Semiring

variable (R : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M]
variable {ι : Type w} [DecidableEq ι] [Fintype ι]
variable (b : Basis ι R M)
variable [Module.Finite R M] [Module.Projective R M]

/-- The trace of an endomorphism of a finite projective module, defined by the canonical
identification of endomorphisms with the tensor product of the dual and the module. -/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
  contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap

/-- The trace corresponds to contraction under the canonical tensor-Hom equivalence. -/
@[simp]
theorem trace_eq_contract : trace R M ∘ₗ dualTensorHom R M M = contractLeft R M := by
  ext x
  simp [trace]

@[simp]
theorem trace_eq_contract_apply (x : Module.Dual R M ⊗[R] M) :
    trace R M (dualTensorHom R M M x) = contractLeft R M x := by
  rw [← comp_apply, trace_eq_contract]

/-- The canonical definition of trace as contraction. -/
theorem trace_eq_contract' :
    trace R M = contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap := rfl

variable {M}

variable {R} in
@[simp]
lemma trace_smulRight (f : M →ₗ[R] R) (x : M) :
    trace R M (f.smulRight x) = f x := by
  exact trace_eq_contract_apply R M (f ⊗ₜ[R] x)

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  classical
  simp only [trace, ← dualTensorHomEquivOfBasis_eq_dualTensorHomEquiv b]
  simp [dualTensorHomEquivOfBasis, Matrix.trace, toMatrix_apply]

variable {R} in
@[simp] theorem _root_.Matrix.trace_toLin_eq (A : Matrix ι ι R) (b : Basis ι R M) :
    LinearMap.trace R _ (Matrix.toLin b b A) = A.trace := by
  simp [trace_eq_matrix_trace R b]

variable {R} in
@[simp] theorem _root_.Matrix.trace_toLin'_eq (A : Matrix ι ι R) :
    LinearMap.trace R _ A.toLin' = A.trace :=
  A.trace_toLin_eq (Pi.basisFun R ι)

theorem trace_mul_comm (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) := by
  induction f using LinearMap.inductionOn_smulRight with
  | add f h hf hh => simp_all [add_mul, mul_add]
  | smulRight φ m => simp [Module.End.mul_eq_comp]

lemma trace_mul_cycle (f g h : M →ₗ[R] M) :
    trace R M (f * g * h) = trace R M (h * f * g) := by
  rw [LinearMap.trace_mul_comm, ← mul_assoc]

lemma trace_mul_cycle' (f g h : M →ₗ[R] M) :
    trace R M (f * (g * h)) = trace R M (h * (f * g)) := by
  rw [← mul_assoc, LinearMap.trace_mul_comm]

lemma trace_lie_mul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (f g h : M →ₗ[R] M) : trace R M (⁅f, g⁆ * h) = trace R M (f * ⁅g, h⁆) := by
  simp only [Ring.lie_def, sub_mul, mul_sub, map_sub, mul_assoc]
  rw [trace_mul_comm R g (f * h), mul_assoc]

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
theorem trace_conj (g : M →ₗ[R] M) (f : (M →ₗ[R] M)ˣ) :
    trace R M (↑f * g * ↑f⁻¹) = trace R M g := by
  rw [trace_mul_comm]
  simp

@[simp]
lemma trace_lie {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f g : Module.End R M) :
    trace R M ⁅f, g⁆ = 0 := by
  rw [Ring.lie_def, map_sub, trace_mul_comm]
  exact sub_self _

end Semiring

section Ring

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]
variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
theorem trace_one [Module.Free R M] : trace R M 1 = (finrank R M : R) := by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b, toMatrix_one, finrank_eq_card_chooseBasisIndex]
  simp

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
theorem trace_id [Module.Free R M] : trace R M id = (finrank R M : R) := by
  rw [← Module.End.one_eq_id, trace_one]

@[simp]
theorem trace_transpose : trace R (Module.Dual R M) ∘ₗ Module.Dual.transpose = trace R M := by
  let e := dualTensorHomEquiv R M M
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f m; simp [e]

section TwoModules

variable (N)
variable [Module.Projective R N] [Module.Finite R N]

theorem trace_prodMap :
    trace R (M × N) ∘ₗ prodMapLinear R M N M N R =
      (coprod id id : R × R →ₗ[R] R) ∘ₗ prodMap (trace R M) (trace R N) := by
  let e := (dualTensorHomEquiv R M M).prodCongr (dualTensorHomEquiv R N N)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext <;> simp [e]

variable {R M N} in
theorem trace_prodMap' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M × N) (prodMap f g) = trace R M f + trace R N g := by
  exact congrArg (fun t => t (f, g)) (trace_prodMap R M N)

open Function

theorem trace_tensorProduct : compr₂ (mapBilinear (.id R) M N M N) (trace R (M ⊗ N)) =
    compl₁₂ (lsmul R R : R →ₗ[R] R →ₗ[R] R) (trace R M) (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R M M) from (dualTensorHomEquiv R M M).surjective)
        (show Surjective (dualTensorHom R N N) from (dualTensorHomEquiv R N N).surjective)).1
  ext f m g n
  simp [map_dualTensorHom]

theorem trace_comp_comm :
    compr₂ (llcomp R M N M) (trace R M) = compr₂ (llcomp R N M N).flip (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R N M) from (dualTensorHomEquiv R N M).surjective)
        (show Surjective (dualTensorHom R M N) from (dualTensorHomEquiv R M N).surjective)).1
  ext g m f n
  simp [llcomp_apply', comp_dualTensorHom, mul_comm]

variable {R M N}

@[simp]
theorem trace_transpose' (f : M →ₗ[R] M) :
    trace R _ (Module.Dual.transpose (R := R) f) = trace R M f := by
  rw [← comp_apply, trace_transpose]

theorem trace_tensorProduct' (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    trace R (M ⊗ N) (map f g) = trace R M f * trace R N g := by
  exact congrArg (fun t => t f g) (trace_tensorProduct R M N)

theorem trace_comp_comm' (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g) := by
  exact congrArg (fun t => t g f) (trace_comp_comm R M N)

end TwoModules

variable {R M}

/-- If an endomorphism of a finite projective module takes values in a finite projective
submodule, then its restriction has the same trace. -/
lemma trace_restrict_eq_of_forall_mem (p : Submodule R M)
    [Module.Finite R p] [Module.Projective R p] (f : M →ₗ[R] M)
    (hf : ∀ x, f x ∈ p) (hf' : ∀ x ∈ p, f x ∈ p := fun x _ ↦ hf x) :
    trace R p (f.restrict hf') = trace R M f := by
  exact trace_comp_comm' p.subtype (f.codRestrict p hf)

omit [Module.Finite R M] [Module.Projective R M] in
variable [Module.Projective R N] [Module.Finite R N] [Module.Projective R P] [Module.Finite R P] in
lemma trace_comp_cycle (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] M) :
    trace R P (g ∘ₗ f ∘ₗ h) = trace R N (f ∘ₗ h ∘ₗ g) := by
  rw [trace_comp_comm', comp_assoc]

variable [Module.Projective R P] [Module.Finite R P] in
lemma trace_comp_cycle' (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] M) :
    trace R P ((g ∘ₗ f) ∘ₗ h) = trace R M ((h ∘ₗ g) ∘ₗ f) := by
  rw [trace_comp_comm', ← comp_assoc]

@[simp]
theorem trace_conj' [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) : trace R N (e.conj f) = trace R M f := by
  rw [e.conj_apply, trace_comp_comm', ← comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, id_comp]

@[simp] theorem trace_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [Module.Finite K V] [Module.Finite K W] {F : Type*}
    [EquivLike F (End K V) (End K W)] [AlgEquivClass F K _ _]
    (f : F) (x : End K V) : (f x).trace K W = x.trace K V :=
  have ⟨_, h⟩ := (AlgEquiv.ofClass f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ trace_conj' _ _

@[simp] theorem _root_.Matrix.trace_map {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {F : Type*} [EquivLike F (Matrix m m K) (Matrix n n K)]
    [AlgEquivClass F K _ _] (f : F) (x : Matrix m m K) : (f x).trace = x.trace := by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.trace_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquiv.ofClass f)).trans Matrix.toLinAlgEquiv') x.toLin'

@[simp] theorem _root_.Matrix.trace_map' {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
    [FunLike F (Matrix m m K) (Matrix m m K)] [AlgHomClass F K _ _] (f : F) (x : Matrix m m K) :
    (f x).trace = x.trace := by
  by_cases! Nonempty m
  · exact Matrix.trace_map (AlgEquiv.ofBijective _ (AlgHom.ofClass f).bijective) x
  · simp

theorem IsProj.trace {p : Submodule R M} {f : M →ₗ[R] M} (h : IsProj p f) [Module.Free R p]
    [Module.Finite R p] [Module.Projective R (ker f)] [Module.Finite R (ker f)] :
    trace R M f = (finrank R p : R) := by
  rw [h.eq_conj_prodMap, trace_conj', trace_prodMap', trace_id, map_zero, add_zero]

open LinearMap in
/-- An idempotent endomorphism of a module over a characteristic-zero commutative ring
with vanishing trace is the zero map, provided its range is finite free and its kernel
is finite projective.

The freeness, projectivity and finiteness instance arguments on `range e` and `ker e` are
automatic over a field, and more generally over any principal ideal domain `R` for which
`M` itself is finite and free (submodules of finite free modules over a PID are finite
and free). -/
theorem IsIdempotentElem.trace_eq_zero_iff {R : Type*} [CommRing R] [CharZero R]
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    {e : M →ₗ[R] M} (he : IsIdempotentElem e)
    [Module.Free R (range e)] [Module.Finite R (range e)]
    [Module.Projective R (ker e)] [Module.Finite R (ker e)] :
    trace R M e = 0 ↔ e = 0 := by
  rw [he.isProj_range.trace, Nat.cast_eq_zero, finrank_eq_zero_iff_of_free,
    Submodule.subsingleton_iff_eq_bot, range_eq_bot]

alias ⟨IsIdempotentElem.eq_zero_of_trace_eq_zero, _⟩ := IsIdempotentElem.trace_eq_zero_iff

lemma isNilpotent_trace_of_isNilpotent {f : M →ₗ[R] M} (hf : IsNilpotent f) :
    IsNilpotent (trace R M f) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hpow (k : ℕ) : (i ∘ₗ f ∘ₗ p) ^ (k + 1) = i ∘ₗ (f ^ (k + 1)) ∘ₗ p := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ _ (k + 1), ih, pow_succ f (k + 1)]
      simp only [Module.End.mul_eq_comp, comp_assoc]
      rw [← comp_assoc (f ∘ₗ p) i p, hpi, id_comp]
  have hf' : IsNilpotent (i ∘ₗ f ∘ₗ p) := by
    obtain ⟨k, hk⟩ := hf
    refine ⟨k + 1, ?_⟩
    rw [hpow, pow_succ, hk, zero_mul, zero_comp, comp_zero]
  have ht : trace R (Fin n → R) (i ∘ₗ f ∘ₗ p) = trace R M f := by
    rw [trace_comp_comm', comp_assoc, hpi, comp_id]
  rw [← ht, trace_eq_matrix_trace R (Pi.basisFun R (Fin n))]
  apply Matrix.isNilpotent_trace_of_isNilpotent
  exact hf'.map (LinearMap.toMatrixAlgEquiv (Pi.basisFun R (Fin n)))

lemma trace_comp_eq_mul_of_commute_of_isNilpotent [IsReduced R] {f g : Module.End R M}
    (μ : R) (h_comm : Commute f g) (hg : IsNilpotent (g - algebraMap R _ μ)) :
    trace R M (f ∘ₗ g) = μ * trace R M f := by
  set n := g - algebraMap R _ μ
  replace hg : trace R M (f ∘ₗ n) = 0 := by
    rw [← isNilpotent_iff_eq_zero, ← Module.End.mul_eq_comp]
    refine isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_left ?_ hg)
    exact h_comm.sub_right (Algebra.commute_algebraMap_right μ f)
  have hμ : g = algebraMap R _ μ + n := eq_add_of_sub_eq' rfl
  have : f ∘ₗ algebraMap R _ μ = μ • f := by ext; simp -- TODO Surely exists?
  rw [hμ, comp_add, map_add, hg, add_zero, this, map_smul, smul_eq_mul]

/-- Trace commutes with arbitrary extension of scalars for finite projective modules. -/
@[simp]
lemma trace_baseChange (f : M →ₗ[R] M) (A : Type*) [CommRing A] [Algebra R A] :
    trace A _ (f.baseChange A) = algebraMap R A (trace R _ f) := by
  induction f using LinearMap.inductionOn_smulRight with
  | add f g hf hg => simp_all
  | smulRight φ m =>
    let φ' : A ⊗[R] M →ₗ[A] A := (AlgebraTensorModule.rid R A A).toLinearMap ∘ₗ φ.baseChange A
    have h : (φ.smulRight m).baseChange A = φ'.smulRight (1 ⊗ₜ[R] m) := by
      ext x; simp [φ']
    rw [h, trace_smulRight]
    simp [φ', Algebra.algebraMap_eq_smul_one]

end Ring

end LinearMap

/-- If `S` is an `R`-algebra that is free of rank `1` over `R`, the map `R →+* S` is an
isomorphism. -/
lemma Module.Free.bijective_algebraMap_of_finrank_eq_one {R S : Type*} [CommRing R] [Ring S]
    [Algebra R S] [Nontrivial R] [Free R S] (h : finrank R S = 1) :
    Function.Bijective (algebraMap R S) := by
  exact bijective_algebraMap_of_linearEquiv
    (Module.nonempty_linearEquiv_of_finrank_eq_one h).some
