/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.LinearAlgebra.Finsupp.Sym2


/-!
# Constructing a bilinear map from a quadratic map, given a basis

This file provides an alternative to `QuadraticMap.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

open LinearMap (BilinMap)

section

variable {ι R M} [Semiring R] [AddCommMonoid M] [Module R M]

/--
Define the multiplication of a scalar-valued, finitely supported, function with a module-valued
function as a finitely supported module-valued function.
-/
noncomputable def Finsupp.hMul (f : ι →₀ R) (g : ι → M) : (ι →₀ M) :=
    Finsupp.ofSupportFinite (fun a ↦ f a • g a) (by
      apply Set.Finite.subset f.finite_support
      simp only [Function.support_subset_iff, Finsupp.mem_support_iff, Ne,
        Finsupp.fun_support_eq, Finset.mem_coe]
      intro x hx h
      apply hx
      rw [h, zero_smul])

@[simp]
lemma Finsupp.coe_pointwise_module_smul (f : ι →₀ R) (g : ι → M) (a : ι) :
    (Finsupp.hMul f g) a = f a • g a := rfl

end

namespace QuadraticMap

section

variable {ι R M N}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Finsupp in
theorem map_finsuppSum' (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) =
      ∑ p ∈ f.support.sym2, (((polarSym2 Q) ∘ Sym2.map (fun i => (g i (f i)))) p)
        - ∑ i ∈ f.support, Q (g i (f i)) := by
  exact Q.map_sum' _ (fun i => g i (f i))

lemma polarSym2_map_mul (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R) :
    (polarSym2 Q) ∘ Sym2.map (Finsupp.hMul l g) = Sym2.mul l • (polarSym2 Q) ∘ Sym2.map g := by
  ext ⟨_,_⟩
  simp_all only [Function.comp_apply, Finsupp.coe_pointwise_module_smul, Sym2.map_pair_eq,
    polarSym2_sym2Mk, polar_smul_right, polar_smul_left, Pi.smul_apply', Sym2.mul_sym2Mk, mul_comm,
    ← smul_assoc, smul_eq_mul]

open Finsupp in
lemma test2 (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R) (p : Sym2 ι) :
    (polarSym2 Q) (p.map (hMul l g))
      = (Sym2.mul_finsupp l) p • ((polarSym2 Q) (p.map g)) := by
  obtain ⟨a,b⟩ := p
  rw [Sym2.mul_finsupp]
  simp only [coe_pointwise_module_smul, Sym2.map_pair_eq, polarSym2_sym2Mk, polar_smul_right,
    polar_smul_left, onFinset_apply, Sym2.mul_sym2Mk]
  rw [← smul_assoc, smul_eq_mul, mul_comm]

open Finsupp in
lemma test (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R) :
    (polarSym2 Q) ∘ Sym2.map (hMul l g)
      = hMul (Sym2.mul_finsupp l) ((polarSym2 Q) ∘ (Sym2.map g)) := by
  rw [polarSym2_map_mul, polarSym2]
  ext ⟨a,b⟩
  simp_all only [Pi.smul_apply', Sym2.mul_sym2Mk, Function.comp_apply, Sym2.map_pair_eq,
    Sym2.lift_mk]
  rfl


open Finsupp in
theorem apply_linearCombination' (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) =
      linearCombination R ((polarSym2 Q) ∘ Sym2.map g) (Sym2.mul_finsupp l) -
      linearCombination R (Q ∘ g) (l * l)  := by
  simp_rw [linearCombination_apply, map_finsuppSum', map_smul, mul_smul]
  rw [Finsupp.sum_of_support_subset (l * l) (support_mul_self l) (fun i a => a • (⇑Q ∘ g) i)
    (fun _ _=> by simp only [Function.comp_apply, zero_smul])]
  simp only [mul_apply, Function.comp_apply]
  simp only [←smul_eq_mul, smul_assoc]
  simp_all only [sub_left_inj]
  rw [Finsupp.sum_of_support_subset (Sym2.mul_finsupp l) (Sym2.mul_finsupp_support l) _
    (fun p hp => zero_smul R ((polarSym2 Q) (Sym2.map g p)))]
  apply Finset.sum_congr rfl
  intro p _
  rw [← test2]
  rfl

open Finsupp in
theorem sum_polar_sub_repr_sq (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R ((polarSym2 Q) ∘ Sym2.map bm) (Sym2.mul_finsupp (bm.repr x)) -
      linearCombination R (Q ∘ bm) ((bm.repr x) * (bm.repr x)) = Q x := by
  rw [← apply_linearCombination', Basis.linearCombination_repr]

variable [DecidableEq ι]

-- c.f. `_root_.map_finsupp_sum`
open Finsupp in
theorem map_finsuppSum (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) =
      f.sum (fun i r => Q (g i r)) +
      ∑ p ∈ f.support.sym2 with ¬ p.IsDiag,
        ((polarSym2 Q) ∘ Sym2.map (fun i => (g i (f i)))) p := by
  exact Q.map_sum _ _

-- c.f. `Finsupp.apply_linearCombination`
open Finsupp in
theorem apply_linearCombination (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) = linearCombination R (Q ∘ g) (l * l) +
      ∑ p ∈ l.support.sym2 with ¬ p.IsDiag,
        (hMul (Sym2.mul_finsupp l) ((polarSym2 Q) ∘ Sym2.map g)) p := by
  simp_rw [linearCombination_apply, map_finsuppSum, map_smul, mul_smul]
  rw [Finsupp.sum_of_support_subset (l * l) (support_mul_self l) (fun i a => a • (⇑Q ∘ g) i)
    (fun _ _=> by simp only [Function.comp_apply, zero_smul])]
  simp only [mul_apply, Function.comp_apply]
  simp only [←smul_eq_mul, smul_assoc]
  rw [Finsupp.sum]
  simp_rw [add_right_inj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← test]
  simp only [Function.comp_apply, coe_pointwise_module_smul]

-- c.f. `LinearMap.sum_repr_mul_repr_mul`
open Finsupp in
theorem sum_repr_sq_add_sum_repr_mul_polar (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (Q ∘ bm) ((bm.repr x) * (bm.repr x)) +
      ∑ p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag,
        (hMul (Sym2.mul_finsupp (bm.repr x)) ((polarSym2 Q) ∘ Sym2.map bm)) p = Q x := by
  rw [← apply_linearCombination, Basis.linearCombination_repr]

end

variable {ι R M N}  [LinearOrder ι]
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- Given an ordered basis, produce a bilinear form associated with the quadratic form.

Unlike `QuadraticMap.associated`, this is not symmetric; however, as a result it can be used even
in characteristic two. When considered as a matrix, the form is triangular. -/
noncomputable def toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) : LinearMap.BilinMap R M N :=
  bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

theorem toBilin_apply (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) :
    Q.toBilin bm (bm i) (bm j) =
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0 := by
  simp [toBilin]

theorem toQuadraticMap_toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm).toQuadraticMap = Q := by
  ext x
  rw [← bm.linearCombination_repr x, LinearMap.BilinMap.toQuadraticMap_apply,
      Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, if_true]
  rw [Finset.sum_ite_of_false, QuadraticMap.map_sum, ← Finset.sum_filter]
  · simp_rw [← polar_smul_right _ (bm.repr x <| Prod.snd _),
      ← polar_smul_left _ (bm.repr x <| Prod.fst _)]
    simp_rw [QuadraticMap.map_smul, mul_smul, Finset.sum_sym2_filter_not_isDiag]
    rfl
  · intro x hx
    rw [Finset.mem_offDiag] at hx
    simpa using hx.2.2

/-- From a free module, every quadratic map can be built from a bilinear form.

See `BilinMap.not_forall_toQuadraticMap_surjective` for a counterexample when the module is
not free. -/
theorem _root_.LinearMap.BilinMap.toQuadraticMap_surjective [Module.Free R M] :
    Function.Surjective (LinearMap.BilinMap.toQuadraticMap : LinearMap.BilinMap R M N → _) := by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticMap_toBilin _ b⟩

@[simp]
lemma add_toBilin (bm : Basis ι R M) (Q₁ Q₂ : QuadraticMap R M N) :
    (Q₁ + Q₂).toBilin bm = Q₁.toBilin bm + Q₂.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_add]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_lt, toBilin_apply, polar_add]

variable (S) [CommSemiring S] [Algebra S R]
variable [Module S N] [IsScalarTower S R N]

@[simp]
lemma smul_toBilin (bm : Basis ι R M) (s : S) (Q : QuadraticMap R M N) :
    (s • Q).toBilin bm = s • Q.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_smul]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_lt, toBilin_apply]

/-- `QuadraticMap.toBilin` as an S-linear map -/
@[simps]
noncomputable def toBilinHom (bm : Basis ι R M) : QuadraticMap R M N →ₗ[S] BilinMap R M N where
  toFun Q := Q.toBilin bm
  map_add' := add_toBilin bm
  map_smul' := smul_toBilin S bm

end QuadraticMap
