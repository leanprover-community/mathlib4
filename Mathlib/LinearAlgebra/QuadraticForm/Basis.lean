/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Sym.Sym2

/-!
# Constructing a bilinear map from a quadratic map, given a basis

This file provides an alternative to `QuadraticMap.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

open LinearMap (BilinMap)

namespace QuadraticMap

section

variable {α R}

/--
`CommMagma.mul` as a function from `Sym2`.
-/
def Sym2.mul [CommMagma R] (f : α → R) : Sym2 α → R :=
  Sym2.lift ⟨fun i j => (f i * f j), fun _ _ => mul_comm _ _⟩

@[simp]
lemma Sym2.mul_sym2Mk [CommMagma R] (f : α → R) (xy : α × α) :
    mul f (.mk xy) = f xy.1 * f xy.2 := rfl

end


section

variable {ι R M N}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Finsupp in
theorem map_finsuppSum' (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) =
      ∑ p ∈ f.support.sym2, (((polarSym2 Q) ∘ Sym2.map (fun i => (g i (f i)))) p)
        - ∑ i ∈ f.support, Q (g i (f i)) := by
  exact Q.map_sum' _ (fun i => g i (f i))

lemma partial_result1 (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R) :
    (polarSym2 Q) ∘ Sym2.map (l * g) = Sym2.lift ⟨fun i j => l j • l i • polar (⇑Q) (g i) (g j),
      fun _ _ => by simp_rw [polar_comm]; rw [smul_comm]⟩ := by
  rw [polarSym2, Sym2.lift_comp_map]
  simp_all only [Finset.product_eq_sprod]
  ext ⟨i,j⟩
  simp_all only [Sym2.lift_mk]
  have e1 (k : ι): (l * g) k = (l k) • (g k) := rfl
  rw [e1, e1]
  simp_rw [polar_smul_right, polar_smul_left]

lemma partial_result2a (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R) :
    Sym2.lift ⟨fun i j => l j • l i • polar (⇑Q) (g i) (g j),
      fun _ _ => by simp_rw [polar_comm]; rw [smul_comm]⟩ =
      Sym2.mul l • (polarSym2 Q) ∘ Sym2.map g := by
  ext ⟨i,j⟩
  simp_all only [Sym2.lift_mk, Pi.smul_apply']
  rw [← smul_assoc]
  simp only [smul_eq_mul, Pi.smul_apply', Sym2.lift_mk, Sym2.mul, Function.comp_apply,
    Sym2.map_pair_eq, polarSym2_sym2Mk, mul_comm]

variable [DecidableEq ι]

/--
Lift `i j => (l i * l j)` to `Sym2 ι`
-/
noncomputable def scalar (l : ι →₀ R) : Sym2 ι →₀ R := Finsupp.onFinset
    ((l.support.product l.support).image Sym2.mk)
    (Sym2.mul l) (fun p hp => by
      simp only [Finset.product_eq_sprod, Finset.mem_image, Finset.mem_product,
        Finsupp.mem_support_iff, ne_eq, Prod.exists]
      simp only [ne_eq] at hp
      obtain ⟨a,b⟩ := p
      simp only [Sym2.mul_sym2Mk] at hp
      use a
      use b
      constructor
      · aesop
      · aesop
    )

lemma partial_result3a (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R) :
    Sym2.mul l • (polarSym2 Q) ∘ Sym2.map g =
        scalar l * (polarSym2 Q) ∘ Sym2.map g := by
  rw [polarSym2]
  rw [Sym2.lift_comp_map]
  rw [scalar]
  simp_all only [Finset.product_eq_sprod]
  simp_rw [Finsupp.pointwiseModuleScalar]
  simp_all only [Finsupp.onFinset_apply]
  ext ⟨i,j⟩
  simp_all only [smul_eq_mul, Pi.smul_apply', Sym2.lift_mk]
  rw [Finsupp.ofSupportFinite]
  simp_all only [Finsupp.coe_mk, Sym2.lift_mk]

lemma test (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R) :
    (polarSym2 Q) ∘ Sym2.map (l * g)  = (scalar l) * (polarSym2 Q) ∘ (Sym2.map g) := by
  rw [partial_result1, partial_result2a, partial_result3a]

open Finsupp in
theorem apply_linearCombination' (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) =
      linearCombination R ((polarSym2 Q) ∘ Sym2.map g) (scalar l) -
      linearCombination R (Q ∘ g) (l * l)  := by
  simp_rw [linearCombination_apply, map_finsuppSum',
    map_smul, mul_smul]
  rw [Finsupp.sum_of_support_subset (l * l)
    (subset_trans Finsupp.support_mul (by rw [Finset.inter_self])) (fun i a => a • (⇑Q ∘ g) i)
    (fun _ _=> by simp only [Function.comp_apply, zero_smul])]
  simp only [Finset.inter_self, mul_apply, Function.comp_apply]
  simp only [←smul_eq_mul, smul_assoc]
  simp_all only [sub_left_inj]
  have e2 (p : Sym2 ι) :
      (scalar l * (polarSym2 Q) ∘ Sym2.map g) p = (scalar l) p • (polarSym2 Q) (Sym2.map g p) :=
    rfl
  have e3 : (scalar l).support ⊆  l.support.sym2 := by
    intro p hp
    simp [scalar] at hp
    obtain ⟨j,k⟩ := p
    simp
    by_contra H
    simp at H
    have c1 : l j * l k = 0 := by
      rcases eq_or_ne (l j) 0 with hz | hz
      · exact mul_eq_zero_of_left hz (l k)
      · exact mul_eq_zero_of_right _ (H hz)
    simp_all only [Sym2.mul_sym2Mk, not_true_eq_false]
  rw [Finsupp.sum_of_support_subset (scalar l) e3]
  · have d1 (x : Sym2 ι) :
    (polarSym2 Q) (Sym2.map (fun i ↦ l i • g i) x) =
      (scalar l) x • (polarSym2 Q) (Sym2.map g x) := by
      rw [← e2]
      rw [← test]
      rfl
    simp_rw [d1]
  intro p hp
  exact zero_smul R ((polarSym2 Q) (Sym2.map g p))

open Finsupp in
theorem sum_polar_sub_repr_sq (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R ((polarSym2 Q) ∘ Sym2.map bm) (scalar (bm.repr x)) -
      linearCombination R (Q ∘ bm) ((bm.repr x) * (bm.repr x)) = Q x := by
  rw [← apply_linearCombination', Basis.linearCombination_repr]

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
      ∑ p ∈ l.support.sym2 with ¬ p.IsDiag, ((scalar l) * ((polarSym2 Q) ∘ Sym2.map g)) p := by
  simp_rw [linearCombination_apply, map_finsuppSum,
    map_smul, mul_smul]
  rw [Finsupp.sum_of_support_subset (l * l)
    (subset_trans Finsupp.support_mul (by rw [Finset.inter_self])) (fun i a => a • (⇑Q ∘ g) i)
    (fun _ _=> by simp only [Function.comp_apply, zero_smul])]
  simp only [Finset.inter_self, mul_apply, Function.comp_apply]
  simp only [←smul_eq_mul, smul_assoc]
  have e1 : (l.sum fun i r ↦ r • r • Q (g i))  = ∑ x ∈ l.support, l x • l x • Q (g x) := rfl
  rw [e1]
  simp_rw [add_right_inj]
  simp_rw [← test]
  simp_all only [Function.comp_apply]
  rfl

-- c.f. `LinearMap.sum_repr_mul_repr_mul`
open Finsupp in
theorem sum_repr_sq_add_sum_repr_mul_polar (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (Q ∘ bm) ((bm.repr x) * (bm.repr x)) +
      ∑ p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag,
        ((scalar (bm.repr x)) * ((polarSym2 Q) ∘ Sym2.map bm)) p = Q x := by
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
