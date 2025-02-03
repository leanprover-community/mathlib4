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

variable {ι R M N}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/--
Lift the polar
-/
def polar_sym2 (Q : QuadraticMap R M N) : Sym2 M → N :=
  Sym2.lift ⟨fun m₁ m₂ => (polar Q) m₁ m₂, fun i j => by simp only [polar_comm]⟩

/--
Lift the polar
-/
def polar_lift {ι} (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) : Sym2 ι → N :=
  Q.polar_sym2 ∘ Sym2.map (fun i => (g i (f i)))

lemma recover {ι} (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q.polar_lift f g = Sym2.lift ⟨fun i j => (polar Q) (g i (f i)) (g j (f j)),
      fun i j => by simp only [polar_comm]⟩ := (Equiv.symm_apply_eq Sym2.lift).mp rfl

open Finsupp in
theorem map_finsuppSum' (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) =
      ∑ p ∈ f.support.sym2, (Q.polar_lift f g p) - ∑ i ∈ f.support, Q (g i (f i)) := by
  rw [recover]
  exact Q.map_sum' _ (fun i => g i (f i))

variable [DecidableEq ι]

/--
Lift `i j => (l i * l j)` to `Sym2 ι`
-/
noncomputable def scalar (l : ι →₀ R) : Sym2 ι →₀ R := Finsupp.onFinset
    ((l.support.product l.support).image Sym2.mk)
    (Sym2.lift ⟨fun i j => (l i * l j), fun _ _ => mul_comm _ _⟩) (fun p hp => by
      simp only [Finset.product_eq_sprod, Finset.mem_image, Finset.mem_product,
        Finsupp.mem_support_iff, ne_eq, Prod.exists]
      simp only [ne_eq] at hp
      obtain ⟨a,b⟩ := p
      simp only [Sym2.lift_mk] at hp
      use a
      use b
      constructor
      · aesop
      · aesop
    )


variable (Q : QuadraticMap R M N) (g : ι → M) (l : ι →₀ R)

/-
lemma test (p : Sym2 ι) :
    Q.polar_sym2 (Sym2.map (fun i ↦ l i • g i) p) = (scalar l p) • Q.polar_sym2 (Sym2.map g p) := by
  rw [scalar]
  simp_all only [Finset.product_eq_sprod, Finsupp.onFinset_apply]
  rw [polar_sym2]
  rw [← Sym2.lift_comp_map_apply]
  rw [← Sym2.lift_comp_map_apply]
  simp_all only [polar_smul_right, polar_smul_left]
  sorry


lemma recover2 : Finsupp.linearCombination R (Q.polar_sym2 ∘ Sym2.map g) (scalar l) =
    ∑ p ∈ l.support.sym2,
        p.lift
          ⟨fun i j => (l i * l j) • polar Q (g i) (g j), fun i j => by
            simp only [polar_comm, mul_comm]⟩ := by
  simp_rw [Finsupp.linearCombination_apply]
  simp_rw [scalar]
  simp_all only [Finset.product_eq_sprod, Function.comp_apply]
  sorry

open Finsupp in
theorem apply_linearCombination' (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) =
      linearCombination R (Q.polar_sym2 ∘ Sym2.map g) (scalar l) -
      linearCombination R (Q ∘ g) (l * l)  := by
  simp_rw [linearCombination_apply, map_finsuppSum',
    map_smul, mul_smul]
  rw [Finsupp.sum_of_support_subset (l * l)
    (subset_trans Finsupp.support_mul (by rw [Finset.inter_self])) (fun i a => a • (⇑Q ∘ g) i)
    (fun _ _=> by simp only [Function.comp_apply, zero_smul])]
  simp only [Finset.inter_self, mul_apply, Function.comp_apply]
  simp only [←smul_eq_mul, smul_assoc]
  simp_all only [sub_left_inj]
  rw [polar_lift]
  simp_all only [Function.comp_apply]
  simp_rw [test]
  sorry



open Finsupp in
theorem sum_polar_sub_repr_sq (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
      ∑ p ∈ (bm.repr x).support.sym2,
        p.lift
          ⟨fun i j => (bm.repr x i * bm.repr x j) • polar Q (bm i) (bm j), fun i j => by
            simp only [polar_comm, mul_comm]⟩ -
        linearCombination R (Q ∘ bm) ((bm.repr x) * (bm.repr x)) = Q x := by
  rw [← apply_linearCombination', Basis.linearCombination_repr]
-/


-- c.f. `_root_.map_finsupp_sum`
open Finsupp in
theorem map_finsuppSum (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) =
      f.sum (fun i r => Q (g i r)) + ∑ p ∈ f.support.sym2 with ¬ p.IsDiag, Q.polar_lift f g p := by
  rw [recover]
  exact Q.map_sum _ _

-- c.f. `Finsupp.apply_linearCombination`
open Finsupp in
theorem apply_linearCombination (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) = linearCombination R (Q ∘ g) (l * l) +
      ∑ p ∈ l.support.sym2 with ¬ p.IsDiag,
        p.lift
          ⟨fun i j => (l i * l j) • polar Q (g i) (g j), fun i j => by
            simp only [polar_comm, mul_comm]⟩ := by
  simp_rw [linearCombination_apply, map_finsuppSum, recover, polar_smul_left, polar_smul_right,
    map_smul, mul_smul, add_left_inj]
  rw [Finsupp.sum, Finsupp.sum_of_support_subset (l * l)
    (subset_trans Finsupp.support_mul (by rw [Finset.inter_self])) (fun i a => a • (⇑Q ∘ g) i)
    (fun _ _=> by simp only [Function.comp_apply, zero_smul])]
  simp only [Finset.inter_self, mul_apply, Function.comp_apply]
  simp only [←smul_eq_mul, smul_assoc]

-- c.f. `LinearMap.sum_repr_mul_repr_mul`
open Finsupp in
theorem sum_repr_sq_add_sum_repr_mul_polar (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (Q ∘ bm) ((bm.repr x) * (bm.repr x)) +
      ∑ p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag,
        p.lift
          ⟨fun i j => (bm.repr x i * bm.repr x j) • polar Q (bm i) (bm j), fun i j => by
            simp only [polar_comm, mul_comm]⟩ = Q x := by
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
