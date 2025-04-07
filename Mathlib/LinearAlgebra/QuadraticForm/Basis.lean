/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Sym.Sym2.Finsupp
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.Data.Sym.Sym2.Prod

/-!
# Constructing a bilinear map from a quadratic map, given a basis

This file provides an alternative to `QuadraticMap.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

open LinearMap (BilinMap)

namespace QuadraticMap
variable {ι R M N : Type*}

section Finsupp
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Finsupp

theorem map_finsuppSum' (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) =
      ∑ p ∈ f.support.sym2, polarSym2 Q (p.map fun i ↦ g i (f i)) - f.sum fun i a ↦ Q (g i a) :=
  Q.map_sum' ..

theorem apply_linearCombination' (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) =
      linearCombination R (polarSym2 Q ∘ Sym2.map g) l.sym2Mul -
        linearCombination R (Q ∘ g) (l * l) := by
  simp_rw [linearCombination_apply, map_finsuppSum', Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp,
    l.sym2Mul.sum_of_support_subset support_sym2Mul_subset _ <| by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

theorem sum_polar_sub_repr_sq (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (polarSym2 Q ∘ Sym2.map bm) (bm.repr x).sym2Mul -
      linearCombination R (Q ∘ bm) (bm.repr x * bm.repr x) = Q x := by
  rw [← apply_linearCombination', Basis.linearCombination_repr]

variable [DecidableEq ι]

/-- The quadratic version of `_root_.map_finsupp_sum`. -/
theorem map_finsuppSum (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) = f.sum (fun i r ↦ Q (g i r)) +
      ∑ p ∈ f.support.sym2 with ¬ p.IsDiag, polarSym2 Q (p.map fun i ↦ g i (f i)) := Q.map_sum _ _

/-- The quadratic version of `Finsupp.apply_linearCombination`. -/
theorem apply_linearCombination (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) = linearCombination R (Q ∘ g) (l * l) +
      ∑ p ∈ l.support.sym2 with ¬ p.IsDiag, (p.map l).mul • polarSym2 Q (p.map g) := by
  simp_rw [linearCombination_apply, map_finsuppSum, Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

/-- The quadratic version of `LinearMap.sum_repr_mul_repr_mul`. -/
theorem sum_repr_sq_add_sum_repr_mul_polar (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (Q ∘ bm) (bm.repr x * bm.repr x) +
      ∑ p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag,
        Sym2.mul (p.map (bm.repr x)) • polarSym2 Q (p.map bm) = Q x := by
  rw [← apply_linearCombination, Basis.linearCombination_repr]

end Finsupp

variable [LinearOrder ι]
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
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, map_smul, toBilin_apply,
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

lemma toBilin_symm_eq_Polar (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm) + (Q.toBilin bm).flip = polarBilin Q := by
  ext a b
  conv_rhs => rw [← toQuadraticMap_toBilin Q bm]
  simp only [toQuadraticMap_toBilin]
  symm
  calc Q (a + b) - Q a - Q b = (Q.toBilin bm).toQuadraticMap (a + b) - Q a - Q b := by
        rw [ toQuadraticMap_toBilin Q]
  _ = (((Q.toBilin bm) a a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a - Q b := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, map_add, map_add, LinearMap.add_apply]
  _ = (((Q.toBilin bm).toQuadraticMap a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a
    - Q b := by rw [LinearMap.BilinMap.toQuadraticMap_apply]
  _ = ((Q a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a - Q b := by
    rw [ toQuadraticMap_toBilin Q]
  _ = ((Q a + (Q.toBilin bm) b a) + ((Q.toBilin bm) a b + (Q.toBilin bm).toQuadraticMap b)) - Q a
    - Q b := by rw [map_add, LinearMap.add_apply,
      LinearMap.BilinMap.toQuadraticMap_apply (Q.toBilin bm) b]
  _ = ((Q a + (Q.toBilin bm) b a) + ((Q.toBilin bm) a b + Q b)) - Q a - Q b := by
    rw [ toQuadraticMap_toBilin Q]
  _ = ((Q.toBilin bm) a) b + ((Q.toBilin bm) b) a := by abel

lemma polar_toQuadraticMap (B : BilinMap R M N) (x y : M) :
    polar B.toQuadraticMap x y = B x y + B y x := by
  simp only [polar, BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply]
  abel

lemma below_diag (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) (h : j < i) :
  (Q.toBilin bm) (bm i) (bm j) = 0 := by
  simp [QuadraticMap.toBilin]
  have p1 : ¬ (i = j) := by exact ne_of_gt h
  have p2: ¬ (i < j) := by exact not_lt_of_gt h
  simp_all only [not_lt, ↓reduceIte, ite_eq_right_iff, isEmpty_Prop, IsEmpty.forall_iff]

lemma above_diag (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) (h : i < j) :
  (Q.toBilin bm) (bm i) (bm j) = (polar Q) (bm i) (bm j) := by
  simp [QuadraticMap.toBilin]
  have p1 : ¬ (i = j) := by exact ne_of_lt h
  simp_all only [↓reduceIte]

lemma on_diag (Q : QuadraticMap R M N) (bm : Basis ι R M) (i : ι) :
    2 • (Q.toBilin bm) (bm i) (bm i) = (polar Q) (bm i) (bm i) := by
  simp [QuadraticMap.toBilin]

lemma polarBilin_toQuadraticMap (B : BilinMap R M N) :
    polarBilin B.toQuadraticMap = B + B.flip := by
  ext x y
  simp only [polarBilin_apply_apply, polar_toQuadraticMap, LinearMap.add_apply,
    LinearMap.flip_apply]

theorem toBilin_toQuadraticMap (B : BilinMap R M N) (bm : Basis ι R M) (x y : M) :
    let s := (bm.repr x).support ∪ (bm.repr y).support
    B.toQuadraticMap.toBilin bm x y =
      (∑ i ∈ s,
        ((bm.repr x) i) •((bm.repr y) i) • B (bm i) (bm i)) +
      ∑ p ∈ Finset.filter (fun p ↦ p.1 < p.2) s.offDiag,
        ((bm.repr x) p.1) • ((bm.repr y) p.2) • (B + B.flip) (bm p.1) (bm p.2) := by
  simp_rw [toBilin, polar_toQuadraticMap, BilinMap.toQuadraticMap_apply]
  let s := (bm.repr x).support ∪ (bm.repr y).support
  conv_lhs => rw [← bm.linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset (s := s) (bm.repr x) Finset.subset_union_left _
      (fun i _ ↦ zero_smul R (bm i))]
  conv_lhs =>  rw [← bm.linearCombination_repr y, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset (s := s) (bm.repr y) Finset.subset_union_right _
      (fun i _ ↦ zero_smul R (bm i))]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul,
    ← Finset.sum_product', ← Finset.diag_union_offDiag s,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  simp only [Basis.constr_basis, ↓reduceIte, smul_ite, smul_add, smul_zero, add_right_inj]
  rw [Finset.sum_ite_of_false (by aesop) _ _, ← Finset.sum_filter]
  simp_rw [LinearMap.add_apply, LinearMap.flip_apply, smul_add]
  simp only [Finset.subset_union_left, Finset.subset_union_right, s]

end toBilin

/-
c.f `LinearAlgebra/QuadraticForm/TensorProduct`
-/

open TensorProduct

section uniqueness

universe uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

variable [CommRing R] [CommRing A] [Nontrivial A]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁]
variable [SMulCommClass R A N₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

variable (Q₁ : QuadraticMap A M₁ N₁)
variable (Q₂ : QuadraticMap R M₂ N₂)

variable (Q : QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂))

-- #check span_tmul_eq_top

-- theorem span_tmul_eq_top : Submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤

-- #check TensorProduct.exists_finset

-- #check span_tmul_eq_top

-- #check Finsupp.mem_span_iff_linearCombination


variable (S : Finset (M₁ × M₂)) --(hS ), x = ∑ i ∈ S, i.1 ⊗ₜ[R] i.2

variable (hQ : ∀ a b, Q (a ⊗ₜ b) = Q₁ a ⊗ₜ Q₂ b)

lemma tens1 (x : M₁ ⊗[R] M₂) : x ∈ Submodule.span R { t : M₁ ⊗[R] M₂ | ∃ m n, m ⊗ₜ n = t } := by
  rw [span_tmul_eq_top]
  trivial

/- Every element of the tensor product occurs as a linear combination of basic tensors -/
lemma tens2 (x : M₁ ⊗[R] M₂) :
    let s := { t : M₁ ⊗[R] M₂ | ∃ m n, m ⊗ₜ n = t }
    ∃ l : s →₀ R, Finsupp.linearCombination R (↑) l = x := by
  let s := { t : M₁ ⊗[R] M₂ | ∃ m n, m ⊗ₜ n = t }
  apply (Finsupp.mem_span_iff_linearCombination R s x).mp
  exact tens1 x

/- Alternatively, since `A` has a unit, we can also express each element as a sum of tensors. -/
omit [Algebra R A] [IsScalarTower R A M₁] in
lemma exists_finset_as_lin_comb :  ∑ i ∈ S, i.1 ⊗ₜ[R] i.2 =
    (Finsupp.linearCombination A (fun (i : (M₁ × M₂)) => i.1 ⊗ₜ[R] i.2)
    (Finsupp.mk S (Set.indicator S.toSet (fun _ => (1 : A))) (fun _ => by simp))) := by
  rw [Finsupp.linearCombination_apply_of_mem_supported A (fun ⦃a⦄ a ↦ a) ]
  simp only [Finsupp.coe_mk]
  apply Finset.sum_congr rfl _
  intro x hx
  simp_all only [Finset.mem_coe, Set.indicator_of_mem, one_smul]

omit [Algebra R A] [IsScalarTower R A M₁] [IsScalarTower R A N₁] in
theorem test [LinearOrder (M₁ × M₂)] :
    let g := fun (i : (M₁ × M₂)) => i.1 ⊗ₜ[R] i.2
    let l := Finsupp.mk S (Set.indicator S.toSet (fun _ => (1 : A))) (fun _ => by simp)
    Q (Finsupp.linearCombination A g l) =
      (l.sum fun i r => (r * r) • Q (g i)) +
      ∑ p ∈ l.support.sym2 with ¬ p.IsDiag, polar_lift_lc Q g l p := by
  simp_rw [map_finsupp_linearCombination]

end uniqueness



section TensorProduct

universe uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

variable [CommRing R] [CommRing A]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁]
variable [SMulCommClass R A N₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

variable (R A) in
/-- The tensor product of two quadratic maps injects into quadratic maps on tensor products.

Note this is heterobasic; the quadratic map on the left can take values in a module over a larger
ring than the one on the right. -/
-- `noncomputable` is a performance workaround for mathlib4#7103
noncomputable def tensorDistribFree {ι₁ : Type*} [LinearOrder ι₁] (bm₁ : Basis ι₁ A M₁)
    {ι₂ : Type*} [LinearOrder ι₂] (bm₂ : Basis ι₂ R M₂) :
    QuadraticMap A M₁ N₁ ⊗[R] QuadraticMap R M₂ N₂ →ₗ[A] QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ ⊗[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.toBilinHom _ bm₁ : QuadraticMap A M₁ N₁ →ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.toBilinHom _ bm₂ : QuadraticMap R M₂ N₂ →ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB


variable {ι₁ : Type*} [LinearOrder ι₁] (bm₁ : Basis ι₁ A M₁) (Q₁ : QuadraticMap A M₁ N₁)
variable {ι₂ : Type*} [LinearOrder ι₂] (bm₂ : Basis ι₂ R M₂) (Q₂ : QuadraticMap R M₂ N₂)

@[simp]
theorem tensorDistriFree_tmul (m₁ : M₁) (m₂ : M₂) :
    tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₁ m₁ ⊗ₜ Q₂ m₂ := by
  apply (BilinMap.tensorDistrib_tmul _ _ _ _ _ _).trans
  apply congr_arg₂ _
  · rw [← LinearMap.BilinMap.toQuadraticMap_apply, toBilinHom_apply, toQuadraticMap_toBilin]
  · rw [← LinearMap.BilinMap.toQuadraticMap_apply, toBilinHom_apply, toQuadraticMap_toBilin]

lemma tensorDistribFree_apply
    {ι₁ : Type*} [LinearOrder ι₁] (bm₁ : Basis ι₁ A M₁)
    {ι₂ : Type*} [LinearOrder ι₂] (bm₂ : Basis ι₂ R M₂) :
  tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂) =
    ((Q₁.toBilin bm₁).tmul (Q₂.toBilin bm₂)).toQuadraticMap := rfl

lemma tensorDistriFree_left_self (a : M₁) (b c : M₂):
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (a ⊗ₜ b) (a ⊗ₜ c) =
    Q₁ a ⊗ₜ polarBilin Q₂ b c := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, ← BilinMap.toQuadraticMap_apply, toQuadraticMap_toBilin,
    ← TensorProduct.tmul_add, ← toBilin_symm_eq_Polar Q₂ bm₂]
  rfl

lemma tensorDistriFree_right_self (a b : M₁) (c : M₂):
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (a ⊗ₜ c) (b ⊗ₜ c) =
    polarBilin Q₁ a b ⊗ₜ  Q₂ c := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, ← BilinMap.toQuadraticMap_apply, toQuadraticMap_toBilin,
    ← TensorProduct.add_tmul, ← toBilin_symm_eq_Polar Q₁ bm₁]
  rfl

lemma tensorDistriFree_polar11
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₁ < j₁) (h₂ : i₂ < j₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
      (polar Q₁) (bm₁ i₁) (bm₁ j₁) ⊗ₜ (polar Q₂) (bm₂ i₂) (bm₂ j₂) := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, below_diag Q₁ bm₁ j₁ i₁ h₁, zero_tmul, add_zero,
    above_diag Q₁ bm₁ i₁ j₁ h₁, above_diag Q₂ bm₂ i₂ j₂ h₂]

lemma tensorDistriFree_polar12
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₁ < j₁) (h₂ : j₂ < i₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) = 0 := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, below_diag Q₁ bm₁ j₁ i₁ h₁, zero_tmul, add_zero,
    above_diag Q₁ bm₁ i₁ j₁ h₁, below_diag _ _ _ _ h₂, tmul_zero]

lemma tensorDistriFree_polar21
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : j₁ < i₁) (h₂ : i₂ < j₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) = 0 := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul]
  rw [above_diag Q₂ bm₂ i₂ j₂ h₂]
  rw [below_diag _ _ _ _ h₂]
  rw [tmul_zero, add_zero]
  rw [below_diag _ _ _ _ h₁]
  rw [zero_tmul]

lemma tensorDistriFree_polar22
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : j₁ < i₁) (h₂ : j₂ < i₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
      (polar Q₁) (bm₁ i₁) (bm₁ j₁) ⊗ₜ (polar Q₂) (bm₂ i₂) (bm₂ j₂) := by
    rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, above_diag Q₁ bm₁ j₁ i₁ h₁] --, zero_tmul, add_zero,
    rw [below_diag Q₁ bm₁ i₁ j₁ h₁, below_diag _ _ _ _ h₂, tmul_zero]
    rw [zero_add]
    rw [above_diag _ _ _ _ h₂]
    rw [polar_comm, polar_comm Q₂]

/--
Lift the tensor of two polars (LC)
-/
noncomputable def polarnn_lift_lc (g₁ : ι₁ → M₁ ) (g₂ : ι₂ → M₂) (l : ι₁ × ι₂ →₀ A) :
  Sym2 (ι₁ × ι₂) → N₁ ⊗[R] N₂ :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) =>
    l (i₁, i₂) • l (j₁, j₂) •
      (polar Q₁) (g₁ i₁) (g₁ j₁) ⊗ₜ (polar Q₂) (g₂ i₂) (g₂ j₂),
    by
      intro i j
      simp only [polar_comm]
      rw [smul_comm]
      ⟩

/--
Lift the tensor of two polars (Basis)
-/
noncomputable def polarnn_lift (x : M₁ ⊗[R] M₂) : Sym2 (ι₁ × ι₂) → N₁ ⊗[R] N₂ :=
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  polarnn_lift_lc Q₁ Q₂ bm₁ bm₂ (bm.repr x)

lemma tensorDistriFree_polar1 (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₁ = j₁) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
    Q₁ (bm₁ i₁) ⊗ₜ (polarBilin Q₂) (bm₂ i₂) (bm₂ j₂) := by
  rw [← h₁, tensorDistriFree_left_self]

lemma tensorDistriFree_polar2 (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₂ = j₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
    (polarBilin Q₁) (bm₁ i₁) (bm₁ j₁) ⊗ₜ Q₂ (bm₂ i₂)   := by
  rw [← h₁, tensorDistriFree_right_self]



/--
-Lift the polar (Basis)
--/
noncomputable def polar_lift (Q : QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂))
  (bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂)) (x : M₁ ⊗[R] M₂) := polar_lift_lc Q bm (bm.repr x)

lemma polar_lift_eq_polarnn_lift_on_symOffDiagUpper
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) (p : Sym2 (ι₁ × ι₂))
    (h: p ∈ Finset.filter symOffDiagUpper s) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    polar_lift Q bm x p =  polarnn_lift bm₁ Q₁ bm₂ Q₂ x p := by
  induction' p with i j
  simp_rw [polar_lift, polar_lift_lc, polarnn_lift, polarnn_lift_lc, Sym2.lift_mk, Prod.mk.eta]
  rw [Finset.mem_filter, symOffDiagUpper_iff_proj_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply]
  rcases h2 with ⟨c1,c2⟩ | ⟨c3, c4⟩
  · rw [tensorDistriFree_polar11 bm₁ Q₁ bm₂ Q₂ _ _ _ _ c1 c2]
  · rw [tensorDistriFree_polar22 _ _ _ _ _ _ _ _ c3 c4]

lemma polar_lift_eq_zero_on_symOffDiagLower
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) (p : Sym2 (ι₁ × ι₂))
    (h: p ∈ Finset.filter symOffDiagLower s) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    Q.polar_lift bm x p = 0 := by
  induction' p with i j
  simp_rw [polar_lift, polar_lift_lc, Sym2.lift_mk]
  rw [Finset.mem_filter, symOffDiagLower_iff_proj_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply]
  rcases h2 with ⟨c1,c2⟩ | ⟨c3, c4⟩
  · rw [tensorDistriFree_polar12 bm₁ Q₁ bm₂ Q₂ _ _ _ _ c1 c2, smul_zero, smul_zero]
  · rw [tensorDistriFree_polar21 bm₁ Q₁ bm₂ Q₂ _ _ _ _ c3 c4, smul_zero, smul_zero]

/--
Lift the left side (LC)
-/
noncomputable def polar_left_lift_lc (g₁ : ι₁ → M₁ ) (g₂ : ι₂ → M₂) (l : ι₁ × ι₂ →₀ A) :
    Sym2 (ι₁ × ι₂) → N₁ ⊗[R] N₂ :=
  Sym2.lift ⟨fun i j => if i.1 = j.1 then l i •
    l j • Q₁ (g₁ i.1) ⊗ₜ polarBilin Q₂ (g₂ i.2) (g₂ j.2) else 0,
  fun _ _ => ite_congr (by rw [eq_iff_iff, eq_comm])
    (fun h => by
      simp_rw [polarBilin_apply_apply, h, polar_comm]
      rw [smul_comm]) (congrFun rfl)⟩

/--
Lift the left side (Basis)
-/
noncomputable def polar_left_lift (x : M₁ ⊗[R] M₂) : Sym2 (ι₁ × ι₂) → N₁ ⊗[R] N₂ :=
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  polar_left_lift_lc Q₁ Q₂ bm₁ bm₂ (bm.repr x)

lemma polar_lift_eq_polarleft_lift_on_symOffDiagLeft_lc (g₁ : ι₁ → M₁ ) (g₂ : ι₂ → M₂)
    (l : ι₁ × ι₂ →₀ A)
    (s : Finset (Sym2 (ι₁ × ι₂))) (p : Sym2 (ι₁ × ι₂))
    (h: p ∈ Finset.filter symOffDiagLeft s) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    polar_lift_lc Q (fun i => g₁ i.1 ⊗ₜ g₂ i.2) l p =  polar_left_lift_lc Q₁ Q₂ g₁ g₂ l p := by
  induction' p with i j
  simp
  rw [polar_lift_lc, polar_left_lift_lc]
  simp at h
  obtain e1 := h.2.1
  simp only [Sym2.lift_mk, polarBilin_apply_apply]
  simp_rw [e1]
  simp_all only [true_and, ↓reduceIte]
  obtain ⟨fst, snd⟩ := i
  obtain ⟨fst_1, snd_1⟩ := j
  obtain ⟨left, right⟩ := h
  subst e1
  simp_all only [Basis.tensorProduct_apply]
  rw [tensorDistriFree_left_self]
  rfl

lemma polar_lift_eq_polarleft_lift_on_symOffDiagLeft
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) (p : Sym2 (ι₁ × ι₂))
    (h: p ∈ Finset.filter symOffDiagLeft s) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    polar_lift Q bm x p =  polar_left_lift bm₁ Q₁ bm₂ Q₂ x p := by
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
/-
  simp_rw [polar_lift, polar_left_lift]
  rw [(polar_lift_eq_polarleft_lift_on_symOffDiagLeft_lc bm₁ Q₁ bm₂ Q₂ bm)]
-/

  induction' p with i j
  simp
  rw [polar_lift, polar_lift_lc, polar_left_lift, polar_left_lift_lc]
  simp at h
  obtain e1 := h.2.1
  simp only [Sym2.lift_mk, polarBilin_apply_apply]
  simp_rw [e1]
  simp_all only [true_and, ↓reduceIte]
  obtain ⟨fst, snd⟩ := i
  obtain ⟨fst_1, snd_1⟩ := j
  obtain ⟨left, right⟩ := h
  subst e1
  simp_all only [Basis.tensorProduct_apply]
  rw [tensorDistriFree_polar1 _ _ _ _ _ _ _ _ rfl]
  rfl


lemma sum_left (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    (∑ p ∈ s with symOffDiagLeft p, Q.polar_lift bm x p) =
      (∑ p ∈ s with symOffDiagLeft p, polar_left_lift bm₁ Q₁ bm₂ Q₂ x p) := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  apply Finset.sum_congr rfl _
  intro p hp
  rw [polar_lift_eq_polarleft_lift_on_symOffDiagLeft _ _ _ _ s _ _ _]
  exact hp

/--
Lift the right side
-/
noncomputable def polar_right_lift (x : M₁ ⊗[R] M₂) : Sym2 (ι₁ × ι₂) → N₁ ⊗[R] N₂ :=
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  Sym2.lift ⟨fun i j => if i.2 = j.2 then (bm.repr x) i •
    (bm.repr x) j • (polarBilin Q₁) (bm₁ i.1) (bm₁ j.1) ⊗ₜ Q₂ (bm₂ i.2) else 0,
  fun i j => ite_congr (by rw [eq_iff_iff, eq_comm])
    (fun h => by
      simp_rw [polarBilin_apply_apply, h, polar_comm]
      rw [smul_comm]
      ) (congrFun rfl)⟩

lemma polar_lift_eq_polarright_lift_on_symOffDiagRight
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) (p : Sym2 (ι₁ × ι₂))
    (h: p ∈ Finset.filter symOffDiagRight s) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    polar_lift Q bm x p =  polar_right_lift bm₁ Q₁ bm₂ Q₂ x p := by
  induction' p with i j
  simp
  rw [polar_lift, polar_lift_lc, polar_right_lift]
  simp at h
  obtain e1 := h.2.1
  simp only [Sym2.lift_mk, polarBilin_apply_apply]
  simp_rw [e1]
  simp_all only [true_and, ↓reduceIte]
  obtain ⟨fst, snd⟩ := i
  obtain ⟨fst_1, snd_1⟩ := j
  obtain ⟨left, right⟩ := h
  subst e1
  simp_all only [Basis.tensorProduct_apply]
  rw [tensorDistriFree_polar2 _ _ _ _ _ _ _ _ rfl]
  rfl

lemma sum_right (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    (∑ p ∈ s with symOffDiagRight p, Q.polar_lift bm x p) =
      (∑ p ∈ s with symOffDiagRight p, polar_right_lift bm₁ Q₁ bm₂ Q₂ x p) := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  apply Finset.sum_congr rfl _
  intro p hp
  rw [polar_lift_eq_polarright_lift_on_symOffDiagRight _ _ _ _ s _ _ _]
  exact hp

theorem sum_lower (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    ∑ p ∈ s with symOffDiagLower p, Q.polar_lift bm x p = 0 := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  rw [← Finset.sum_empty]
  rw [Finset.sum_subset (Finset.empty_subset _) (fun p hp₁ _ =>
    polar_lift_eq_zero_on_symOffDiagLower bm₁ Q₁ bm₂ Q₂ s x p hp₁)]

theorem sum_upper (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    (∑ p ∈ s with symOffDiagUpper p, polarnn_lift bm₁ Q₁ bm₂ Q₂ x p) =
    ∑ p ∈ s with symOffDiagUpper p, Q.polar_lift bm x p := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  apply Finset.sum_congr rfl _
  intro p hp
  rw [polar_lift_eq_polarnn_lift_on_symOffDiagUpper bm₁ Q₁ bm₂ Q₂ s x p hp]

theorem pre_tensor_expansion (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    ((bm.repr x).sum fun i r => (r * r) • (Q₁ (bm₁ i.1) ⊗ₜ[R] Q₂ (bm₂ i.2)))
      + (∑ p ∈ s with symOffDiagLeft p, polar_lift Q bm x p)
      + (∑ p ∈ s with symOffDiagRight p, polar_lift Q bm x p)
      + (∑ p ∈ s with symOffDiagUpper p, polar_lift Q bm x p)
      + (∑ p ∈ s with symOffDiagLower p, polar_lift Q bm x p) = Q x := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  simp_rw [basis_expansion Q bm x]
  have e1 (i : ι₁ × ι₂) : Q₁ (bm₁ i.1) ⊗ₜ Q₂ (bm₂ i.2) = Q (bm i) := by
    rw [Basis.tensorProduct_apply, tensorDistriFree_tmul]
  simp_rw [e1]
  simp_rw [polar_lift, polar_lift_lc]
  simp_rw [← sum_on_left_right_upper_lower]
  abel

theorem tensor_expansion (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    ((bm.repr x).sum fun i r => (r * r) • (Q₁ (bm₁ i.1) ⊗ₜ[R] Q₂ (bm₂ i.2)))
      + (∑ p ∈ s with symOffDiagLeft p, polar_left_lift bm₁ Q₁ bm₂ Q₂ x p)
      + (∑ p ∈ s with symOffDiagRight p, polar_right_lift bm₁ Q₁ bm₂ Q₂ x p)
      + (∑ p ∈ s with symOffDiagUpper p, polarnn_lift bm₁ Q₁ bm₂ Q₂ x p) = Q x := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  simp_rw [← pre_tensor_expansion]
  simp_rw [sum_left, sum_right, sum_lower, sum_upper]
  rw [add_zero]

end TensorProduct

end QuadraticMap
