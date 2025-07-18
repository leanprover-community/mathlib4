/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!

# Inner product space structure on tensor products

-/

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

open scoped TensorProduct

instance TensorProduct.instInner : Inner 𝕜 (E ⊗[𝕜] F) :=
  ⟨fun x y =>
    LinearMap.mul' 𝕜 𝕜 ((homTensorHomMap 𝕜 _ _ _ _ ((mapₛₗ (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x)) y)⟩

@[simp]
theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl

@[simp]
theorem TensorProduct.inner_add (x y z : E ⊗[𝕜] F) :
    inner 𝕜 x (y + z) = inner 𝕜 x y + inner 𝕜 x z := by
  simp [inner]

@[simp]
theorem TensorProduct.add_inner (x y z : E ⊗[𝕜] F) :
    inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z := by
  simp [inner]

@[simp]
theorem TensorProduct.sum_inner {n : Type*} [Fintype n] (x : n → E ⊗[𝕜] F)
    (y : E ⊗[𝕜] F) : inner 𝕜 (∑ i, x i) y = ∑ i, inner 𝕜 (x i) y := by
  simp [inner]

@[simp]
theorem TensorProduct.inner_sum {n : Type*} [Fintype n] (x : E ⊗[𝕜] F) (y : n → E ⊗[𝕜] F) :
    inner 𝕜 x (∑ i, y i) = ∑ i, inner 𝕜 x (y i) := by
  simp [inner]

@[simp]
theorem TensorProduct.smul_inner (x y : E ⊗[𝕜] F) (c : 𝕜) :
    inner 𝕜 (c • x) y = starRingEnd 𝕜 c * inner 𝕜 x y := by
  simp [inner]

@[simp]
theorem TensorProduct.inner_smul (x y : E ⊗[𝕜] F) (c : 𝕜) :
    inner 𝕜 x (c • y) = c * inner 𝕜 x y := by
  simp [inner]

theorem TensorProduct.conj_inner (x y : E ⊗[𝕜] F) :
    starRingEnd 𝕜 (inner 𝕜 x y) = inner 𝕜 y x :=
  x.induction_on (by simp only [inner, map_zero, LinearMap.zero_apply])
    (y.induction_on (by simp only [inner, mapₛₗ_tmul, homTensorHomMap_apply, map_zero,
      LinearMap.zero_apply, implies_true]) (fun x y => by simp only [inner_tmul, map_mul,
      inner_conj_symm, implies_true])
    (fun x y hx hy a b => by simp_all only [inner, mapₛₗ_tmul, homTensorHomMap_apply, map_add,
      LinearMap.add_apply]))
    (fun x y hx hy => by simp_all only [inner, map_add, LinearMap.add_apply])

section

theorem TensorProduct.of_basis_eq_span {𝕜 E F : Type*} [CommSemiring 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] (x : TensorProduct 𝕜 E F)
    {ι₁ ι₂ : Type _} [Fintype ι₁] [Fintype ι₂] (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F) :
    x = ∑ i : ι₁, ∑ j : ι₂, (b₁.tensorProduct b₂).repr x (i, j) • b₁ i ⊗ₜ[𝕜] b₂ j :=
  x.induction_on
  (by simp only [map_zero, Finsupp.zero_apply, zero_smul, Finset.sum_const_zero])
  (fun α₁ α₂ => by
    simp_rw [Basis.tensorProduct_repr_tmul_apply,
      smul_eq_mul, mul_comm, ← TensorProduct.smul_tmul_smul, ←
      TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, Basis.sum_repr])
  (fun a b ha hb => by
    simp_rw [_root_.map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb])

variable (𝕜 E) in
lemma toFinitedimensional (e : E) :
    ∃ (E' : Submodule 𝕜 E) (_ : FiniteDimensional 𝕜 E'), e ∈ E' := by
  classical
  let b := Basis.ofVectorSpace 𝕜 E
  refine ⟨Submodule.span 𝕜 (Finset.image b (b.repr e).support),
    FiniteDimensional.span_finset _ _, ?_⟩
  convert Basis.mem_span_repr_support b e
  simp

variable (E F) in
lemma tensor_submodule_range_mono1 {E' E'' : Submodule 𝕜 E} (F' : Submodule 𝕜 F)
    (le1 : E' ≤ E'') :
    LinearMap.range (TensorProduct.map E'.subtype F'.subtype) ≤
      LinearMap.range (TensorProduct.map E''.subtype F'.subtype) := fun x hx => by
  obtain ⟨x, rfl⟩ := hx
  induction' x using TensorProduct.induction_on with e f x₁ x₂ ih₁ ih₂
  · rw [map_zero]
    exact Submodule.zero_mem _
  · exact ⟨⟨e, le1 e.2⟩ ⊗ₜ f, rfl⟩
  · rw [map_add]
    exact Submodule.add_mem _ ih₁ ih₂

variable (E F) in
lemma tensor_submodule_range_mono2 (E' : Submodule 𝕜 E) {F' F'' : Submodule 𝕜 F}
    (le2 : F' ≤ F'') :
    LinearMap.range (TensorProduct.map E'.subtype F'.subtype) ≤
      LinearMap.range (TensorProduct.map E'.subtype F''.subtype) := fun x hx => by
  obtain ⟨x, rfl⟩ := hx
  induction' x using TensorProduct.induction_on with e f x₁ x₂ ih₁ ih₂
  · rw [map_zero]; exact Submodule.zero_mem _
  · exact ⟨e ⊗ₜ ⟨f, le2 f.2⟩, rfl⟩
  · rw [map_add]; exact Submodule.add_mem _ ih₁ ih₂

variable (E F) in
lemma toTensorFiniteDimensional (z : E ⊗[𝕜] F) : ∃ (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (_ : FiniteDimensional 𝕜 E') (_ : FiniteDimensional 𝕜 F'),
    z ∈ LinearMap.range (TensorProduct.map E'.subtype F'.subtype) := by
  induction' z using TensorProduct.induction_on with e f z₁ z₂ ih₁ ih₂
  · refine ⟨⊥, ⊥, ?_, ?_, Submodule.zero_mem _⟩
    exacts [finiteDimensional_bot 𝕜 E, finiteDimensional_bot 𝕜 F]
  · rcases toFinitedimensional 𝕜 E e with ⟨E', iE', he⟩
    rcases toFinitedimensional 𝕜 F f with ⟨F', iF', hf⟩
    exact ⟨E', F', iE', iF', ⟨⟨e, he⟩ ⊗ₜ ⟨f, hf⟩, rfl⟩⟩
  · rcases ih₁ with ⟨E1, F1, iE1, iF1, ⟨z1, rfl⟩⟩
    rcases ih₂ with ⟨E2, F2, iE2, iF2, ⟨z2, rfl⟩⟩
    have le1 : LinearMap.range (TensorProduct.map E1.subtype F1.subtype) ≤
        LinearMap.range (TensorProduct.map (E1 ⊔ E2).subtype (F1 ⊔ F2).subtype) :=
      (tensor_submodule_range_mono1 E F F1 (le_sup_left : E1 ≤ E1 ⊔ E2)).trans
        (tensor_submodule_range_mono2 E F _ le_sup_left)
    have le2 : LinearMap.range (TensorProduct.map E2.subtype F2.subtype) ≤
        LinearMap.range (TensorProduct.map (E1 ⊔ E2).subtype (F1 ⊔ F2).subtype) :=
      (tensor_submodule_range_mono1 _ _ _ (le_sup_right : E2 ≤ E1 ⊔ E2)).trans
        (tensor_submodule_range_mono2 _ _ _ le_sup_right)
    exact ⟨E1 ⊔ E2, F1 ⊔ F2, Submodule.finiteDimensional_sup E1 E2,
      Submodule.finiteDimensional_sup F1 F2, Submodule.add_mem _ (le1 ⟨z1, rfl⟩) (le2 ⟨z2, rfl⟩)⟩

lemma tensor_product_aux_restrict_apply' (x y : E ⊗[𝕜] F)
    (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x' y' : E' ⊗[𝕜] F')
    (hx : x = TensorProduct.map E'.subtype F'.subtype x')
    (hy : y = TensorProduct.map E'.subtype F'.subtype y') :
    (inner 𝕜 x y) = (inner 𝕜 x' y') := by
  rw [hx, hy]
  revert x
  induction' x' using TensorProduct.induction_on with e' f' x₁ x₂ ih₁ ih₂
  · simp [inner]
  · revert y
    induction' y' using TensorProduct.induction_on with e'' f'' y₁ y₂ ih₁ ih₂
    · simp [inner]
    · intro x h y h'
      rfl
    · intro x hx y hy
      simp_all
  · intro x hx
    simp_all

lemma tensor_product_aux_restrict_apply (x y : E ⊗[𝕜] F)
    (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (hx : x ∈ LinearMap.range (TensorProduct.map E'.subtype F'.subtype))
    (hy : y ∈ LinearMap.range (TensorProduct.map E'.subtype F'.subtype)) :
    (inner 𝕜 x y) = (inner 𝕜 hx.choose hy.choose) := by
  apply tensor_product_aux_restrict_apply'
  · exact (hx.choose_spec).symm
  · exact (hy.choose_spec).symm

open scoped ComplexOrder

theorem TensorProduct.inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  obtain ⟨E', F', iE', iF', hz⟩ := toTensorFiniteDimensional E F x
  rw [tensor_product_aux_restrict_apply x x E' F' hz hz] at hx
  let y := hz.choose
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have hy : y = hz.choose := rfl
  rw [← hy] at hx
  rw [TensorProduct.of_basis_eq_span y e.toBasis f.toBasis] at hx
  simp only [OrthonormalBasis.coe_toBasis, TensorProduct.inner_sum, TensorProduct.inner_smul,
    TensorProduct.sum_inner, TensorProduct.smul_inner, inner_tmul] at hx
  simp [OrthonormalBasis.inner_eq_ite] at hx
  simp [RCLike.mul_conj, ← Finset.sum_product'] at hx
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by simp)] at hx
  simp at hx
  have : y = 0 := by
    rw [Basis.ext_elem_iff (e.toBasis.tensorProduct f.toBasis)]
    simp only [hx, map_zero, Finsupp.coe_zero, Pi.zero_apply, implies_true]
  rw [← hz.choose_spec, ← hy, this, map_zero]

theorem TensorProduct.re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := by
  obtain ⟨E', F', iE', iF', hz⟩ := toTensorFiniteDimensional E F x
  rw [tensor_product_aux_restrict_apply x x E' F' hz hz]
  let y := hz.choose
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have hy : y = hz.choose := rfl
  rw [← hy]
  rw [TensorProduct.of_basis_eq_span y e.toBasis f.toBasis]
  simp only [OrthonormalBasis.coe_toBasis, TensorProduct.inner_sum, TensorProduct.inner_smul,
    TensorProduct.sum_inner, TensorProduct.smul_inner, inner_tmul]
  simp only [OrthonormalBasis.inner_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, ← Finset.sum_product', RCLike.mul_conj, map_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact sq_nonneg _

end

noncomputable instance TensorProduct.instNormedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 (E ⊗[𝕜] F) _ _ _
  { conj_inner_symm := fun x y => TensorProduct.conj_inner y x
    add_left := TensorProduct.add_inner
    smul_left := TensorProduct.smul_inner
    definite := TensorProduct.inner_definite
    re_inner_nonneg := TensorProduct.re_inner_self_nonneg }

noncomputable instance TensorProduct.instInnerProductSpace :
    @InnerProductSpace 𝕜 (E ⊗[𝕜] F) _ _ :=
  InnerProductSpace.ofCore _
