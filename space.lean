/-
Copyright (c) 2025 __________________. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: __________________
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.HopkinsLevitzki

open Submodule Module Basis

noncomputable section

variable {K : Type*} [DivisionRing K] {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)

namespace LinearMap

/-- 选择与核空间互补的子空间 -/
def kerComplement : Submodule K V :=
  (ker f).exists_isCompl.choose

/-- 核空间与其补空间构成互补子空间 -/
lemma isCompl_ker_kerComplement : IsCompl f.kerComplement (ker f) :=
  (ker f).exists_isCompl.choose_spec.symm

/-- 核空间与其补空间的直和等价于整个空间 -/
def directSumDecomposition : (f.kerComplement × (ker f)) ≃ₗ[K] V :=
  prodEquivOfIsCompl _ _ f.isCompl_ker_kerComplement

/-- 直和分解的核分量在映射 `f` 下为零，因此不影响像。

    具体来说，对于任意 `y ∈ V`，将其分解为 `y = y_ker + y_comp`（其中 `y_ker ∈ ker f`, `y_comp ∈ kerComplement f`），
    则有 `f y_ker = 0`，因此 `f y = f y_comp`。
    而 `(directSumDecomposition.symm y).1` 对应的是核分量 `y_ker`。 -/
lemma apply_ker_component_eq_zero (y : V) : f (f.directSumDecomposition.symm y).1 = f y := by
  nth_rw 2 [← Submodule.IsCompl.projection_add_projection_eq_self f.isCompl_ker_kerComplement y]
  refine sub_mem_ker_iff.mp ?_
  #check map_coe_ker
  sorry
  -- simp only [map_add, , add_zero]
  -- rfl

/-- 通过线性映射f的直和分解构造V的基。

    当V被分解为ker f ⊕ kerComplement f时，该基由核空间和补空间的基通过直和分解等价映射得到。
    具体来说：
    - 索引集是`kerComplement f`的基索引与`ker f`的基索引的直和（Sum类型）
    - 基向量通过`f.directSumDecomposition`等价关系从子空间基组合而成

    这一定义体现了第一同构定理的几何实质：V ≃ ker f × (range f)，且kerComplement f ≃ range f。
-/
def decomposition_basis :
    Basis ((ofVectorSpaceIndex K f.kerComplement) ⊕ (ofVectorSpaceIndex K (LinearMap.ker f))) K V :=
  .map (.prod (ofVectorSpace K _) (ofVectorSpace K _)) (f.directSumDecomposition)

/-- 线性映射 `f` 在核补空间上的限制，即将核补空间嵌入到 `V` 后应用 `f` -/
def ker_complement_restriction : f.kerComplement →ₗ[K] W :=
    f.comp f.kerComplement.subtype

/-- 线性映射 `f` 在其核补空间上的限制是单射。

这是因为核空间 `ker f` 与补空间 `kerComplement f` 是互补子空间（由 `isCompl_ker_kerComplement` 保证），
它们的交集仅为零子空间，因此 `f` 在补空间上的限制具有平凡核。 -/
lemma ker_complement_restriction_injective : ker f.ker_complement_restriction = ⊥ := by
  simpa [ker_complement_restriction, ker_comp, ← disjoint_iff_comap_eq_bot]
    using f.isCompl_ker_kerComplement.disjoint

/-- 通过核补空间的基和限制映射 `f ∘ Submodule.subtype (kerComplement f)` 构造的映射，
    将基索引映射到 `W` 中的向量 -/
def ker_complement_basis_image :
    ofVectorSpaceIndex K f.kerComplement → W :=
  f.ker_complement_restriction ∘ (ofVectorSpace K f.kerComplement)

/-- `ker_complement_basis_image f` 是线性无关的，因为 `f` 在核补空间上是单射 -/
lemma linear_independent_ker_complement_basis_image :
    LinearIndependent K f.ker_complement_basis_image :=
  LinearIndependent.map' (ofVectorSpace K f.kerComplement).linearIndependent _
    f.ker_complement_restriction_injective

/-- 通过将核补空间的基像（对应 `range f`）与余核的基扩展组合，构造 `W` 的基 -/
def range_decomposition_basis :
    Basis ((ofVectorSpaceIndex K f.kerComplement) ⊕
      (sumExtendIndex f.linear_independent_ker_complement_basis_image)) K W :=
  Basis.sumExtend f.linear_independent_ker_complement_basis_image

open FiniteDimensional
instance [FiniteDimensional K W] :
  Fintype (sumExtendIndex f.linear_independent_ker_complement_basis_image) := by
  have h1 := fintypeBasisIndex f.range_decomposition_basis
  apply @Fintype.sumRight _ _ h1

instance [FiniteDimensional K V]: Fintype (ofVectorSpaceIndex K f.kerComplement) := by infer_instance
instance [FiniteDimensional K V]: Fintype (ofVectorSpaceIndex K (ker f)) := by infer_instance
instance : DecidableEq (ofVectorSpaceIndex K f.kerComplement) := Classical.typeDecidableEq _
instance : DecidableEq (ofVectorSpaceIndex K (ker f)) := Classical.typeDecidableEq _

/-- 核空间的补空间线性同构于像空间 -/
def kerComplementEquivRange :
    f.kerComplement ≃ₗ[K] (range f) := by
  let g : f.kerComplement →ₗ[K] range f :=
    codRestrict (range f) f.ker_complement_restriction
      (by
        intro x
        simp only [mem_range, LinearMap.mem_range, LinearMap.ker_complement_restriction, LinearMap.comp_apply]
        exact ⟨(f.kerComplement.subtype x), rfl⟩
      )
  apply LinearEquiv.ofBijective g
  constructor
  · simpa [← ker_eq_bot, g, ker_codRestrict]
     using f.ker_complement_restriction_injective
  intro ⟨x, y, hyx⟩
  use (f.directSumDecomposition.2 y).1
  simp [g, codRestrict, ← hyx, ker_complement_restriction, apply_ker_component_eq_zero]


/-- 核补空间的维数等于线性映射的秩。

    这是第一同构定理的推论：由于 `kerComplement f ≃ₗ[K] range f`，
    所以 `finrank K (kerComplement f) = finrank K (range f) = rank f`。
-/
lemma finrank_kerComplement_eq_rank {r : ℕ} (hr : rank f = r) :
    finrank K f.kerComplement = r := by
  simp [(finrank_eq_of_rank_eq hr).symm, LinearEquiv.finrank_eq f.kerComplementEquivRange]

/-- 核空间的维数等于全空间维数减去线性映射的秩。

    这是秩-零化度定理（Rank-Nullity Theorem）的直接应用：
    `finrank K V = finrank K (range f) + finrank K (ker f)`，
    因此 `finrank K (ker f) = finrank K V - rank f`。
-/
lemma finrank_ker_eq
  [FiniteDimensional K V] {r n: ℕ}
  (hr : rank f = r) (hn : finrank K V = n) : finrank K (ker f) = n - r := by
  simp [← hn, ← finrank_range_add_finrank_ker f, (finrank_eq_of_rank_eq hr).symm]

lemma card_cokernel_basis_index_eq  {m r : ℕ} [FiniteDimensional K V]
    [FiniteDimensional K W]
    (hm : finrank K W = m) (hr : f.rank = r) :
  Fintype.card (sumExtendIndex f.linear_independent_ker_complement_basis_image) = m - r := by
  have := finrank_eq_card_basis f.range_decomposition_basis
  rw [Fintype.card_sum, hm] at this
  rw [this]
  simp [← finrank_eq_card_basis (ofVectorSpace K f.kerComplement),
    f.finrank_kerComplement_eq_rank hr]

lemma apply_kerComplement_basis_eq_range_basis (j) : (f (f.decomposition_basis (Sum.inl j))) = (f.range_decomposition_basis (Sum.inl j)) := by
    simp [LinearMap.decomposition_basis, directSumDecomposition,range_decomposition_basis, sumExtend, Equiv.sumCongr,
      ker_complement_basis_image, ker_complement_restriction]


end LinearMap

end

/-- 当索引类型 `ι` 的基数等于自然数 `r` 时，非构造性地获得 `ι` 与 `Fin r` 之间的等价关系。

这个等价关系存在是因为：
- 前提条件 `h : Cardinal.mk ι = r` 保证了 `ι` 的势等于 `r`
- 通过 `Cardinal.mk_eq_nat_iff` 将基数相等转化为类型等价
- 使用选择公理 (`Classical.choice`) 从存在性证明中提取具体的等价关系

注意：由于使用了选择公理，此定义是 `noncomputable` 的。 -/
noncomputable def indexEquivOfCardinalEq {ι}{r : ℕ} (h : Cardinal.mk ι = r) :
    ι ≃ Fin r := by
  apply Classical.choice
  rwa [← Cardinal.mk_eq_nat_iff]

/-- 对于有限维向量空间 `V` 的任意一组基 `b : Basis ι K V`，其索引集 `ι` 与 `Fin (finrank K V)` 等价。

这个等价关系的数学基础是：
1. 基的势等于向量空间的维数 (`Basis.mk_eq_rank''`)
2. 在有限维情况下，维数等于秩 (`finrank_eq_rank'`)
3. 通过 `indexEquivOfCardinalEq` 将基数相等具体化为类型等价

这表明虽然基的索引类型 `ι` 可能抽象不同，但它的本质大小由向量空间的维数唯一确定。 -/
noncomputable def basisIndexEquivFin {ι r K V} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hr : finrank K V = r) (b : Basis ι K V) : ι ≃ Fin r := by
  apply indexEquivOfCardinalEq
  rw [Basis.mk_eq_rank'' b]
  rw [← hr, finrank_eq_rank']

section

variable  {R : Type} [Field R] {m n r: ℕ}  {M₁ : Type} {M₂ : Type}
  [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M₁] [Module R M₂]
  [FiniteDimensional R M₁]
  [FiniteDimensional R M₂]
  (f : M₁ →ₗ[R] M₂)

open Matrix LinearMap

/-- 线性映射的标准形存在性定理（抽象索引版本）。

对于任意线性映射 `f : M₁ →ₗ[R] M₂`，存在适当的基使得 `f` 的矩阵表示为分块对角形式：`[I_r  0; 0 0 ]`
其中 `r = rank f`，`I_r` 是 `r × r` 单位矩阵。

这个版本使用抽象的基索引类型，保持最大的一般性。 -/
theorem exists_basis_for_normal_form_abstract :
  ∃ (v₁ : Basis ((ofVectorSpaceIndex R f.kerComplement) ⊕ (ofVectorSpaceIndex R (LinearMap.ker f))) R M₁)
    (v₂ : Basis ((ofVectorSpaceIndex R f.kerComplement) ⊕
      (sumExtendIndex f.linear_independent_ker_complement_basis_image)) R M₂),
    LinearMap.toMatrix v₁ v₂ f = fromBlocks 1 0 0 0 := by
  use f.decomposition_basis, f.range_decomposition_basis
  funext i j
  simp [LinearMap.toMatrix_apply]
  match i, j with
  | Sum.inl i', Sum.inl j' =>
    simp [f.apply_kerComplement_basis_eq_range_basis j',
      Finsupp.single, Pi.single, Function.update, Matrix.one_apply]
  | Sum.inr i', Sum.inr j' =>
    simp [LinearMap.decomposition_basis, directSumDecomposition]
  | Sum.inl i', Sum.inr j' =>
    simp [LinearMap.decomposition_basis, directSumDecomposition]
  | Sum.inr i', Sum.inl j' =>
    simp [f.apply_kerComplement_basis_eq_range_basis j']

/-- 线性映射的标准形存在性定理（具体维数版本）。

在已知具体维数条件下（`finrank R M₁ = n`, `finrank R M₂ = m`, `rank f = r`），
存在基使得 `f` 的矩阵表示为标准分块形式：`[I_r  0; 0 0 ]`
其中索引集具体化为 `Fin r ⊕ Fin (n - r)` 和 `Fin r ⊕ Fin (m - r)`。

这是秩-零化度定理的矩阵表现形式。 -/
theorem exists_basis_for_normal_form (hn : finrank R M₁ = n) (hm : finrank R M₂ = m)
  (hr : rank f = r) :
  ∃ (v₁ : Basis (Fin r ⊕ Fin (n - r)) R M₁) (v₂ : Basis (Fin r ⊕ Fin (m - r)) R M₂)
  , LinearMap.toMatrix v₁ v₂ f = fromBlocks 1 0 0 0:= by
  have ⟨v₁, v₂, hvf⟩ := exists_basis_for_normal_form_abstract f
  let hu₁ : (ofVectorSpaceIndex R f.kerComplement) ⊕ (ofVectorSpaceIndex R (ker f)) ≃ Fin r ⊕ Fin (n - r) := by
    refine Equiv.sumCongr ?_ ?_
    apply basisIndexEquivFin (finrank_kerComplement_eq_rank f hr) (ofVectorSpace R _)
    apply basisIndexEquivFin (f.finrank_ker_eq hr hn) (ofVectorSpace R _)
  let u₁ : Basis (Fin r ⊕ Fin (n - r)) R M₁ :=  v₁.reindex hu₁
  let hu₂ : (ofVectorSpaceIndex R f.kerComplement) ⊕ (sumExtendIndex f.linear_independent_ker_complement_basis_image) ≃ Fin r ⊕ Fin (m - r) := by
    refine Equiv.sumCongr ?_ ?_
    apply basisIndexEquivFin (finrank_kerComplement_eq_rank f hr) (ofVectorSpace R _)
    apply indexEquivOfCardinalEq
    simp [card_cokernel_basis_index_eq f hm hr]
  let u₂ : Basis (Fin r ⊕ Fin (m - r)) R M₂ :=  v₂.reindex hu₂
  use u₁, u₂
  calc (LinearMap.toMatrix u₁ u₂) f
    _ = ((LinearMap.toMatrix v₁ v₂) f).reindex hu₂ hu₁ := by
      simp [u₁, u₂]
      funext i j
      simp [LinearMap.toMatrix_apply]
    _ = (fromBlocks 1 0 0 0).reindex hu₂ hu₁ := by rw [hvf]
    _ = _ := by
      simp [hu₁, hu₂, Equiv.sumCongr]
      funext i j
      match i, j with
      | Sum.inl i', Sum.inl j' => simp [basisIndexEquivFin, indexEquivOfCardinalEq, Matrix.one_apply]
      | Sum.inr i', Sum.inr j' => simp
      | Sum.inl i', Sum.inr j' => simp
      | Sum.inr i', Sum.inl j' => simp

end
