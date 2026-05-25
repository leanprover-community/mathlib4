/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Subspaces of inner product spaces

This file defines the inner-product structure on a subspace of an inner-product space, and proves
some theorems about orthogonal families of subspaces.
-/

@[expose] public section

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp Module

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Submodule

variable [AddCommGroup E] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Inner product space structure on subspaces -/

/-- Induced inner product on a submodule. -/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  .induced W.subtype

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
theorem Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫ :=
  rfl

theorem Orthonormal.codRestrict {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) (s : Submodule 𝕜 E)
    (hvs : ∀ i, v i ∈ s) : Orthonormal 𝕜 (E := s) (ι := ι) (Set.codRestrict v s hvs) :=
  s.subtypeₗᵢ.orthonormal_comp_iff.mp hv

theorem orthonormal_span {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Orthonormal 𝕜 (E := Submodule.span 𝕜 (Set.range v)) (ι := ι) fun i : ι =>
      ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :=
  hv.codRestrict (Submodule.span 𝕜 (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)

end Submodule

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/

section OrthogonalFamily_Seminormed

variable [AddCommGroup E] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} (𝕜)

open DirectSum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → Submodule 𝕜 E`.  We
instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.
The connection to the subobject spelling is shown in `orthogonalFamily_iff_pairwise`.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`PiLp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
def OrthogonalFamily (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, SeminormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace 𝕜 (G i)] (V : ∀ i, G i →ₗᵢ[𝕜] E) : Prop :=
  Pairwise fun i j => ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0

variable {𝕜}
variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace 𝕜 (G i)] {V : ∀ i, G i →ₗᵢ[𝕜] E}

theorem Orthonormal.orthogonalFamily {v : ι → E} (hv : Orthonormal 𝕜 v) :
    OrthogonalFamily 𝕜 (fun _i : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]

section
variable (hV : OrthogonalFamily 𝕜 G V)
include hV

theorem OrthogonalFamily.eq_ite [DecidableEq ι] {i j : ι} (v : G i) (w : G j) :
    ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 := by
  split_ifs with h
  · rfl
  · exact hV h v w

theorem OrthogonalFamily.inner_right_dfinsupp
    [∀ (i) (x : G i), Decidable (x ≠ 0)] [DecidableEq ι] (l : ⨁ i, G i) (i : ι) (v : G i) :
    ⟪V i v, l.sum fun j => V j⟫ = ⟪v, l i⟫ :=
  calc
    ⟪V i v, l.sum fun j => V j⟫ = l.sum fun j => fun w => ⟪V i v, V j w⟫ :=
      DFinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.sum fun j => fun w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      (congr_arg l.sum <| funext fun _ => funext <| hV.eq_ite v)
    _ = ⟪v, l i⟫ := by
      simp only [DFinsupp.sum, Finset.sum_ite_eq,
        DFinsupp.mem_support_toFun]
      split_ifs with h
      · simp only [LinearIsometry.inner_map_map]
      · simp only [of_not_not h, inner_zero_right]

theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (l : ∀ i, G i) (i : ι) (v : G i) :
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ := by
  classical
  calc
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
    _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
      (congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j))
    _ = ⟪v, l i⟫ := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, (V i).inner_map_map, if_true]

nonrec theorem OrthogonalFamily.inner_sum (l₁ l₂ : ∀ i, G i) (s : Finset ι) :
    ⟪∑ i ∈ s, V i (l₁ i), ∑ j ∈ s, V j (l₂ j)⟫ = ∑ i ∈ s, ⟪l₁ i, l₂ i⟫ := by
  classical
  calc
    ⟪∑ i ∈ s, V i (l₁ i), ∑ j ∈ s, V j (l₂ j)⟫ = ∑ j ∈ s, ∑ i ∈ s, ⟪V i (l₁ i), V j (l₂ j)⟫ := by
      simp only [sum_inner, inner_sum]
    _ = ∑ j ∈ s, ∑ i ∈ s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 := by
      congr with i
      congr with j
      apply hV.eq_ite
    _ = ∑ i ∈ s, ⟪l₁ i, l₂ i⟫ := by
      simp only [Finset.sum_ite_of_true, Finset.sum_ite_eq', LinearIsometry.inner_map_map,
        imp_self, imp_true_iff]

theorem OrthogonalFamily.norm_sum (l : ∀ i, G i) (s : Finset ι) :
    ‖∑ i ∈ s, V i (l i)‖ ^ 2 = ∑ i ∈ s, ‖l i‖ ^ 2 := by
  have : ((‖∑ i ∈ s, V i (l i)‖ : ℝ) : 𝕜) ^ 2 = ∑ i ∈ s, ((‖l i‖ : ℝ) : 𝕜) ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact mod_cast this

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
theorem OrthogonalFamily.comp {γ : Type*} {f : γ → ι} (hf : Function.Injective f) :
    OrthogonalFamily 𝕜 (fun g => G (f g)) fun g => V (f g) :=
  fun _i _j hij v w => hV (hf.ne hij) v w

theorem OrthogonalFamily.orthonormal_sigma_orthonormal {α : ι → Type*} {v_family : ∀ i, α i → G i}
    (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 fun a : Σ i, α i => V a.1 (v_family a.1 a.2) := by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v ≠ w := fun h => by
      subst h
      exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).2 this
  · exact hV hij (v_family i v) (v_family j w)

theorem OrthogonalFamily.norm_sq_diff_sum [DecidableEq ι] (f : ∀ i, G i) (s₁ s₂ : Finset ι) :
    ‖(∑ i ∈ s₁, V i (f i)) - ∑ i ∈ s₂, V i (f i)‖ ^ 2 =
      (∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2 := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  let F : ∀ i, G i := fun i => if i ∈ s₁ then f i else -f i
  have hF₁ : ∀ i ∈ s₁ \ s₂, F i = f i := fun i hi => if_pos (Finset.sdiff_subset hi)
  have hF₂ : ∀ i ∈ s₂ \ s₁, F i = -f i := fun i hi => if_neg (Finset.mem_sdiff.mp hi).2
  have hF : ∀ i, ‖F i‖ = ‖f i‖ := by
    intro i
    dsimp only [F]
    split_ifs <;> simp only [norm_neg]
  have :
    ‖(∑ i ∈ s₁ \ s₂, V i (F i)) + ∑ i ∈ s₂ \ s₁, V i (F i)‖ ^ 2 =
      (∑ i ∈ s₁ \ s₂, ‖F i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖F i‖ ^ 2 := by
    have hs : Disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff
    simpa only [Finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ ∪ s₂ \ s₁)
  convert! this using 4
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₁ i hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₂ i hi, LinearIsometry.map_neg]
  · simp only [hF]
  · simp only [hF]

/-- A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(fun i ↦ ‖f i‖ ^ 2)` is summable. -/
theorem OrthogonalFamily.summable_iff_norm_sq_summable [CompleteSpace E] (f : ∀ i, G i) :
    (Summable fun i => V i (f i)) ↔ Summable fun i => ‖f i‖ ^ 2 := by
  classical
    simp only [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff, norm_neg_add,
      Real.norm_eq_abs]
    constructor
    · intro hf ε hε
      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
      use a
      intro s₁ hs₁ s₂ hs₂
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
      refine (abs_sub _ _).trans_lt ?_
      have : ∀ i, 0 ≤ ‖f i‖ ^ 2 := fun i : ι => sq_nonneg _
      simp only [Finset.abs_sum_of_nonneg' this]
      have : ((∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2) < √ε ^ 2 := by
        rw [← hV.norm_sq_diff_sum, sq_lt_sq, abs_of_nonneg (sqrt_nonneg _),
          abs_of_nonneg (norm_nonneg _)]
        exact H s₁ hs₁ s₂ hs₂
      have hη := sq_sqrt (le_of_lt hε)
      linarith
    · intro hf ε hε
      have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
      obtain ⟨a, H⟩ := hf _ hε'
      use a
      intro s₁ hs₁ s₂ hs₂
      refine (abs_lt_of_sq_lt_sq' ?_ (le_of_lt hε)).2
      have has : a ≤ s₁ ⊓ s₂ := le_inf hs₁ hs₂
      rw [hV.norm_sq_diff_sum]
      have Hs₁ : ∑ x ∈ s₁ \ s₂, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert! H _ hs₁ _ has
        have : s₁ ⊓ s₂ ⊆ s₁ := Finset.inter_subset_left
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      have Hs₂ : ∑ x ∈ s₂ \ s₁, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert! H _ hs₂ _ has
        have : s₁ ⊓ s₂ ⊆ s₂ := Finset.inter_subset_right
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      linarith

end

end OrthogonalFamily_Seminormed

section OrthogonalFamily

variable [AddCommGroup E] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} {G : ι → Type*}

/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
theorem OrthogonalFamily.independent {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    iSupIndep V := by
  classical
  apply iSupIndep_of_dfinsupp_lsum_injective
  refine LinearMap.ker_eq_bot.mp ?_
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  ext i
  suffices ⟪(v i : E), v i⟫ = 0 by simpa only [inner_self_eq_zero] using this
  calc
    ⟪(v i : E), v i⟫ = ⟪(v i : E), DFinsupp.lsum ℕ (fun i => (V i).subtype) v⟫ := by
      simpa only [DFinsupp.sumAddHom_apply, DFinsupp.lsum_apply_apply] using
        (hV.inner_right_dfinsupp v i (v i)).symm
    _ = 0 := by simp only [hv, inner_zero_right]

theorem DirectSum.IsInternal.collectedBasis_orthonormal [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι → Type*}
    {v_family : ∀ i, Basis (α i) 𝕜 (V i)} (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 (hV_sum.collectedBasis v_family) := by
  simpa only [hV_sum.collectedBasis_coe] using hV.orthonormal_sigma_orthonormal hv_family

end OrthogonalFamily
