/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Bilinear form

This file defines orthogonal bilinear forms.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

open LinearMap (BilinForm)
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `BilinForm.iIsOrtho`. -/
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0

theorem isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

theorem isOrtho_zero_left (x : M) : IsOrtho B (0 : M) x := LinearMap.isOrtho_zero_left B x

theorem isOrtho_zero_right (x : M) : IsOrtho B x (0 : M) :=
  zero_right x

theorem ne_zero_of_not_isOrtho_self {B : BilinForm K V} (x : V) (hx₁ : ¬B.IsOrtho x x) : x ≠ 0 :=
  fun hx₂ => hx₁ (hx₂.symm ▸ isOrtho_zero_left _)

theorem IsRefl.ortho_comm (H : B.IsRefl) {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩

theorem IsAlt.ortho_comm (H : B₁.IsAlt) {x y : M₁} : IsOrtho B₁ x y ↔ IsOrtho B₁ y x :=
  LinearMap.IsAlt.ortho_comm H

theorem IsSymm.ortho_comm (H : B.IsSymm) {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  LinearMap.IsSymm.ortho_comm (isSymm_iff.1 H)

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`BilinForm.IsOrtho` -/
def iIsOrtho {n : Type w} (B : BilinForm R M) (v : n → M) : Prop :=
  B.IsOrthoᵢ v

theorem iIsOrtho_def {n : Type w} {B : BilinForm R M} {v : n → M} :
    B.iIsOrtho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl

section

variable {R₄ M₄ : Type*} [CommRing R₄] [IsDomain R₄]
variable [AddCommGroup M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}

@[simp]
theorem isOrtho_smul_left {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G (a • x) y ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a ↦ (ha a).elim

@[simp]
theorem isOrtho_smul_right {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G x (a • y) ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a ↦ (ha a).elim

/-- A set of orthogonal vectors `v` with respect to some bilinear form `B` is linearly independent
  if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem linearIndependent_of_iIsOrtho {n : Type w} {B : BilinForm K V} {v : n → V}
    (hv₁ : B.iIsOrtho v) (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K v := by
  classical
    rw [linearIndependent_iff']
    intro s w hs i hi
    have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
    have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j _ hij
      rw [iIsOrtho_def.1 hv₁ _ _ hij, mul_zero]
    simp_rw [sum_left, smul_left, hsum] at this
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this

end

section Orthogonal

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B y x = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "right" orthogonal complement one could define a "left" orthogonal
complement for which, for all `y` in `N`, `B x y = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M where
  carrier := { m | ∀ n ∈ N, IsOrtho B n m }
  zero_mem' x _ := isOrtho_zero_right x
  add_mem' {x y} hx hy n hn := by
    rw [IsOrtho, add_right, show B n x = 0 from hx n hn, show B n y = 0 from hy n hn, zero_add]
  smul_mem' c x hx n hn := by
    rw [IsOrtho, smul_right, show B n x = 0 from hx n hn, mul_zero]

variable {N L : Submodule R M}

@[simp]
theorem mem_orthogonal_iff {N : Submodule R M} {m : M} :
    m ∈ B.orthogonal N ↔ ∀ n ∈ N, IsOrtho B n m :=
  Iff.rfl

@[simp] lemma orthogonal_bot : B.orthogonal ⊥ = ⊤ := by ext; simp [IsOrtho]

theorem orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N := fun _ hn l hl => hn l (h hl)

theorem le_orthogonal_orthogonal (b : B.IsRefl) : N ≤ B.orthogonal (B.orthogonal N) :=
  fun n hn _ hm => b _ _ (hm n hn)

lemma orthogonal_top_eq_ker (hB : B.IsRefl) :
    B.orthogonal ⊤ = LinearMap.ker B := by
  ext; simp [LinearMap.BilinForm.IsOrtho, LinearMap.ext_iff, hB.eq_iff]

lemma orthogonal_top_eq_bot (hB : B.Nondegenerate) (hB₀ : B.IsRefl) :
    B.orthogonal ⊤ = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hx ↦ hB _ fun y ↦ hB₀ _ _ <| hx y Submodule.mem_top

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊓ B.orthogonal (K ∙ x) = ⊥ := by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h => ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  have := h.2 x ?_
  · rw [Finset.sum_singleton] at this ⊢
    suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
    change B x (μ x • x) = 0 at this
    rw [smul_right] at this
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero hx this
  · rw [Submodule.mem_span]
    exact fun _ hp => hp <| Finset.mem_singleton_self _

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K ∙ x) = LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ B x) := by
  ext y
  simp_rw [mem_orthogonal_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [IsOrtho, smul_left, mul_eq_zero]
    exact Or.intro_right _ h

theorem span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊔ B.orthogonal (K ∙ x) = ⊤ := by
  rw [orthogonal_span_singleton_eq_toLin_ker]
  exact LinearMap.span_singleton_sup_ker_eq_top _ hx

/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K ∙ x) (B.orthogonal <| K ∙ x) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

variable {M₂' : Type*}
variable [AddCommMonoid M₂'] [Module R M₂']

/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `Disjoint W (B.orthogonal W)`. -/
theorem nondegenerate_restrict_of_disjoint_orthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl)
    {W : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) : (B.restrict W).Nondegenerate := by
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R₁]
  refine hW.le_bot ⟨hx, fun y hy => ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp only [restrict_apply, domRestrict_apply] at b₁
  exact isOrtho_def.mpr (b x y b₁)

/-- An orthogonal basis with respect to a nondegenerate bilinear form has no self-orthogonal
elements. -/
theorem iIsOrtho.not_isOrtho_basis_self_of_nondegenerate {n : Type w} [Nontrivial R]
    {B : BilinForm R M} {v : Basis n R M} (h : B.iIsOrtho v) (hB : B.Nondegenerate) (i : n) :
    ¬B.IsOrtho (v i) (v i) := by
  intro ho
  refine v.ne_zero i (hB (v i) fun m => ?_)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, sum_right]
  apply Finset.sum_eq_zero
  rintro j -
  rw [smul_right]
  convert mul_zero (vi j) using 2
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
iff the basis has no elements which are self-orthogonal. -/
theorem iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self {n : Type w} [Nontrivial R]
    [NoZeroDivisors R] (B : BilinForm R M) (v : Basis n R M) (hO : B.iIsOrtho v) :
    B.Nondegenerate ↔ ∀ i, ¬B.IsOrtho (v i) (v i) := by
  refine ⟨hO.not_isOrtho_basis_self_of_nondegenerate, fun ho m hB => ?_⟩
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, sum_left,
           smul_left] at hB
  rw [Finset.sum_eq_single i] at hB
  · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (ho i) hB
  · intro j _ hij
    convert mul_zero (vi j) using 2
    exact hO hij
  · intro hi
    convert zero_mul (M₀ := R) _ using 2
    exact Finsupp.notMem_support_iff.mp hi

section

theorem toLin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V) (W : Subspace K V) (b : B.IsRefl) :
    (LinearMap.ker <| B.domRestrict W).map W.subtype = (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    constructor
    · simp [hx]
    · intro y _
      rw [IsOrtho, b]
      change (B.domRestrict W) ⟨x, hx⟩ y = 0
      rw [hker]
      rfl
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    ext y
    change B x y = 0
    rw [b]
    exact hx.2 _ Submodule.mem_top

theorem toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V)
    (W : Subspace K V) :
    (LinearMap.range (B.domRestrict W)).dualCoannihilator = B.orthogonal W := by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hx (B.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw

lemma ker_restrict_eq_of_codisjoint {p q : Submodule R M} (hpq : Codisjoint p q)
    {B : LinearMap.BilinForm R M} (hB : ∀ x ∈ p, ∀ y ∈ q, B x y = 0) :
    LinearMap.ker (B.restrict p) = (LinearMap.ker B).comap p.subtype := by
  ext ⟨z, hz⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hpq w
    simpa [hB z hz y hy] using LinearMap.congr_fun h ⟨x, hx⟩
  · ext ⟨x, hx⟩
    simpa using LinearMap.congr_fun h x

lemma inf_orthogonal_self_le_ker_restrict {W : Submodule R M} (b₁ : B.IsRefl) :
    W ⊓ B.orthogonal W ≤ (LinearMap.ker <| B.restrict W).map W.subtype := by
  rintro v ⟨hv : v ∈ W, hv' : v ∈ B.orthogonal W⟩
  simp only [Submodule.mem_map, mem_ker, restrict_apply, Submodule.coe_subtype, Subtype.exists,
    exists_and_left, exists_prop, exists_eq_right_right]
  refine ⟨?_, hv⟩
  ext ⟨w, hw⟩
  exact b₁ w v <| hv' w hw

variable [FiniteDimensional K V]

open Module Submodule

variable {B : BilinForm K V}

theorem finrank_add_finrank_orthogonal (b₁ : B.IsRefl) (W : Submodule K V) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  rw [← toLin_restrict_ker_eq_inf_orthogonal _ _ b₁, ←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W)),
      add_comm, ← add_assoc, add_comm (finrank K (LinearMap.ker (B.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]

lemma finrank_orthogonal (hB : B.Nondegenerate) (hB₀ : B.IsRefl) (W : Submodule K V) :
    finrank K (B.orthogonal W) = finrank K V - finrank K W := by
  have := finrank_add_finrank_orthogonal hB₀ (W := W)
  rw [B.orthogonal_top_eq_bot hB hB₀, inf_bot_eq, finrank_bot, add_zero] at this
  cutsat

lemma orthogonal_orthogonal (hB : B.Nondegenerate) (hB₀ : B.IsRefl) (W : Submodule K V) :
    B.orthogonal (B.orthogonal W) = W := by
  apply (eq_of_le_of_finrank_le (LinearMap.BilinForm.le_orthogonal_orthogonal hB₀) _).symm
  simp only [finrank_orthogonal hB hB₀]
  omega

variable {W : Submodule K V}

lemma isCompl_orthogonal_iff_disjoint (hB₀ : B.IsRefl) :
    IsCompl W (B.orthogonal W) ↔ Disjoint W (B.orthogonal W) := by
  refine ⟨IsCompl.disjoint, fun h ↦ ⟨h, ?_⟩⟩
  rw [codisjoint_iff]
  apply (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  calc
    finrank K V ≤ finrank K V + finrank K ↥(W ⊓ B.orthogonal ⊤) := le_self_add
    _ ≤ finrank K ↥(W ⊔ B.orthogonal W) + finrank K ↥(W ⊓ B.orthogonal W) := ?_
    _ ≤ finrank K ↥(W ⊔ B.orthogonal W) := by simp [h.eq_bot]
  rw [finrank_sup_add_finrank_inf_eq, finrank_add_finrank_orthogonal hB₀ W]

/-- A subspace is complement to its orthogonal complement with respect to some
reflexive bilinear form if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem isCompl_orthogonal_of_restrict_nondegenerate
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    refine Subtype.mk_eq_mk.1 (b₂ ⟨x, hx₁⟩ ?_)
    rintro ⟨n, hn⟩
    simp only [restrict_apply, domRestrict_apply]
    exact b₁ n x (b₁ x n (b₁ n x (hx₂ n hn)))
  refine IsCompl.of_eq this (eq_top_of_finrank_eq <| (finrank_le _).antisymm ?_)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K V, ← this, finrank_sup_add_finrank_inf_eq,
    finrank_add_finrank_orthogonal b₁]
  exact le_self_add

/-- A subspace is complement to its orthogonal complement with respect to some reflexive bilinear
form if and only if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_iff_isCompl_orthogonal
    (b₁ : B.IsRefl) : (B.restrict W).Nondegenerate ↔ IsCompl W (B.orthogonal W) :=
  ⟨fun b₂ => isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂, fun h =>
    B.nondegenerate_restrict_of_disjoint_orthogonal b₁ h.1⟩

lemma orthogonal_eq_top_iff (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) :
    B.orthogonal W = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).inf_eq_bot
  rwa [h, inf_top_eq] at this

lemma eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) (b₃ : B.orthogonal W = ⊥) :
    W = ⊤ := by
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).sup_eq_top
  rwa [b₃, sup_bot_eq] at this

lemma orthogonal_eq_bot_iff
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) (b₃ : B.Nondegenerate) :
    B.orthogonal W = ⊥ ↔ W = ⊤ := by
  refine ⟨eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot b₁ b₂, fun h ↦ ?_⟩
  rw [h, eq_bot_iff]
  exact fun x hx ↦ b₃ x fun y ↦ b₁ y x <| by simpa using hx y

end

/-! We note that we cannot use `BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` for the
lemma below since the below lemma does not require `V` to be finite dimensional. However,
`BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` does not require `B` to be nondegenerate
on the whole space. -/


/-- The restriction of a reflexive, non-degenerate bilinear form on the orthogonal complement of
the span of a singleton is also non-degenerate. -/
theorem restrict_nondegenerate_orthogonal_spanSingleton (B : BilinForm K V) (b₁ : B.Nondegenerate)
    (b₂ : B.IsRefl) {x : V} (hx : ¬B.IsOrtho x x) :
    Nondegenerate <| B.restrict <| B.orthogonal (K ∙ x) := by
  refine fun m hm => Submodule.coe_eq_zero.1 (b₁ m.1 fun n => ?_)
  have : n ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  rcases Submodule.mem_sup.1 this with ⟨y, hy, z, hz, rfl⟩
  specialize hm ⟨z, hz⟩
  rw [restrict] at hm
  erw [add_right, show B m.1 y = 0 by rw [b₂]; exact m.2 y hy, hm, add_zero]

end BilinForm

end LinearMap
