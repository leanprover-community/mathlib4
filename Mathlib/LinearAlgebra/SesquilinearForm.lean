/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import Mathlib.Algebra.Module.LinearMap
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.RingTheory.NonZeroDivisors

#align_import linear_algebra.sesquilinear_form from "leanprover-community/mathlib"@"87c54600fe3cdc7d32ff5b50873ac724d86aef8d"

/-!
# Sesquilinear form

This files provides properties about sesquilinear forms. The maps considered are of the form
`M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁` and `M₂` is a module over `R₂`.
Sesquilinear forms are the special case that `M₁ = M₂`, `R₁ = R₂ = R`, and `I₁ = RingHom.id R`.
Taking additionally `I₂ = RingHom.id R`, then one obtains bilinear forms.

These forms are a special case of the bilinear maps defined in `BilinearMap.lean` and all basic
lemmas about construction and elementary calculations are found there.

## Main declarations

* `IsOrtho`: states that two vectors are orthogonal with respect to a sesquilinear form
* `IsSymm`, `IsAlt`: states that a sesquilinear form is symmetric and alternating, respectively
* `orthogonalBilin`: provides the orthogonal complement with respect to sesquilinear form

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/


open BigOperators

variable {R R₁ R₂ R₃ M M₁ M₂ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

namespace LinearMap

/-! ### Orthogonal vectors -/


section CommRing

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] [CommSemiring R₂]
  [AddCommMonoid M₂] [Module R₂ M₂] {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def IsOrtho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x : M₁) (y : M₂) : Prop :=
  B x y = 0
#align linear_map.is_ortho LinearMap.IsOrtho

theorem isOrtho_def {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} {x y} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl
#align linear_map.is_ortho_def LinearMap.isOrtho_def

theorem isOrtho_zero_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x) : IsOrtho B (0 : M₁) x := by
  dsimp only [IsOrtho]
  -- ⊢ ↑(↑B 0) x = 0
  rw [map_zero B, zero_apply]
  -- 🎉 no goals
#align linear_map.is_ortho_zero_left LinearMap.isOrtho_zero_left

theorem isOrtho_zero_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x) : IsOrtho B x (0 : M₂) :=
  map_zero (B x)
#align linear_map.is_ortho_zero_right LinearMap.isOrtho_zero_right

theorem isOrtho_flip {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R} {x y} : B.IsOrtho x y ↔ B.flip.IsOrtho y x := by
  simp_rw [isOrtho_def, flip_apply]
  -- 🎉 no goals
#align linear_map.is_ortho_flip LinearMap.isOrtho_flip

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`BilinForm.isOrtho` -/
def IsOrthoᵢ (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R) (v : n → M₁) : Prop :=
  Pairwise (B.IsOrtho on v)
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho LinearMap.IsOrthoᵢ

theorem isOrthoᵢ_def {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R} {v : n → M₁} :
    B.IsOrthoᵢ v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho_def LinearMap.isOrthoᵢ_def

theorem isOrthoᵢ_flip (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R) {v : n → M₁} :
    B.IsOrthoᵢ v ↔ B.flip.IsOrthoᵢ v := by
  simp_rw [isOrthoᵢ_def]
  -- ⊢ (∀ (i j : n), i ≠ j → ↑(↑B (v i)) (v j) = 0) ↔ ∀ (i j : n), i ≠ j → ↑(↑(flip …
  constructor <;> intro h i j hij
  -- ⊢ (∀ (i j : n), i ≠ j → ↑(↑B (v i)) (v j) = 0) → ∀ (i j : n), i ≠ j → ↑(↑(flip …
                  -- ⊢ ↑(↑(flip B) (v i)) (v j) = 0
                  -- ⊢ ↑(↑B (v i)) (v j) = 0
  · rw [flip_apply]
    -- ⊢ ↑(↑B (v j)) (v i) = 0
    exact h j i (Ne.symm hij)
    -- 🎉 no goals
  simp_rw [flip_apply] at h
  -- ⊢ ↑(↑B (v i)) (v j) = 0
  exact h j i (Ne.symm hij)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho_flip LinearMap.isOrthoᵢ_flip

end CommRing

section Field

variable [Field K] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁] [Field K₂] [AddCommGroup V₂]
  [Module K₂ V₂] {I₁ : K₁ →+* K} {I₂ : K₂ →+* K} {I₁' : K₁ →+* K} {J₁ : K →+* K} {J₂ : K →+* K}

-- todo: this also holds for [CommRing R] [IsDomain R] when J₁ is invertible
theorem ortho_smul_left {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] K} {x y} {a : K₁} (ha : a ≠ 0) :
    IsOrtho B x y ↔ IsOrtho B (a • x) y := by
  dsimp only [IsOrtho]
  -- ⊢ ↑(↑B x) y = 0 ↔ ↑(↑B (a • x)) y = 0
  constructor <;> intro H
  -- ⊢ ↑(↑B x) y = 0 → ↑(↑B (a • x)) y = 0
                  -- ⊢ ↑(↑B (a • x)) y = 0
                  -- ⊢ ↑(↑B x) y = 0
  · rw [map_smulₛₗ₂, H, smul_zero]
    -- 🎉 no goals
  · rw [map_smulₛₗ₂, smul_eq_zero] at H
    -- ⊢ ↑(↑B x) y = 0
    cases' H with H H
    -- ⊢ ↑(↑B x) y = 0
    · rw [map_eq_zero I₁] at H
      -- ⊢ ↑(↑B x) y = 0
      trivial
      -- 🎉 no goals
    · exact H
      -- 🎉 no goals
#align linear_map.ortho_smul_left LinearMap.ortho_smul_left

-- todo: this also holds for [CommRing R] [IsDomain R] when J₂ is invertible
theorem ortho_smul_right {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] K} {x y} {a : K₂} {ha : a ≠ 0} :
    IsOrtho B x y ↔ IsOrtho B x (a • y) := by
  dsimp only [IsOrtho]
  -- ⊢ ↑(↑B x) y = 0 ↔ ↑(↑B x) (a • y) = 0
  constructor <;> intro H
  -- ⊢ ↑(↑B x) y = 0 → ↑(↑B x) (a • y) = 0
                  -- ⊢ ↑(↑B x) (a • y) = 0
                  -- ⊢ ↑(↑B x) y = 0
  · rw [map_smulₛₗ, H, smul_zero]
    -- 🎉 no goals
  · rw [map_smulₛₗ, smul_eq_zero] at H
    -- ⊢ ↑(↑B x) y = 0
    cases' H with H H
    -- ⊢ ↑(↑B x) y = 0
    · simp at H
      -- ⊢ ↑(↑B x) y = 0
      exfalso
      -- ⊢ False
      exact ha H
      -- 🎉 no goals
    · exact H
      -- 🎉 no goals
#align linear_map.ortho_smul_right LinearMap.ortho_smul_right

/-- A set of orthogonal vectors `v` with respect to some sesquilinear form `B` is linearly
  independent if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem linearIndependent_of_isOrthoᵢ {B : V₁ →ₛₗ[I₁] V₁ →ₛₗ[I₁'] K} {v : n → V₁}
    (hv₁ : B.IsOrthoᵢ v) (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K₁ v := by
  classical
    rw [linearIndependent_iff']
    intro s w hs i hi
    have : B (s.sum fun i : n ↦ w i • v i) (v i) = 0 := by rw [hs, map_zero, zero_apply]
    have hsum : (s.sum fun j : n ↦ I₁ (w j) * B (v j) (v i)) = I₁ (w i) * B (v i) (v i) := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j _hj hij
      rw [isOrthoᵢ_def.1 hv₁ _ _ hij, mul_zero]
    simp_rw [B.map_sum₂, map_smulₛₗ₂, smul_eq_mul, hsum] at this
    apply (map_eq_zero I₁).mp
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this
set_option linter.uppercaseLean3 false in
#align linear_map.linear_independent_of_is_Ortho LinearMap.linearIndependent_of_isOrthoᵢ

end Field

/-! ### Reflexive bilinear forms -/


section Reflexive

variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] {I₁ : R₁ →+* R}
  {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R}

/-- The proposition that a sesquilinear form is reflexive -/
def IsRefl (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Prop :=
  ∀ x y, B x y = 0 → B y x = 0
#align linear_map.is_refl LinearMap.IsRefl

namespace IsRefl

variable (H : B.IsRefl)

theorem eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := fun {x y} ↦ H x y
#align linear_map.is_refl.eq_zero LinearMap.IsRefl.eq_zero

theorem ortho_comm {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩
#align linear_map.is_refl.ortho_comm LinearMap.IsRefl.ortho_comm

theorem domRestrict (H : B.IsRefl) (p : Submodule R₁ M₁) : (B.domRestrict₁₂ p p).IsRefl :=
  fun _ _ ↦ by
  simp_rw [domRestrict₁₂_apply]
  -- ⊢ ↑(↑B ↑x✝¹) ↑x✝ = 0 → ↑(↑B ↑x✝) ↑x✝¹ = 0
  exact H _ _
  -- 🎉 no goals
#align linear_map.is_refl.dom_restrict_refl LinearMap.IsRefl.domRestrict

@[simp]
theorem flip_isRefl_iff : B.flip.IsRefl ↔ B.IsRefl :=
  ⟨fun h x y H ↦ h y x ((B.flip_apply _ _).trans H), fun h x y ↦ h y x⟩
#align linear_map.is_refl.flip_is_refl_iff LinearMap.IsRefl.flip_isRefl_iff

theorem ker_flip_eq_bot (H : B.IsRefl) (h : LinearMap.ker B = ⊥) : LinearMap.ker B.flip = ⊥ := by
  refine' ker_eq_bot'.mpr fun _ hx ↦ ker_eq_bot'.mp h _ _
  -- ⊢ ↑B x✝ = 0
  ext
  -- ⊢ ↑(↑B x✝¹) x✝ = ↑0 x✝
  exact H _ _ (LinearMap.congr_fun hx _)
  -- 🎉 no goals
#align linear_map.is_refl.ker_flip_eq_bot LinearMap.IsRefl.ker_flip_eq_bot

theorem ker_eq_bot_iff_ker_flip_eq_bot (H : B.IsRefl) :
    LinearMap.ker B = ⊥ ↔ LinearMap.ker B.flip = ⊥ := by
  refine' ⟨ker_flip_eq_bot H, fun h ↦ _⟩
  -- ⊢ ker B = ⊥
  exact (congr_arg _ B.flip_flip.symm).trans (ker_flip_eq_bot (flip_isRefl_iff.mpr H) h)
  -- 🎉 no goals
#align linear_map.is_refl.ker_eq_bot_iff_ker_flip_eq_bot LinearMap.IsRefl.ker_eq_bot_iff_ker_flip_eq_bot

end IsRefl

end Reflexive

/-! ### Symmetric bilinear forms -/


section Symmetric

variable [CommSemiring R] [AddCommMonoid M] [Module R M] {I : R →+* R} {B : M →ₛₗ[I] M →ₗ[R] R}

/-- The proposition that a sesquilinear form is symmetric -/
def IsSymm (B : M →ₛₗ[I] M →ₗ[R] R) : Prop :=
  ∀ x y, I (B x y) = B y x
#align linear_map.is_symm LinearMap.IsSymm

namespace IsSymm

protected theorem eq (H : B.IsSymm) (x y) : I (B x y) = B y x :=
  H x y
#align linear_map.is_symm.eq LinearMap.IsSymm.eq

theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 ↦ by
  rw [← H.eq]
  -- ⊢ ↑I (↑(↑B x) y) = 0
  simp [H1]
  -- 🎉 no goals
#align linear_map.is_symm.is_refl LinearMap.IsSymm.isRefl

theorem ortho_comm (H : B.IsSymm) {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.isRefl.ortho_comm
#align linear_map.is_symm.ortho_comm LinearMap.IsSymm.ortho_comm

theorem domRestrict (H : B.IsSymm) (p : Submodule R M) : (B.domRestrict₁₂ p p).IsSymm :=
  fun _ _ ↦ by
  simp_rw [domRestrict₁₂_apply]
  -- ⊢ ↑I (↑(↑B ↑x✝¹) ↑x✝) = ↑(↑B ↑x✝) ↑x✝¹
  exact H _ _
  -- 🎉 no goals
#align linear_map.is_symm.dom_restrict_symm LinearMap.IsSymm.domRestrict

end IsSymm

theorem isSymm_iff_eq_flip {B : M →ₗ[R] M →ₗ[R] R} : B.IsSymm ↔ B = B.flip := by
  constructor <;> intro h
  -- ⊢ IsSymm B → B = flip B
                  -- ⊢ B = flip B
                  -- ⊢ IsSymm B
  · ext
    -- ⊢ ↑(↑B x✝¹) x✝ = ↑(↑(flip B) x✝¹) x✝
    rw [← h, flip_apply, RingHom.id_apply]
    -- 🎉 no goals
  intro x y
  -- ⊢ ↑(RingHom.id R) (↑(↑B x) y) = ↑(↑B y) x
  conv_lhs => rw [h]
  -- 🎉 no goals
#align linear_map.is_symm_iff_eq_flip LinearMap.isSymm_iff_eq_flip

end Symmetric

/-! ### Alternating bilinear forms -/


section Alternating

variable [CommRing R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] {I₁ : R₁ →+* R}
  {I₂ : R₁ →+* R} {I : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R}

/-- The proposition that a sesquilinear form is alternating -/
def IsAlt (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Prop :=
  ∀ x, B x x = 0
#align linear_map.is_alt LinearMap.IsAlt

namespace IsAlt

variable (H : B.IsAlt)

theorem self_eq_zero (x : M₁) : B x x = 0 :=
  H x
#align linear_map.is_alt.self_eq_zero LinearMap.IsAlt.self_eq_zero

theorem neg (x y : M₁) : -B x y = B y x := by
  have H1 : B (y + x) (y + x) = 0 := self_eq_zero H (y + x)
  -- ⊢ -↑(↑B x) y = ↑(↑B y) x
  simp [map_add, self_eq_zero H] at H1
  -- ⊢ -↑(↑B x) y = ↑(↑B y) x
  rw [add_eq_zero_iff_neg_eq] at H1
  -- ⊢ -↑(↑B x) y = ↑(↑B y) x
  exact H1
  -- 🎉 no goals
#align linear_map.is_alt.neg LinearMap.IsAlt.neg

theorem isRefl : B.IsRefl := by
  intro x y h
  -- ⊢ ↑(↑B y) x = 0
  rw [← neg H, h, neg_zero]
  -- 🎉 no goals
#align linear_map.is_alt.is_refl LinearMap.IsAlt.isRefl

theorem ortho_comm {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.isRefl.ortho_comm
#align linear_map.is_alt.ortho_comm LinearMap.IsAlt.ortho_comm

end IsAlt

theorem isAlt_iff_eq_neg_flip [NoZeroDivisors R] [CharZero R] {B : M₁ →ₛₗ[I] M₁ →ₛₗ[I] R} :
    B.IsAlt ↔ B = -B.flip := by
  constructor <;> intro h
  -- ⊢ IsAlt B → B = -flip B
                  -- ⊢ B = -flip B
                  -- ⊢ IsAlt B
  · ext
    -- ⊢ ↑(↑B x✝¹) x✝ = ↑(↑(-flip B) x✝¹) x✝
    simp_rw [neg_apply, flip_apply]
    -- ⊢ ↑(↑B x✝¹) x✝ = -↑(↑B x✝) x✝¹
    exact (h.neg _ _).symm
    -- 🎉 no goals
  intro x
  -- ⊢ ↑(↑B x) x = 0
  let h' := congr_fun₂ h x x
  -- ⊢ ↑(↑B x) x = 0
  simp only [neg_apply, flip_apply, ← add_eq_zero_iff_eq_neg] at h'
  -- ⊢ ↑(↑B x) x = 0
  exact add_self_eq_zero.mp h'
  -- 🎉 no goals
#align linear_map.is_alt_iff_eq_neg_flip LinearMap.isAlt_iff_eq_neg_flip

end Alternating

end LinearMap

namespace Submodule

/-! ### The orthogonal complement -/

variable [CommRing R] [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R}
  {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R}

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonalBilin (N : Submodule R₁ M₁) (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Submodule R₁ M₁
    where
  carrier := { m | ∀ n ∈ N, B.IsOrtho n m }
  zero_mem' x _ := B.isOrtho_zero_right x
  add_mem' hx hy n hn := by
    rw [LinearMap.IsOrtho, map_add, show B n _ = 0 from hx n hn, show B n _ = 0 from hy n hn,
      zero_add]
  smul_mem' c x hx n hn := by
    rw [LinearMap.IsOrtho, LinearMap.map_smulₛₗ, show B n x = 0 from hx n hn, smul_zero]
    -- 🎉 no goals
#align submodule.orthogonal_bilin Submodule.orthogonalBilin

variable {N L : Submodule R₁ M₁}

@[simp]
theorem mem_orthogonalBilin_iff {m : M₁} : m ∈ N.orthogonalBilin B ↔ ∀ n ∈ N, B.IsOrtho n m :=
  Iff.rfl
#align submodule.mem_orthogonal_bilin_iff Submodule.mem_orthogonalBilin_iff

theorem orthogonalBilin_le (h : N ≤ L) : L.orthogonalBilin B ≤ N.orthogonalBilin B :=
  fun _ hn l hl ↦ hn l (h hl)
#align submodule.orthogonal_bilin_le Submodule.orthogonalBilin_le

theorem le_orthogonalBilin_orthogonalBilin (b : B.IsRefl) :
    N ≤ (N.orthogonalBilin B).orthogonalBilin B := fun n hn _m hm ↦ b _ _ (hm n hn)
#align submodule.le_orthogonal_bilin_orthogonal_bilin Submodule.le_orthogonalBilin_orthogonalBilin

end Submodule

namespace LinearMap

section Orthogonal

variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  {J : K →+* K} {J₁ : K₁ →+* K} {J₁' : K₁ →+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot (B : V₁ →ₛₗ[J₁] V₁ →ₛₗ[J₁'] K) (x : V₁)
    (hx : ¬B.IsOrtho x x) : (K₁ ∙ x) ⊓ Submodule.orthogonalBilin (K₁ ∙ x) B = ⊥ := by
  rw [← Finset.coe_singleton]
  -- ⊢ Submodule.span K₁ ↑{x} ⊓ Submodule.orthogonalBilin (Submodule.span K₁ ↑{x})  …
  refine' eq_bot_iff.2 fun y h ↦ _
  -- ⊢ y ∈ ⊥
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩
  -- ⊢ ∑ i in {x}, μ i • i ∈ ⊥
  replace h := h.2 x (by simp [Submodule.mem_span] : x ∈ Submodule.span K₁ ({x} : Finset V₁))
  -- ⊢ ∑ i in {x}, μ i • i ∈ ⊥
  rw [Finset.sum_singleton] at h ⊢
  -- ⊢ μ x • x ∈ ⊥
  suffices hμzero : μ x = 0
  -- ⊢ μ x • x ∈ ⊥
  · rw [hμzero, zero_smul, Submodule.mem_bot]
    -- 🎉 no goals
  rw [isOrtho_def, map_smulₛₗ, smul_eq_mul] at h
  -- ⊢ μ x = 0
  exact Or.elim (zero_eq_mul.mp h.symm)
      (fun y ↦ by simpa using y)
      (fun hfalse ↦ False.elim $ hx hfalse)
#align linear_map.span_singleton_inf_orthogonal_eq_bot LinearMap.span_singleton_inf_orthogonal_eq_bot

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_to_lin_ker {B : V →ₗ[K] V →ₛₗ[J] K} (x : V) :
    Submodule.orthogonalBilin (K ∙ x) B = LinearMap.ker (B x) := by
  ext y
  -- ⊢ y ∈ Submodule.orthogonalBilin (Submodule.span K {x}) B ↔ y ∈ ker (↑B x)
  simp_rw [Submodule.mem_orthogonalBilin_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  -- ⊢ (∀ (n : V), (∃ a, a • x = n) → IsOrtho B n y) ↔ ↑(↑B x) y = 0
  constructor
  -- ⊢ (∀ (n : V), (∃ a, a • x = n) → IsOrtho B n y) → ↑(↑B x) y = 0
  · exact fun h ↦ h x ⟨1, one_smul _ _⟩
    -- 🎉 no goals
  · rintro h _ ⟨z, rfl⟩
    -- ⊢ IsOrtho B (z • x) y
    rw [isOrtho_def, map_smulₛₗ₂, smul_eq_zero]
    -- ⊢ ↑(RingHom.id K) z = 0 ∨ ↑(↑B x) y = 0
    exact Or.intro_right _ h
    -- 🎉 no goals
#align linear_map.orthogonal_span_singleton_eq_to_lin_ker LinearMap.orthogonal_span_singleton_eq_to_lin_ker

-- todo: Generalize this to sesquilinear maps
theorem span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊔ @Submodule.orthogonalBilin _ _ _ _ _ _ (_) _ _ (K ∙ x) B = ⊤ := by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  -- ⊢ Submodule.span K {x} ⊔ ker (↑B x) = ⊤
  exact (B x).span_singleton_sup_ker_eq_top hx
  -- 🎉 no goals
#align linear_map.span_singleton_sup_orthogonal_eq_top LinearMap.span_singleton_sup_orthogonal_eq_top

-- todo: Generalize this to sesquilinear maps
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem isCompl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K ∙ x) (@Submodule.orthogonalBilin _ _ _ _ _ _ (_) _ _ (K ∙ x) B) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }
#align linear_map.is_compl_span_singleton_orthogonal LinearMap.isCompl_span_singleton_orthogonal

end Orthogonal

/-! ### Adjoint pairs -/


section AdjointPair

section AddCommMonoid

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M]

variable [AddCommMonoid M₁] [Module R M₁]

variable [AddCommMonoid M₂] [Module R M₂]

variable {I : R →+* R}

variable {B F : M →ₗ[R] M →ₛₗ[I] R} {B' : M₁ →ₗ[R] M₁ →ₛₗ[I] R} {B'' : M₂ →ₗ[R] M₂ →ₛₗ[I] R}

variable {f f' : M →ₗ[R] M₁} {g g' : M₁ →ₗ[R] M}

variable (B B' f g)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def IsAdjointPair :=
  ∀ x y, B' (f x) y = B x (g y)
#align linear_map.is_adjoint_pair LinearMap.IsAdjointPair

variable {B B' f g}

theorem isAdjointPair_iff_comp_eq_compl₂ : IsAdjointPair B B' f g ↔ B'.comp f = B.compl₂ g := by
  constructor <;> intro h
  -- ⊢ IsAdjointPair B B' f g → comp B' f = compl₂ B g
                  -- ⊢ comp B' f = compl₂ B g
                  -- ⊢ IsAdjointPair B B' f g
  · ext x y
    -- ⊢ ↑(↑(comp B' f) x) y = ↑(↑(compl₂ B g) x) y
    rw [comp_apply, compl₂_apply]
    -- ⊢ ↑(↑B' (↑f x)) y = ↑(↑B x) (↑g y)
    exact h x y
    -- 🎉 no goals
  · intro _ _
    -- ⊢ ↑(↑B' (↑f x✝)) y✝ = ↑(↑B x✝) (↑g y✝)
    rw [← compl₂_apply, ← comp_apply, h]
    -- 🎉 no goals
#align linear_map.is_adjoint_pair_iff_comp_eq_compl₂ LinearMap.isAdjointPair_iff_comp_eq_compl₂

theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun _ _ ↦ by simp only [zero_apply, map_zero]
                                                                    -- 🎉 no goals
#align linear_map.is_adjoint_pair_zero LinearMap.isAdjointPair_zero

theorem isAdjointPair_id : IsAdjointPair B B 1 1 := fun _ _ ↦ rfl
#align linear_map.is_adjoint_pair_id LinearMap.isAdjointPair_id

theorem IsAdjointPair.add (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x _ ↦ by
  rw [f.add_apply, g.add_apply, B'.map_add₂, (B x).map_add, h, h']
  -- 🎉 no goals
#align linear_map.is_adjoint_pair.add LinearMap.IsAdjointPair.add

theorem IsAdjointPair.comp {f' : M₁ →ₗ[R] M₂} {g' : M₂ →ₗ[R] M₁} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B' B'' f' g') : IsAdjointPair B B'' (f'.comp f) (g.comp g') := fun _ _ ↦ by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h', h]
  -- 🎉 no goals
#align linear_map.is_adjoint_pair.comp LinearMap.IsAdjointPair.comp

theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) :=
  h'.comp h
#align linear_map.is_adjoint_pair.mul LinearMap.IsAdjointPair.mul

end AddCommMonoid

section AddCommGroup

variable [CommRing R]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup M₁] [Module R M₁]

variable {B F : M →ₗ[R] M →ₗ[R] R} {B' : M₁ →ₗ[R] M₁ →ₗ[R] R}

variable {f f' : M →ₗ[R] M₁} {g g' : M₁ →ₗ[R] M}

theorem IsAdjointPair.sub (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f - f') (g - g') := fun x _ ↦ by
  rw [f.sub_apply, g.sub_apply, B'.map_sub₂, (B x).map_sub, h, h']
  -- 🎉 no goals
#align linear_map.is_adjoint_pair.sub LinearMap.IsAdjointPair.sub

theorem IsAdjointPair.smul (c : R) (h : IsAdjointPair B B' f g) :
    IsAdjointPair B B' (c • f) (c • g) := fun _ _ ↦ by
  simp [h _]
  -- 🎉 no goals
#align linear_map.is_adjoint_pair.smul LinearMap.IsAdjointPair.smul

end AddCommGroup

end AdjointPair

/-! ### Self-adjoint pairs-/


section SelfadjointPair

section AddCommMonoid

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M]

variable {I : R →+* R}

variable (B F : M →ₗ[R] M →ₛₗ[I] R)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def IsPairSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B F f f
#align linear_map.is_pair_self_adjoint LinearMap.IsPairSelfAdjoint

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
protected def IsSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f f
#align linear_map.is_self_adjoint LinearMap.IsSelfAdjoint

end AddCommMonoid

section AddCommGroup

variable [CommRing R]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup M₁] [Module R M₁] (B F : M →ₗ[R] M →ₗ[R] R)

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where
  carrier := { f | IsPairSelfAdjoint B F f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c
#align linear_map.is_pair_self_adjoint_submodule LinearMap.isPairSelfAdjointSubmodule

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def IsSkewAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f (-f)
#align linear_map.is_skew_adjoint LinearMap.IsSkewAdjoint

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B B
#align linear_map.self_adjoint_submodule LinearMap.selfAdjointSubmodule

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B) B
#align linear_map.skew_adjoint_submodule LinearMap.skewAdjointSubmodule

variable {B F}

@[simp]
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R M) :
    f ∈ isPairSelfAdjointSubmodule B F ↔ IsPairSelfAdjoint B F f :=
  Iff.rfl
#align linear_map.mem_is_pair_self_adjoint_submodule LinearMap.mem_isPairSelfAdjointSubmodule

theorem isPairSelfAdjoint_equiv (e : M₁ ≃ₗ[R] M) (f : Module.End R M) :
    IsPairSelfAdjoint B F f ↔
      IsPairSelfAdjoint (B.compl₁₂ ↑e ↑e) (F.compl₁₂ ↑e ↑e) (e.symm.conj f) := by
  have hₗ :
    (F.compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M)).comp (e.symm.conj f) =
      (F.comp f).compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, coe_comp, LinearEquiv.coe_coe, compl₁₂_apply,
      LinearEquiv.apply_symm_apply, Function.comp_apply]
  have hᵣ :
    (B.compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M)).compl₂ (e.symm.conj f) =
      (B.compl₂ f).compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, compl₂_apply, coe_comp, LinearEquiv.coe_coe,
      compl₁₂_apply, LinearEquiv.apply_symm_apply, Function.comp_apply]
  have he : Function.Surjective (⇑(↑e : M₁ →ₗ[R] M) : M₁ → M) := e.surjective
  -- ⊢ IsPairSelfAdjoint B F f ↔ IsPairSelfAdjoint (compl₁₂ B ↑e ↑e) (compl₁₂ F ↑e  …
  simp_rw [IsPairSelfAdjoint, isAdjointPair_iff_comp_eq_compl₂, hₗ, hᵣ, compl₁₂_inj he he]
  -- 🎉 no goals
#align linear_map.is_pair_self_adjoint_equiv LinearMap.isPairSelfAdjoint_equiv

theorem isSkewAdjoint_iff_neg_self_adjoint (f : Module.End R M) :
    B.IsSkewAdjoint f ↔ IsAdjointPair (-B) B f f :=
  show (∀ x y, B (f x) y = B x ((-f) y)) ↔ ∀ x y, B (f x) y = (-B) x (f y) by simp
                                                                              -- 🎉 no goals
#align linear_map.is_skew_adjoint_iff_neg_self_adjoint LinearMap.isSkewAdjoint_iff_neg_self_adjoint

@[simp]
theorem mem_selfAdjointSubmodule (f : Module.End R M) :
    f ∈ B.selfAdjointSubmodule ↔ B.IsSelfAdjoint f :=
  Iff.rfl
#align linear_map.mem_self_adjoint_submodule LinearMap.mem_selfAdjointSubmodule

@[simp]
theorem mem_skewAdjointSubmodule (f : Module.End R M) :
    f ∈ B.skewAdjointSubmodule ↔ B.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  -- ⊢ f ∈ skewAdjointSubmodule B ↔ IsAdjointPair (-B) B f f
  exact Iff.rfl
  -- 🎉 no goals
#align linear_map.mem_skew_adjoint_submodule LinearMap.mem_skewAdjointSubmodule

end AddCommGroup

end SelfadjointPair

/-! ### Nondegenerate bilinear forms -/


section Nondegenerate

section CommSemiring

variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] [CommSemiring R₂]
  [AddCommMonoid M₂] [Module R₂ M₂] {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- A bilinear form is called left-separating if
the only element that is left-orthogonal to every other element is `0`; i.e.,
for every nonzero `x` in `M₁`, there exists `y` in `M₂` with `B x y ≠ 0`.-/
def SeparatingLeft (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop :=
  ∀ x : M₁, (∀ y : M₂, B x y = 0) → x = 0
#align linear_map.separating_left LinearMap.SeparatingLeft

variable (M₁ M₂ I₁ I₂)

/-- In a non-trivial module, zero is not non-degenerate. -/
theorem not_separatingLeft_zero [Nontrivial M₁] : ¬(0 : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R).SeparatingLeft :=
  let ⟨m, hm⟩ := exists_ne (0 : M₁)
  fun h ↦ hm (h m fun _n ↦ rfl)
#align linear_map.not_separating_left_zero LinearMap.not_separatingLeft_zero

variable {M₁ M₂ I₁ I₂}

theorem SeparatingLeft.ne_zero [Nontrivial M₁] {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R}
    (h : B.SeparatingLeft) : B ≠ 0 := fun h0 ↦ not_separatingLeft_zero M₁ M₂ I₁ I₂ <| h0 ▸ h
#align linear_map.separating_left.ne_zero LinearMap.SeparatingLeft.ne_zero

section Linear

variable [AddCommMonoid Mₗ₁] [AddCommMonoid Mₗ₂] [AddCommMonoid Mₗ₁'] [AddCommMonoid Mₗ₂']

variable [Module R Mₗ₁] [Module R Mₗ₂] [Module R Mₗ₁'] [Module R Mₗ₂']

variable {B : Mₗ₁ →ₗ[R] Mₗ₂ →ₗ[R] R} (e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂')

theorem SeparatingLeft.congr (h : B.SeparatingLeft) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R R)) B).SeparatingLeft := by
  intro x hx
  -- ⊢ x = 0
  rw [← e₁.symm.map_eq_zero_iff]
  -- ⊢ ↑(LinearEquiv.symm e₁) x = 0
  refine' h (e₁.symm x) fun y ↦ _
  -- ⊢ ↑(↑B (↑(LinearEquiv.symm e₁) x)) y = 0
  specialize hx (e₂ y)
  -- ⊢ ↑(↑B (↑(LinearEquiv.symm e₁) x)) y = 0
  simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_eq_zero_iff] at hx
  exact hx
  -- 🎉 no goals
#align linear_map.separating_left.congr LinearMap.SeparatingLeft.congr

@[simp]
theorem separatingLeft_congr_iff :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R R)) B).SeparatingLeft ↔ B.SeparatingLeft :=
  ⟨fun h ↦ by
    convert h.congr e₁.symm e₂.symm
    -- ⊢ B = ↑(LinearEquiv.arrowCongr (LinearEquiv.symm e₁) (LinearEquiv.arrowCongr ( …
    ext x y
    -- ⊢ ↑(↑B x) y = ↑(↑(↑(LinearEquiv.arrowCongr (LinearEquiv.symm e₁) (LinearEquiv. …
    simp,
    -- 🎉 no goals
   SeparatingLeft.congr e₁ e₂⟩
#align linear_map.separating_left_congr_iff LinearMap.separatingLeft_congr_iff

end Linear

/-- A bilinear form is called right-separating if
the only element that is right-orthogonal to every other element is `0`; i.e.,
for every nonzero `y` in `M₂`, there exists `x` in `M₁` with `B x y ≠ 0`.-/
def SeparatingRight (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop :=
  ∀ y : M₂, (∀ x : M₁, B x y = 0) → y = 0
#align linear_map.separating_right LinearMap.SeparatingRight

/-- A bilinear form is called non-degenerate if it is left-separating and right-separating. -/
def Nondegenerate (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop :=
  SeparatingLeft B ∧ SeparatingRight B
#align linear_map.nondegenerate LinearMap.Nondegenerate

@[simp]
theorem flip_separatingRight {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
    B.flip.SeparatingRight ↔ B.SeparatingLeft :=
  ⟨fun hB x hy ↦ hB x hy, fun hB x hy ↦ hB x hy⟩
#align linear_map.flip_separating_right LinearMap.flip_separatingRight

@[simp]
theorem flip_separatingLeft {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
    B.flip.SeparatingLeft ↔ SeparatingRight B := by rw [← flip_separatingRight, flip_flip]
                                                    -- 🎉 no goals
#align linear_map.flip_separating_left LinearMap.flip_separatingLeft

@[simp]
theorem flip_nondegenerate {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} : B.flip.Nondegenerate ↔ B.Nondegenerate :=
  Iff.trans and_comm (and_congr flip_separatingRight flip_separatingLeft)
#align linear_map.flip_nondegenerate LinearMap.flip_nondegenerate

theorem separatingLeft_iff_linear_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
    B.SeparatingLeft ↔ ∀ x : M₁, B x = 0 → x = 0 := by
  constructor <;> intro h x hB
  -- ⊢ SeparatingLeft B → ∀ (x : M₁), ↑B x = 0 → x = 0
                  -- ⊢ x = 0
                  -- ⊢ x = 0
  · simpa only [hB, zero_apply, eq_self_iff_true, forall_const] using h x
    -- 🎉 no goals
  have h' : B x = 0 := by
    ext
    rw [zero_apply]
    exact hB _
  exact h x h'
  -- 🎉 no goals
#align linear_map.separating_left_iff_linear_nontrivial LinearMap.separatingLeft_iff_linear_nontrivial

theorem separatingRight_iff_linear_flip_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
    B.SeparatingRight ↔ ∀ y : M₂, B.flip y = 0 → y = 0 := by
  rw [← flip_separatingLeft, separatingLeft_iff_linear_nontrivial]
  -- 🎉 no goals
#align linear_map.separating_right_iff_linear_flip_nontrivial LinearMap.separatingRight_iff_linear_flip_nontrivial

/-- A bilinear form is left-separating if and only if it has a trivial kernel. -/
theorem separatingLeft_iff_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
    B.SeparatingLeft ↔ LinearMap.ker B = ⊥ :=
  Iff.trans separatingLeft_iff_linear_nontrivial LinearMap.ker_eq_bot'.symm
#align linear_map.separating_left_iff_ker_eq_bot LinearMap.separatingLeft_iff_ker_eq_bot

/-- A bilinear form is right-separating if and only if its flip has a trivial kernel. -/
theorem separatingRight_iff_flip_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
    B.SeparatingRight ↔ LinearMap.ker B.flip = ⊥ := by
  rw [← flip_separatingLeft, separatingLeft_iff_ker_eq_bot]
  -- 🎉 no goals
#align linear_map.separating_right_iff_flip_ker_eq_bot LinearMap.separatingRight_iff_flip_ker_eq_bot

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] {I I' : R →+* R}

theorem IsRefl.nondegenerate_of_separatingLeft {B : M →ₗ[R] M →ₗ[R] R} (hB : B.IsRefl)
    (hB' : B.SeparatingLeft) : B.Nondegenerate := by
  refine' ⟨hB', _⟩
  -- ⊢ SeparatingRight B
  rw [separatingRight_iff_flip_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mp]
  -- ⊢ ker B = ⊥
  rwa [← separatingLeft_iff_ker_eq_bot]
  -- 🎉 no goals
#align linear_map.is_refl.nondegenerate_of_separating_left LinearMap.IsRefl.nondegenerate_of_separatingLeft

theorem IsRefl.nondegenerate_of_separatingRight {B : M →ₗ[R] M →ₗ[R] R} (hB : B.IsRefl)
    (hB' : B.SeparatingRight) : B.Nondegenerate := by
  refine' ⟨_, hB'⟩
  -- ⊢ SeparatingLeft B
  rw [separatingLeft_iff_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr]
  -- ⊢ ker (flip B) = ⊥
  rwa [← separatingRight_iff_flip_ker_eq_bot]
  -- 🎉 no goals
#align linear_map.is_refl.nondegenerate_of_separating_right LinearMap.IsRefl.nondegenerate_of_separatingRight

/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `Disjoint W (W.orthogonalBilin B)`. -/
theorem nondegenerateRestrictOfDisjointOrthogonal {B : M →ₗ[R] M →ₗ[R] R} (hB : B.IsRefl)
    {W : Submodule R M} (hW : Disjoint W (W.orthogonalBilin B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  refine' (hB.domRestrict W).nondegenerate_of_separatingLeft _
  -- ⊢ SeparatingLeft (domRestrict₁₂ B W W)
  rintro ⟨x, hx⟩ b₁
  -- ⊢ { val := x, property := hx } = 0
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R]
  -- ⊢ x ∈ ⊥
  refine' hW.le_bot ⟨hx, fun y hy ↦ _⟩
  -- ⊢ IsOrtho B y x
  specialize b₁ ⟨y, hy⟩
  -- ⊢ IsOrtho B y x
  simp_rw [domRestrict₁₂_apply] at b₁
  -- ⊢ IsOrtho B y x
  rw [hB.ortho_comm]
  -- ⊢ IsOrtho B x y
  exact b₁
  -- 🎉 no goals
#align linear_map.nondegenerate_restrict_of_disjoint_orthogonal LinearMap.nondegenerateRestrictOfDisjointOrthogonal

/-- An orthogonal basis with respect to a left-separating bilinear form has no self-orthogonal
elements. -/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft [Nontrivial R]
    {B : M →ₛₗ[I] M →ₛₗ[I'] R} {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingLeft)
    (i : n) : ¬B.IsOrtho (v i) (v i) := by
  intro ho
  -- ⊢ False
  refine' v.ne_zero i (hB (v i) fun m ↦ _)
  -- ⊢ ↑(↑B (↑v i)) m = 0
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  -- ⊢ ↑(↑B (↑v i)) (↑(LinearEquiv.symm v.repr) vi) = 0
  rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, map_sum]
  -- ⊢ ∑ i_1 in vi.support, ↑(↑B (↑v i)) (↑vi i_1 • ↑v i_1) = 0
  apply Finset.sum_eq_zero
  -- ⊢ ∀ (x : n), x ∈ vi.support → ↑(↑B (↑v i)) (↑vi x • ↑v x) = 0
  rintro j -
  -- ⊢ ↑(↑B (↑v i)) (↑vi j • ↑v j) = 0
  rw [map_smulₛₗ]
  -- ⊢ ↑I' (↑vi j) • ↑(↑B (↑v i)) (↑v j) = 0
  suffices : B (v i) (v j) = 0
  -- ⊢ ↑I' (↑vi j) • ↑(↑B (↑v i)) (↑v j) = 0
  · rw [this, smul_eq_mul, mul_zero]
    -- 🎉 no goals
  obtain rfl | hij := eq_or_ne i j
  -- ⊢ ↑(↑B (↑v i)) (↑v i) = 0
  · exact ho
    -- 🎉 no goals
  · exact h hij
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho.not_is_ortho_basis_self_of_separating_left LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft

/-- An orthogonal basis with respect to a right-separating bilinear form has no self-orthogonal
elements. -/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight [Nontrivial R]
    {B : M →ₛₗ[I] M →ₛₗ[I'] R} {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingRight)
    (i : n) : ¬B.IsOrtho (v i) (v i) := by
  rw [isOrthoᵢ_flip] at h
  -- ⊢ ¬IsOrtho B (↑v i) (↑v i)
  rw [isOrtho_flip]
  -- ⊢ ¬IsOrtho (flip B) (↑v i) (↑v i)
  exact h.not_isOrtho_basis_self_of_separatingLeft (flip_separatingLeft.mpr hB) i
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho.not_is_ortho_basis_self_of_separating_right LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is left-separating
if the basis has no elements which are self-orthogonal. -/
theorem IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self [NoZeroDivisors R] {B : M →ₗ[R] M →ₗ[R] R}
    (v : Basis n R M) (hO : B.IsOrthoᵢ v) (h : ∀ i, ¬B.IsOrtho (v i) (v i)) : B.SeparatingLeft := by
  intro m hB
  -- ⊢ m = 0
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  -- ⊢ ↑(LinearEquiv.symm v.repr) vi = 0
  rw [LinearEquiv.map_eq_zero_iff]
  -- ⊢ vi = 0
  ext i
  -- ⊢ ↑vi i = ↑0 i
  rw [Finsupp.zero_apply]
  -- ⊢ ↑vi i = 0
  specialize hB (v i)
  -- ⊢ ↑vi i = 0
  simp_rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, map_sum₂, map_smulₛₗ₂,
    smul_eq_mul] at hB
  rw [Finset.sum_eq_single i] at hB
  · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (h i) hB
    -- 🎉 no goals
  · intro j _hj hij
    -- ⊢ ↑(RingHom.id R) (↑vi j) * ↑(↑B (↑v j)) (↑v i) = 0
    replace hij : B (v j) (v i) = 0 := hO hij
    -- ⊢ ↑(RingHom.id R) (↑vi j) * ↑(↑B (↑v j)) (↑v i) = 0
    rw [hij, RingHom.id_apply, mul_zero]
    -- 🎉 no goals
  · intro hi
    -- ⊢ ↑(RingHom.id R) (↑vi i) * ↑(↑B (↑v i)) (↑v i) = 0
    replace hi : vi i = 0 := Finsupp.not_mem_support_iff.mp hi
    -- ⊢ ↑(RingHom.id R) (↑vi i) * ↑(↑B (↑v i)) (↑v i) = 0
    rw [hi, RingHom.id_apply, zero_mul]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho.separating_left_of_not_is_ortho_basis_self LinearMap.IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is right-separating
if the basis has no elements which are self-orthogonal. -/
theorem IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self [NoZeroDivisors R]
    {B : M →ₗ[R] M →ₗ[R] R} (v : Basis n R M) (hO : B.IsOrthoᵢ v)
    (h : ∀ i, ¬B.IsOrtho (v i) (v i)) : B.SeparatingRight := by
  rw [isOrthoᵢ_flip] at hO
  -- ⊢ SeparatingRight B
  rw [← flip_separatingLeft]
  -- ⊢ SeparatingLeft (flip B)
  refine' IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO fun i ↦ _
  -- ⊢ ¬IsOrtho (flip B) (↑v i) (↑v i)
  rw [isOrtho_flip]
  -- ⊢ ¬IsOrtho (flip (flip B)) (↑v i) (↑v i)
  exact h i
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho.separating_right_iff_not_is_ortho_basis_self LinearMap.IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
if the basis has no elements which are self-orthogonal. -/
theorem IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self [NoZeroDivisors R] {B : M →ₗ[R] M →ₗ[R] R}
    (v : Basis n R M) (hO : B.IsOrthoᵢ v) (h : ∀ i, ¬B.IsOrtho (v i) (v i)) : B.Nondegenerate :=
  ⟨IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO h,
    IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self v hO h⟩
set_option linter.uppercaseLean3 false in
#align linear_map.is_Ortho.nondegenerate_of_not_is_ortho_basis_self LinearMap.IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self

end CommRing

end Nondegenerate

end LinearMap
