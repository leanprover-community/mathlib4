/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Sesquilinear maps

This files provides properties about sesquilinear maps and forms. The maps considered are of the
form `M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁`, `M₂` is a module over `R₂` and `M` is a module over `R`.
Sesquilinear forms are the special case that `M₁ = M₂`, `M = R₁ = R₂ = R`, and `I₁ = RingHom.id R`.
Taking additionally `I₂ = RingHom.id R`, then one obtains bilinear forms.

Sesquilinear maps are a special case of the bilinear maps defined in `BilinearMap.lean` and `many`
basic lemmas about construction and elementary calculations are found there.

## Main declarations

* `IsOrtho`: states that two vectors are orthogonal with respect to a sesquilinear map
* `IsSymm`, `IsAlt`: states that a sesquilinear form is symmetric and alternating, respectively
* `orthogonalBilin`: provides the orthogonal complement with respect to sesquilinear form

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form, Sesquilinear map,
-/

open Module

variable {R R₁ R₂ R₃ M M₁ M₂ M₃ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

namespace LinearMap

/-! ### Orthogonal vectors -/


section CommRing

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] [CommSemiring R₂]
  [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M] [Module R M]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- The proposition that two elements of a sesquilinear map space are orthogonal -/
def IsOrtho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop :=
  B x y = 0

theorem isOrtho_def {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} {x y} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

theorem isOrtho_zero_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x) : IsOrtho B (0 : M₁) x := by
  dsimp only [IsOrtho]
  rw [map_zero B, zero_apply]

theorem isOrtho_zero_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x) : IsOrtho B x (0 : M₂) :=
  map_zero (B x)

theorem isOrtho_flip {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M} {x y} : B.IsOrtho x y ↔ B.flip.IsOrtho y x := by
  simp_rw [isOrtho_def, flip_apply]

open scoped Function in -- required for scoped `on` notation
/-- A set of vectors `v` is orthogonal with respect to some bilinear map `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`BilinForm.isOrtho` -/
def IsOrthoᵢ (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M) (v : n → M₁) : Prop :=
  Pairwise (B.IsOrtho on v)

theorem isOrthoᵢ_def {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M} {v : n → M₁} :
    B.IsOrthoᵢ v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl

theorem isOrthoᵢ_flip (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M) {v : n → M₁} :
    B.IsOrthoᵢ v ↔ B.flip.IsOrthoᵢ v := by
  simp_rw [isOrthoᵢ_def]
  constructor <;> exact fun h i j hij ↦ h j i hij.symm

end CommRing

section Field

variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [Field K₂] [AddCommGroup V₂] [Module K₂ V₂]
  {I₁ : K₁ →+* K} {I₂ : K₂ →+* K} {I₁' : K₁ →+* K} {J₁ : K →+* K} {J₂ : K →+* K}

-- todo: this also holds for [CommRing R] [IsDomain R] when J₁ is invertible
theorem ortho_smul_left {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] V} {x y} {a : K₁} (ha : a ≠ 0) :
    IsOrtho B x y ↔ IsOrtho B (a • x) y := by
  dsimp only [IsOrtho]
  constructor <;> intro H
  · rw [map_smulₛₗ₂, H, smul_zero]
  · rw [map_smulₛₗ₂, smul_eq_zero] at H
    rcases H with H | H
    · rw [map_eq_zero I₁] at H
      trivial
    · exact H

-- todo: this also holds for [CommRing R] [IsDomain R] when J₂ is invertible
theorem ortho_smul_right {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] V} {x y} {a : K₂} {ha : a ≠ 0} :
    IsOrtho B x y ↔ IsOrtho B x (a • y) := by
  dsimp only [IsOrtho]
  constructor <;> intro H
  · rw [map_smulₛₗ, H, smul_zero]
  · rw [map_smulₛₗ, smul_eq_zero] at H
    rcases H with H | H
    · simp only [map_eq_zero] at H
      exfalso
      exact ha H
    · exact H

/-- A set of orthogonal vectors `v` with respect to some sesquilinear map `B` is linearly
  independent if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem linearIndependent_of_isOrthoᵢ {B : V₁ →ₛₗ[I₁] V₁ →ₛₗ[I₁'] V} {v : n → V₁}
    (hv₁ : B.IsOrthoᵢ v) (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K₁ v := by
  classical
    rw [linearIndependent_iff']
    intro s w hs i hi
    have : B (s.sum fun i : n ↦ w i • v i) (v i) = 0 := by rw [hs, map_zero, zero_apply]
    have hsum : (s.sum fun j : n ↦ I₁ (w j) • B (v j) (v i)) = I₁ (w i) • B (v i) (v i) := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j _hj hij
      rw [isOrthoᵢ_def.1 hv₁ _ _ hij, smul_zero]
    simp_rw [B.map_sum₂, map_smulₛₗ₂, hsum] at this
    apply (map_eq_zero I₁).mp
    exact (smul_eq_zero.mp this).elim _root_.id (hv₂ i · |>.elim)

end Field

/-! ### Reflexive bilinear maps -/


section Reflexive

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

/-- The proposition that a sesquilinear map is reflexive -/
def IsRefl (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Prop :=
  ∀ x y, B x y = 0 → B y x = 0

namespace IsRefl

section
variable (H : B.IsRefl)
include H

theorem eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := fun {x y} ↦ H x y

theorem eq_iff {x y} : B x y = 0 ↔ B y x = 0 := ⟨H x y, H y x⟩

theorem ortho_comm {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩

theorem domRestrict (p : Submodule R₁ M₁) : (B.domRestrict₁₂ p p).IsRefl :=
  fun _ _ ↦ by
  simp_rw [domRestrict₁₂_apply]
  exact H _ _
end
@[simp]
theorem flip_isRefl_iff : B.flip.IsRefl ↔ B.IsRefl :=
  ⟨fun h x y H ↦ h y x ((B.flip_apply _ _).trans H), fun h x y ↦ h y x⟩

theorem ker_flip_eq_bot (H : B.IsRefl) (h : LinearMap.ker B = ⊥) : LinearMap.ker B.flip = ⊥ := by
  refine ker_eq_bot'.mpr fun _ hx ↦ ker_eq_bot'.mp h _ ?_
  ext
  exact H _ _ (LinearMap.congr_fun hx _)

theorem ker_eq_bot_iff_ker_flip_eq_bot (H : B.IsRefl) :
    LinearMap.ker B = ⊥ ↔ LinearMap.ker B.flip = ⊥ := by
  refine ⟨ker_flip_eq_bot H, fun h ↦ ?_⟩
  exact (congr_arg _ B.flip_flip.symm).trans (ker_flip_eq_bot (flip_isRefl_iff.mpr H) h)

end IsRefl

end Reflexive

/-! ### Symmetric bilinear forms -/


section Symmetric

variable [CommSemiring R] [AddCommMonoid M] [Module R M] {I : R →+* R} {B : M →ₛₗ[I] M →ₗ[R] R}

/-- The proposition that a sesquilinear form is symmetric -/
structure IsSymm (B : M →ₛₗ[I] M →ₗ[R] R) : Prop where
  protected eq : ∀ x y, I (B x y) = B y x

theorem isSymm_def {B : M →ₛₗ[I] M →ₗ[R] R} : B.IsSymm ↔ ∀ x y, I (B x y) = B y x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

namespace IsSymm

theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 ↦ by
  rw [← H.eq]
  simp [H1]

theorem ortho_comm (H : B.IsSymm) {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.isRefl.ortho_comm

theorem domRestrict (H : B.IsSymm) (p : Submodule R M) : (B.domRestrict₁₂ p p).IsSymm where
  eq _ _ := by
    simp_rw [domRestrict₁₂_apply]
    exact H.eq _ _

end IsSymm

@[simp]
theorem isSymm_zero : (0 : M →ₛₗ[I] M →ₗ[R] R).IsSymm := ⟨fun _ _ => map_zero _⟩

protected lemma IsSymm.add {C : M →ₛₗ[I] M →ₗ[R] R} (hB : B.IsSymm) (hC : C.IsSymm) :
    (B + C).IsSymm where
  eq x y := by simp [hB.eq, hC.eq]

theorem BilinMap.isSymm_iff_eq_flip {N : Type*} [AddCommMonoid N] [Module R N]
    {B : LinearMap.BilinMap R M N} : (∀ x y, B x y = B y x) ↔ B = B.flip := by
  simp [LinearMap.ext_iff₂]

theorem isSymm_iff_eq_flip {B : LinearMap.BilinForm R M} : B.IsSymm ↔ B = B.flip :=
  isSymm_def.trans BilinMap.isSymm_iff_eq_flip

end Symmetric

/-! ### Positive semidefinite sesquilinear forms -/

section PositiveSemidefinite

variable [CommSemiring R] [AddCommMonoid M] [Module R M] {I₁ I₂ : R →+* R}

/-- A sesquilinear form `B` is **nonnegative** if for any `x` we have `0 ≤ B x x`. -/
structure IsNonneg [LE R] (B : M →ₛₗ[I₁] M →ₛₗ[I₂] R) where
  nonneg : ∀ x, 0 ≤ B x x

lemma isNonneg_def [LE R] {B : M →ₛₗ[I₁] M →ₛₗ[I₂] R} : B.IsNonneg ↔ ∀ x, 0 ≤ B x x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

@[simp]
lemma isNonneg_zero [Preorder R] : IsNonneg (0 : M →ₛₗ[I₁] M →ₛₗ[I₂] R) := ⟨fun _ ↦ le_rfl⟩

protected lemma IsNonneg.add [Preorder R] [AddLeftMono R] {B C : M →ₛₗ[I₁] M →ₛₗ[I₂] R}
    (hB : B.IsNonneg) (hC : C.IsNonneg) : (B + C).IsNonneg where
  nonneg x := add_nonneg (hB.nonneg x) (hC.nonneg x)

protected lemma IsNonneg.smul [Preorder R] [PosMulMono R] {B : M →ₛₗ[I₁] M →ₛₗ[I₂] R} {c : R}
    (hB : B.IsNonneg) (hc : 0 ≤ c) : (c • B).IsNonneg where
  nonneg x := mul_nonneg hc (hB.nonneg x)

/-- A sesquilinear form `B` is **positive semidefinite** if it is symmetric and nonnegative. -/
structure IsPosSemidef [LE R] (B : M →ₛₗ[I₁] M →ₗ[R] R) extends
  isSymm : B.IsSymm,
  isNonneg : B.IsNonneg

lemma isPosSemidef_def [LE R] {B : M →ₛₗ[I₁] M →ₗ[R] R} : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg :=
  ⟨fun h ↦ ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

@[simp]
lemma isPosSemidef_zero [Preorder R] : IsPosSemidef (0 : M →ₛₗ[I₁] M →ₗ[R] R) where
  isSymm := isSymm_zero
  isNonneg := isNonneg_zero

protected lemma IsPosSemidef.add [Preorder R] [AddLeftMono R] {B C : M →ₛₗ[I₁] M →ₗ[R] R}
    (hB : B.IsPosSemidef) (hC : C.IsPosSemidef) : (B + C).IsPosSemidef :=
  isPosSemidef_def.2 ⟨hB.isSymm.add hC.isSymm, hB.isNonneg.add hC.isNonneg⟩

end PositiveSemidefinite

/-! ### Alternating bilinear maps -/


section Alternating

section CommSemiring

section AddCommMonoid

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {I : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

/-- The proposition that a sesquilinear map is alternating -/
def IsAlt (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Prop :=
  ∀ x, B x x = 0

variable (H : B.IsAlt)
include H

theorem IsAlt.self_eq_zero (x : M₁) : B x x = 0 :=
  H x

theorem IsAlt.eq_of_add_add_eq_zero [IsCancelAdd M] {a b c : M₁} (hAdd : a + b + c = 0) :
    B a b = B b c := by
  have : B a a + B a b + B a c = B a c + B b c + B c c := by
    simp_rw [← map_add, ← map_add₂, hAdd, map_zero, LinearMap.zero_apply]
  rw [H, H, zero_add, add_zero, add_comm] at this
  exact add_left_cancel this

end AddCommMonoid

section AddCommGroup

namespace IsAlt

variable [CommSemiring R] [AddCommGroup M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {I : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

theorem neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x := by
  have H1 : B (y + x) (y + x) = 0 := self_eq_zero H (y + x)
  simpa [map_add, self_eq_zero H, add_eq_zero_iff_neg_eq] using H1

theorem isRefl (H : B.IsAlt) : B.IsRefl := by
  intro x y h
  rw [← neg H, h, neg_zero]

theorem ortho_comm (H : B.IsAlt) {x y} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.isRefl.ortho_comm

end IsAlt

end AddCommGroup

end CommSemiring

section Semiring

variable [CommRing R] [AddCommGroup M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I : R₁ →+* R}

theorem isAlt_iff_eq_neg_flip [NoZeroDivisors R] [CharZero R] {B : M₁ →ₛₗ[I] M₁ →ₛₗ[I] R} :
    B.IsAlt ↔ B = -B.flip := by
  constructor <;> intro h
  · ext
    simp_rw [neg_apply, flip_apply]
    exact (h.neg _ _).symm
  intro x
  let h' := congr_fun₂ h x x
  simp only [neg_apply, flip_apply, ← add_eq_zero_iff_eq_neg] at h'
  exact add_self_eq_zero.mp h'

end Semiring

end Alternating

end LinearMap

namespace Submodule

/-! ### The orthogonal complement -/

variable [CommRing R] [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M] [Module R M]
  {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

/-- The orthogonal complement of a submodule `N` with respect to some bilinear map is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear maps this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonalBilin (N : Submodule R₁ M₁) (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Submodule R₁ M₁ where
  carrier := { m | ∀ n ∈ N, B.IsOrtho n m }
  zero_mem' x _ := B.isOrtho_zero_right x
  add_mem' hx hy n hn := by
    rw [LinearMap.IsOrtho, map_add, show B n _ = 0 from hx n hn, show B n _ = 0 from hy n hn,
      zero_add]
  smul_mem' c x hx n hn := by
    rw [LinearMap.IsOrtho, LinearMap.map_smulₛₗ, show B n x = 0 from hx n hn, smul_zero]

variable {N L : Submodule R₁ M₁}

@[simp]
theorem mem_orthogonalBilin_iff {m : M₁} : m ∈ N.orthogonalBilin B ↔ ∀ n ∈ N, B.IsOrtho n m :=
  Iff.rfl

theorem orthogonalBilin_le (h : N ≤ L) : L.orthogonalBilin B ≤ N.orthogonalBilin B :=
  fun _ hn l hl ↦ hn l (h hl)

theorem le_orthogonalBilin_orthogonalBilin (b : B.IsRefl) :
    N ≤ (N.orthogonalBilin B).orthogonalBilin B := fun n hn _m hm ↦ b _ _ (hm n hn)

end Submodule

namespace LinearMap

section Orthogonal

variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [AddCommGroup V₂] [Module K V₂] {J : K →+* K} {J₁ : K₁ →+* K} {J₁' : K₁ →+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot (B : V₁ →ₛₗ[J₁] V₁ →ₛₗ[J₁'] V₂) (x : V₁)
    (hx : ¬B.IsOrtho x x) : (K₁ ∙ x) ⊓ Submodule.orthogonalBilin (K₁ ∙ x) B = ⊥ := by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h ↦ ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  replace h := h.2 x (by simp [Submodule.mem_span] : x ∈ Submodule.span K₁ ({x} : Finset V₁))
  rw [Finset.sum_singleton] at h ⊢
  suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
  rw [isOrtho_def, map_smulₛₗ] at h
  exact Or.elim (smul_eq_zero.mp h)
      (fun y ↦ by simpa using y)
      (fun hfalse ↦ False.elim <| hx hfalse)

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_to_lin_ker {B : V →ₗ[K] V →ₛₗ[J] V₂} (x : V) :
    Submodule.orthogonalBilin (K ∙ x) B = LinearMap.ker (B x) := by
  ext y
  simp_rw [Submodule.mem_orthogonalBilin_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h ↦ h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [isOrtho_def, map_smulₛₗ₂, smul_eq_zero]
    exact Or.intro_right _ h

-- todo: Generalize this to sesquilinear maps
theorem span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊔ Submodule.orthogonalBilin (N := K ∙ x) (B := B) = ⊤ := by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact (B x).span_singleton_sup_ker_eq_top hx

-- todo: Generalize this to sesquilinear maps
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem isCompl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K ∙ x) (Submodule.orthogonalBilin (N := K ∙ x) (B := B)) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

/-! ### Adjoint pairs -/


section AdjointPair

section AddCommMonoid

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁]
variable [AddCommMonoid M₂] [Module R M₂]
variable [AddCommMonoid M₃] [Module R M₃]
variable {I : R →+* R}
variable {B F : M →ₗ[R] M →ₛₗ[I] M₃} {B' : M₁ →ₗ[R] M₁ →ₛₗ[I] M₃} {B'' : M₂ →ₗ[R] M₂ →ₛₗ[I] M₃}
variable {f f' : M →ₗ[R] M₁} {g g' : M₁ →ₗ[R] M}
variable (B B' f g)

/-- Given a pair of modules equipped with bilinear maps, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def IsAdjointPair (f : M → M₁) (g : M₁ → M) :=
  ∀ x y, B' (f x) y = B x (g y)

variable {B B' f g}

theorem isAdjointPair_iff_comp_eq_compl₂ : IsAdjointPair B B' f g ↔ B'.comp f = B.compl₂ g := by
  constructor <;> intro h
  · ext x y
    rw [comp_apply, compl₂_apply]
    exact h x y
  · intro _ _
    rw [← compl₂_apply, ← comp_apply, h]

theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun _ _ ↦ by
  simp only [Pi.zero_apply, map_zero, zero_apply]

theorem isAdjointPair_id : IsAdjointPair B B (_root_.id : M → M) (_root_.id : M → M) :=
  fun _ _ ↦ rfl

theorem isAdjointPair_one : IsAdjointPair B B (1 : Module.End R M) (1 : Module.End R M) :=
  isAdjointPair_id

theorem IsAdjointPair.add {f f' : M → M₁} {g g' : M₁ → M} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x _ ↦ by
  rw [Pi.add_apply, Pi.add_apply, B'.map_add₂, (B x).map_add, h, h']

theorem IsAdjointPair.comp {f : M → M₁} {g : M₁ → M} {f' : M₁ → M₂} {g' : M₂ → M₁}
    (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B' B'' f' g') :
    IsAdjointPair B B'' (f' ∘ f) (g ∘ g') := fun _ _ ↦ by
  rw [Function.comp_def, Function.comp_def, h', h]

theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) :=
  h'.comp h

end AddCommMonoid

section AddCommGroup

variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable {B F : M →ₗ[R] M →ₗ[R] M₂} {B' : M₁ →ₗ[R] M₁ →ₗ[R] M₂}
variable {f f' : M → M₁} {g g' : M₁ → M}

theorem IsAdjointPair.sub (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f - f') (g - g') := fun x _ ↦ by
  rw [Pi.sub_apply, Pi.sub_apply, B'.map_sub₂, (B x).map_sub, h, h']

theorem IsAdjointPair.smul (c : R) (h : IsAdjointPair B B' f g) :
    IsAdjointPair B B' (c • f) (c • g) := fun _ _ ↦ by
  simp [h _]

end AddCommGroup

section OrthogonalMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinForm R M) (f : M → M)

/-- A linear transformation `f` is orthogonal with respect to a bilinear form `B` if `B` is
bi-invariant with respect to `f`. -/
def IsOrthogonal : Prop :=
  ∀ x y, B (f x) (f y) = B x y

variable {B f}

@[simp]
lemma _root_.LinearEquiv.isAdjointPair_symm_iff {f : M ≃ M} :
    LinearMap.IsAdjointPair B B f f.symm ↔ B.IsOrthogonal f :=
  ⟨fun hf x y ↦ by simpa using hf x (f y), fun hf x y ↦ by simpa using hf x (f.symm y)⟩

lemma isOrthogonal_of_forall_apply_same {F : Type*} [FunLike F M M] [LinearMapClass F R M M]
    (f : F) (h : IsLeftRegular (2 : R)) (hB : B.IsSymm) (hf : ∀ x, B (f x) (f x) = B x x) :
    B.IsOrthogonal f := by
  intro x y
  suffices 2 * B (f x) (f y) = 2 * B x y from h this
  have := hf (x + y)
  simp only [map_add, LinearMap.add_apply, hf x, hf y, show B y x = B x y from hB.eq y x] at this
  rw [show B (f y) (f x) = B (f x) (f y) from hB.eq (f y) (f x)] at this
  simp only [add_assoc, add_right_inj] at this
  simp only [← add_assoc, add_left_inj] at this
  simpa only [← two_mul] using this

end OrthogonalMap

end AdjointPair

/-! ### Self-adjoint pairs -/


section SelfadjointPair

section AddCommMonoid

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁]
variable {I : R →+* R}
variable (B F : M →ₗ[R] M →ₛₗ[I] M₁)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear maps
on the underlying module. In the case that these two maps are identical, this is the usual concept
of self adjointness. In the case that one of the maps is the negation of the other, this is the
usual concept of skew adjointness. -/
def IsPairSelfAdjoint (f : M → M) :=
  IsAdjointPair B F f f

/-- An endomorphism of a module is self-adjoint with respect to a bilinear map if it serves as an
adjoint for itself. -/
protected def IsSelfAdjoint (f : M → M) :=
  IsAdjointPair B B f f

end AddCommMonoid

section AddCommGroup

variable [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂] (B F : M →ₗ[R] M →ₗ[R] M₂)

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where
  carrier := { f | IsPairSelfAdjoint B F f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear map if its negation
serves as an adjoint. -/
def IsSkewAdjoint (f : M → M) :=
  IsAdjointPair B B f (-f)

/-- The set of self-adjoint endomorphisms of a module with bilinear map is a submodule. (In fact
it is a Jordan subalgebra.) -/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B B

/-- The set of skew-adjoint endomorphisms of a module with bilinear map is a submodule. (In fact
it is a Lie subalgebra.) -/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B) B

variable {B F}

@[simp]
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R M) :
    f ∈ isPairSelfAdjointSubmodule B F ↔ IsPairSelfAdjoint B F f :=
  Iff.rfl

theorem isPairSelfAdjoint_equiv (e : M₁ ≃ₗ[R] M) (f : Module.End R M) :
    IsPairSelfAdjoint B F f ↔
      IsPairSelfAdjoint (B.compl₁₂ e e) (F.compl₁₂ e e) (e.symm.conj f) := by
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
  simp_rw [IsPairSelfAdjoint, isAdjointPair_iff_comp_eq_compl₂, hₗ, hᵣ, compl₁₂_inj he he]

theorem isSkewAdjoint_iff_neg_self_adjoint (f : M → M) :
    B.IsSkewAdjoint f ↔ IsAdjointPair (-B) B f f :=
  show (∀ x y, B (f x) y = B x ((-f) y)) ↔ ∀ x y, B (f x) y = (-B) x (f y) by simp

@[simp]
theorem mem_selfAdjointSubmodule (f : Module.End R M) :
    f ∈ B.selfAdjointSubmodule ↔ B.IsSelfAdjoint f :=
  Iff.rfl

@[simp]
theorem mem_skewAdjointSubmodule (f : Module.End R M) :
    f ∈ B.skewAdjointSubmodule ↔ B.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl

end AddCommGroup

end SelfadjointPair

/-! ### Nondegenerate bilinear maps -/


section Nondegenerate

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- A bilinear map is called left-separating if
the only element that is left-orthogonal to every other element is `0`; i.e.,
for every nonzero `x` in `M₁`, there exists `y` in `M₂` with `B x y ≠ 0`. -/
def SeparatingLeft (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  ∀ x : M₁, (∀ y : M₂, B x y = 0) → x = 0

variable (M₁ M₂ I₁ I₂)

/-- In a non-trivial module, zero is not non-degenerate. -/
theorem not_separatingLeft_zero [Nontrivial M₁] : ¬(0 : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M).SeparatingLeft :=
  let ⟨m, hm⟩ := exists_ne (0 : M₁)
  fun h ↦ hm (h m fun _n ↦ rfl)

variable {M₁ M₂ I₁ I₂}

theorem SeparatingLeft.ne_zero [Nontrivial M₁] {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}
    (h : B.SeparatingLeft) : B ≠ 0 := fun h0 ↦ not_separatingLeft_zero M₁ M₂ I₁ I₂ <| h0 ▸ h

section Linear

variable [AddCommMonoid Mₗ₁] [AddCommMonoid Mₗ₂] [AddCommMonoid Mₗ₁'] [AddCommMonoid Mₗ₂']

variable [Module R Mₗ₁] [Module R Mₗ₂] [Module R Mₗ₁'] [Module R Mₗ₂']
variable {B : Mₗ₁ →ₗ[R] Mₗ₂ →ₗ[R] M} (e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂')

theorem SeparatingLeft.congr (h : B.SeparatingLeft) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft := by
  intro x hx
  rw [← e₁.symm.map_eq_zero_iff]
  refine h (e₁.symm x) fun y ↦ ?_
  specialize hx (e₂ y)
  simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_eq_zero_iff] at hx
  exact hx

@[simp]
theorem separatingLeft_congr_iff :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft ↔ B.SeparatingLeft :=
  ⟨fun h ↦ by
    convert h.congr e₁.symm e₂.symm
    ext x y
    simp,
   SeparatingLeft.congr e₁ e₂⟩

end Linear

/-- A bilinear map is called right-separating if
the only element that is right-orthogonal to every other element is `0`; i.e.,
for every nonzero `y` in `M₂`, there exists `x` in `M₁` with `B x y ≠ 0`. -/
def SeparatingRight (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  ∀ y : M₂, (∀ x : M₁, B x y = 0) → y = 0

/-- A bilinear map is called non-degenerate if it is left-separating and right-separating. -/
def Nondegenerate (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  SeparatingLeft B ∧ SeparatingRight B

@[simp]
theorem flip_separatingRight {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.flip.SeparatingRight ↔ B.SeparatingLeft :=
  ⟨fun hB x hy ↦ hB x hy, fun hB x hy ↦ hB x hy⟩

@[simp]
theorem flip_separatingLeft {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.flip.SeparatingLeft ↔ SeparatingRight B := by rw [← flip_separatingRight, flip_flip]

@[simp]
theorem flip_nondegenerate {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} : B.flip.Nondegenerate ↔ B.Nondegenerate :=
  Iff.trans and_comm (and_congr flip_separatingRight flip_separatingLeft)

theorem separatingLeft_iff_linear_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingLeft ↔ ∀ x : M₁, B x = 0 → x = 0 := by
  constructor <;> intro h x hB
  · simpa only [hB, zero_apply, eq_self_iff_true, forall_const] using h x
  have h' : B x = 0 := by
    ext
    rw [zero_apply]
    exact hB _
  exact h x h'

theorem separatingRight_iff_linear_flip_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingRight ↔ ∀ y : M₂, B.flip y = 0 → y = 0 := by
  rw [← flip_separatingLeft, separatingLeft_iff_linear_nontrivial]

/-- A bilinear map is left-separating if and only if it has a trivial kernel. -/
theorem separatingLeft_iff_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingLeft ↔ LinearMap.ker B = ⊥ :=
  Iff.trans separatingLeft_iff_linear_nontrivial LinearMap.ker_eq_bot'.symm

/-- A bilinear map is right-separating if and only if its flip has a trivial kernel. -/
theorem separatingRight_iff_flip_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingRight ↔ LinearMap.ker B.flip = ⊥ := by
  rw [← flip_separatingLeft, separatingLeft_iff_ker_eq_bot]

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁] {I I' : R →+* R}

theorem IsRefl.nondegenerate_iff_separatingLeft {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl) :
    B.Nondegenerate ↔ B.SeparatingLeft := by
  refine ⟨fun h ↦ h.1, fun hB' ↦ ⟨hB', ?_⟩⟩
  rw [separatingRight_iff_flip_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mp]
  rwa [← separatingLeft_iff_ker_eq_bot]

theorem IsRefl.nondegenerate_iff_separatingRight {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl) :
    B.Nondegenerate ↔ B.SeparatingRight := by
  refine ⟨fun h ↦ h.2, fun hB' ↦ ⟨?_, hB'⟩⟩
  rw [separatingLeft_iff_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr]
  rwa [← separatingRight_iff_flip_ker_eq_bot]

lemma disjoint_ker_of_nondegenerate_restrict {B : M →ₗ[R] M →ₗ[R] M₁} {W : Submodule R M}
    (hW : (B.domRestrict₁₂ W W).Nondegenerate) :
    Disjoint W (LinearMap.ker B) := by
  refine Submodule.disjoint_def.mpr fun x hx hx' ↦ ?_
  let x' : W := ⟨x, hx⟩
  suffices x' = 0 by simpa [x']
  apply hW.1 x'
  simp_rw [Subtype.forall, domRestrict₁₂_apply]
  intro y hy
  rw [mem_ker] at hx'
  simp [x', hx']

lemma IsSymm.nondegenerate_restrict_of_isCompl_ker {B : M →ₗ[R] M →ₗ[R] R} (hB : B.IsSymm)
    {W : Submodule R M} (hW : IsCompl W (LinearMap.ker B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y ↦ hB.isRefl (W.subtype x) (W.subtype y)
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ hx'
  simp only [Submodule.mk_eq_zero]
  replace hx' : ∀ y ∈ W, B x y = 0 := by simpa [Subtype.forall] using hx'
  replace hx' : x ∈ W ⊓ ker B := by
    refine ⟨hx, ?_⟩
    ext y
    obtain ⟨u, hu, v, hv, rfl⟩ : ∃ u ∈ W, ∃ v ∈ ker B, u + v = y := by
      rw [← Submodule.mem_sup, hW.sup_eq_top]; exact Submodule.mem_top
    suffices B x u = 0 by rw [mem_ker] at hv; simpa [← hB.eq v, hv]
    exact hx' u hu
  simpa [hW.inf_eq_bot] using hx'

/-- The restriction of a reflexive bilinear map `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `Disjoint W (W.orthogonalBilin B)`. -/
theorem nondegenerate_restrict_of_disjoint_orthogonal {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl)
    {W : Submodule R M} (hW : Disjoint W (W.orthogonalBilin B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  rw [(hB.domRestrict W).nondegenerate_iff_separatingLeft]
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R]
  refine hW.le_bot ⟨hx, fun y hy ↦ ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp_rw [domRestrict₁₂_apply] at b₁
  rw [hB.ortho_comm]
  exact b₁

/-- An orthogonal basis with respect to a left-separating bilinear map has no self-orthogonal
elements. -/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft [Nontrivial R]
    {B : M →ₛₗ[I] M →ₛₗ[I'] M₁} {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingLeft)
    (i : n) : ¬B.IsOrtho (v i) (v i) := by
  intro ho
  refine v.ne_zero i (hB (v i) fun m ↦ ?_)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  rintro j -
  rw [map_smulₛₗ]
  suffices B (v i) (v j) = 0 by rw [this, smul_zero]
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij

/-- An orthogonal basis with respect to a right-separating bilinear map has no self-orthogonal
elements. -/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight [Nontrivial R]
    {B : M →ₛₗ[I] M →ₛₗ[I'] M₁} {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingRight)
    (i : n) : ¬B.IsOrtho (v i) (v i) := by
  rw [isOrthoᵢ_flip] at h
  rw [isOrtho_flip]
  exact h.not_isOrtho_basis_self_of_separatingLeft (flip_separatingLeft.mpr hB) i

/-- Given an orthogonal basis with respect to a bilinear map, the bilinear map is left-separating if
the basis has no elements which are self-orthogonal. -/
theorem IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self [NoZeroSMulDivisors R M₁]
    {B : M →ₗ[R] M →ₗ[R] M₁} (v : Basis n R M) (hO : B.IsOrthoᵢ v)
    (h : ∀ i, ¬B.IsOrtho (v i) (v i)) : B.SeparatingLeft := by
  intro m hB
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂,
           map_smulₛₗ₂] at hB
  rw [Finset.sum_eq_single i] at hB
  · exact (smul_eq_zero.mp hB).elim _root_.id (h i).elim
  · intro j _hj hij
    replace hij : B (v j) (v i) = 0 := hO hij
    rw [hij, RingHom.id_apply, smul_zero]
  · intro hi
    replace hi : vi i = 0 := Finsupp.notMem_support_iff.mp hi
    rw [hi, RingHom.id_apply, zero_smul]

/-- Given an orthogonal basis with respect to a bilinear map, the bilinear map is right-separating
if the basis has no elements which are self-orthogonal. -/
theorem IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self [NoZeroSMulDivisors R M₁]
    {B : M →ₗ[R] M →ₗ[R] M₁} (v : Basis n R M) (hO : B.IsOrthoᵢ v)
    (h : ∀ i, ¬B.IsOrtho (v i) (v i)) : B.SeparatingRight := by
  rw [isOrthoᵢ_flip] at hO
  rw [← flip_separatingLeft]
  refine IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO fun i ↦ ?_
  rw [isOrtho_flip]
  exact h i

/-- Given an orthogonal basis with respect to a bilinear map, the bilinear map is nondegenerate
if the basis has no elements which are self-orthogonal. -/
theorem IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self [NoZeroSMulDivisors R M₁]
    {B : M →ₗ[R] M →ₗ[R] M₁} (v : Basis n R M) (hO : B.IsOrthoᵢ v)
    (h : ∀ i, ¬B.IsOrtho (v i) (v i)) : B.Nondegenerate :=
  ⟨IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO h,
    IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self v hO h⟩

end CommRing

end Nondegenerate

namespace BilinForm

lemma apply_smul_sub_smul_sub_eq [CommRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (x y : M) :
    B ((B x y) • x - (B x x) • y) ((B x y) • x - (B x x) • y) =
      (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, mul_sub,
    mul_comm (B x y) (B x x), mul_left_comm (B x y) (B x x)]
  abel

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M)

/-- The **Cauchy-Schwarz inequality** for positive semidefinite forms. -/
lemma apply_mul_apply_le_of_forall_zero_le (hs : ∀ x, 0 ≤ B x x) (x y : M) :
    (B x y) * (B y x) ≤ (B x x) * (B y y) := by
  have aux (x y : M) : 0 ≤ (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
    rw [← apply_smul_sub_smul_sub_eq B x y]
    exact hs (B x y • x - B x x • y)
  rcases lt_or_ge 0 (B x x) with hx | hx
  · exact sub_nonneg.mp <| nonneg_of_mul_nonneg_right (aux x y) hx
  · replace hx : B x x = 0 := le_antisymm hx (hs x)
    rcases lt_or_ge 0 (B y y) with hy | hy
    · rw [mul_comm (B x y), mul_comm (B x x)]
      exact sub_nonneg.mp <| nonneg_of_mul_nonneg_right (aux y x) hy
    · replace hy : B y y = 0 := le_antisymm hy (hs y)
      suffices B x y = - B y x by simpa [this, hx, hy] using mul_self_nonneg (B y x)
      rw [eq_neg_iff_add_eq_zero]
      apply le_antisymm
      · simpa [hx, hy, le_neg_iff_add_nonpos_left] using hs (x - y)
      · simpa [hx, hy] using hs (x + y)

/-- The **Cauchy-Schwarz inequality** for positive semidefinite symmetric forms. -/
lemma apply_sq_le_of_symm (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) (x y : M) :
    (B x y) ^ 2 ≤ (B x x) * (B y y) := by
  rw [show (B x y) ^ 2 = (B x y) * (B y x) by rw [sq, ← hB.eq, RingHom.id_apply]]
  exact apply_mul_apply_le_of_forall_zero_le B hs x y

/-- The equality case of **Cauchy-Schwarz**. -/
lemma not_linearIndependent_of_apply_mul_apply_eq (hp : ∀ x, x ≠ 0 → 0 < B x x)
    (x y : M) (he : (B x y) * (B y x) = (B x x) * (B y y)) :
    ¬ LinearIndependent R ![x, y] := by
  have hz : (B x y) • x - (B x x) • y = 0 := by
    by_contra hc
    exact (ne_of_lt (hp ((B x) y • x - (B x) x • y) hc)).symm <|
      (apply_smul_sub_smul_sub_eq B x y).symm ▸ (mul_eq_zero_of_right ((B x) x)
      (sub_eq_zero_of_eq he.symm))
  by_contra hL
  by_cases hx : x = 0
  · simpa [hx] using LinearIndependent.ne_zero 0 hL
  · have h := sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
    rw [sub_eq_add_neg, ← neg_smul, add_comm] at h
    exact (Ne.symm (ne_of_lt (hp x hx))) (LinearIndependent.eq_zero_of_pair hL h).2

/-- Strict **Cauchy-Schwarz** is equivalent to linear independence for positive definite forms. -/
lemma apply_mul_apply_lt_iff_linearIndependent [NoZeroSMulDivisors R M]
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (x y : M) :
    (B x y) * (B y x) < (B x x) * (B y y) ↔ LinearIndependent R ![x, y] := by
  have hle : ∀ z, 0 ≤ B z z := by
    intro z
    by_cases hz : z = 0; simp [hz]
    exact le_of_lt (hp z hz)
  constructor
  · contrapose!
    intro h
    rw [LinearIndependent.pair_iff] at h
    push_neg at h
    obtain ⟨r, s, hl, h0⟩ := h
    by_cases hr : r = 0; · simp_all
    by_cases hs : s = 0; · simp_all
    suffices
        (B (r • x) (r • x)) * (B (s • y) (s • y)) = (B (r • x) (s • y)) * (B (s • y) (r • x)) by
      simp only [map_smul, smul_apply, smul_eq_mul] at this
      rw [show r * (r * (B x) x) * (s * (s * (B y) y)) = (r * r * s * s) * ((B x) x * (B y) y) by
        ring, show s * (r * (B x) y) * (r * (s * (B y) x)) = (r * r * s * s) * ((B x) y * (B y) x)
        by ring] at this
      have hrs : r * r * s * s ≠ 0 := by simp [hr, hs]
      exact le_of_eq <| mul_right_injective₀ hrs this
    simp [show s • y = - r • x by rwa [neg_smul, ← add_eq_zero_iff_eq_neg']]
  · contrapose!
    intro h
    refine not_linearIndependent_of_apply_mul_apply_eq B hp x y (le_antisymm
      (apply_mul_apply_le_of_forall_zero_le B hle x y) h)

/-- Strict **Cauchy-Schwarz** is equivalent to linear independence for positive definite symmetric
forms. -/
lemma apply_sq_lt_iff_linearIndependent_of_symm [NoZeroSMulDivisors R M]
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (hB : B.IsSymm) (x y : M) :
    (B x y) ^ 2 < (B x x) * (B y y) ↔ LinearIndependent R ![x, y] := by
  rw [show (B x y) ^ 2 = (B x y) * (B y x) by rw [sq, ← hB.eq, RingHom.id_apply]]
  exact apply_mul_apply_lt_iff_linearIndependent B hp x y

lemma apply_apply_same_eq_zero_iff (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) {x : M} :
    B x x = 0 ↔ x ∈ LinearMap.ker B := by
  rw [LinearMap.mem_ker]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext y
  have := B.apply_sq_le_of_symm hs hB x y
  simp only [h, zero_mul] at this
  exact pow_eq_zero <| le_antisymm this (sq_nonneg (B x y))

lemma nondegenerate_iff (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    B.Nondegenerate ↔ ∀ x, B x x = 0 ↔ x = 0 := by
  simp_rw [hB.isRefl.nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot,
    Submodule.eq_bot_iff, B.apply_apply_same_eq_zero_iff hs hB, mem_ker]
  exact forall_congr' fun x ↦ by aesop

/-- A convenience variant of `LinearMap.BilinForm.nondegenerate_iff` characterising nondegeneracy as
positive definiteness. -/
lemma nondegenerate_iff' (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    B.Nondegenerate ↔ ∀ x, x ≠ 0 → 0 < B x x := by
  rw [B.nondegenerate_iff hs hB, ← not_iff_not]
  push_neg
  exact exists_congr fun x ↦ ⟨by aesop, fun ⟨h₀, h⟩ ↦ Or.inl ⟨le_antisymm h (hs x), h₀⟩⟩

lemma nondegenerate_restrict_iff_disjoint_ker (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm)
    {W : Submodule R M} :
    (B.domRestrict₁₂ W W).Nondegenerate ↔ Disjoint W (LinearMap.ker B) := by
  refine ⟨disjoint_ker_of_nondegenerate_restrict, fun hW ↦ ?_⟩
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y ↦ hB.isRefl (W.subtype x) (W.subtype y)
  rw [IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ h
  simp_rw [Subtype.forall, domRestrict₁₂_apply] at h
  specialize h x hx
  rw [B.apply_apply_same_eq_zero_iff hs hB] at h
  have key : x ∈ W ⊓ LinearMap.ker B := ⟨hx, h⟩
  simpa [hW.eq_bot] using key

end BilinForm

end LinearMap
