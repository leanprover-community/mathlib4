/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying, Christopher Hoskin
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.LinearAlgebra.SesquilinearForm.Hom

/-!
# Bilinear form

Properties of separating left bilinear forms

-/

variable {R R₁ R₂ R₃ M M₁ M₂ M₃ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

open LinearMap (BilinForm)

namespace LinearMap

namespace BilinForm

section

variable [CommRing R₁]

variable [AddCommGroup M₁] [Module R₁ M₁]

theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.SeparatingLeft) :
    Function.Injective (B.compLeft) := fun φ ψ h => by
  ext w
  refine' eq_of_sub_eq_zero (b _ _)
  intro v
  rw [map_sub, sub_apply, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]
#align bilin_form.comp_left_injective LinearMap.BilinForm.compLeft_injective

theorem isAdjointPair_unique_of_separatingLeft (B : BilinForm R₁ M₁) (b : B.SeparatingLeft)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ := by
  apply B.compLeft_injective b
  ext v w
  rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
#align bilin_form.is_adjoint_pair_unique_of_nondegenerate LinearMap.BilinForm.isAdjointPair_unique_of_separatingLeft

end

section FiniteDimensional

variable [Field K] [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

/-- Given a left-separating bilinear form `B` on a finite-dimensional vector space, `B.toDual` is
the linear equivalence between a vector space and its dual with the underlying linear map
`B.toLin`. -/
noncomputable def toDual (B : BilinForm K V) (b : B.SeparatingLeft) : V ≃ₗ[K] Module.Dual K V :=
  B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| LinearMap.separatingLeft_iff_ker_eq_bot.mp b)
    Subspace.dual_finrank_eq.symm
#align bilin_form.to_dual LinearMap.BilinForm.toDual

theorem toDual_def {B : BilinForm K V} (b : B.SeparatingLeft) {m n : V} : B.toDual b m n = B m n :=
  rfl
#align bilin_form.to_dual_def LinearMap.BilinForm.toDual_def

lemma SeparatingLeft.flip {B : BilinForm K V} (hB : B.SeparatingLeft) :
    B.flip.SeparatingLeft := by
  intro x hx
  apply (Module.evalEquiv K V).injective
  ext f
  obtain ⟨y, rfl⟩ := (B.toDual hB).surjective f
  simpa using hx y

lemma separatingLeftFlip_iff {B : BilinForm K V} :
    B.flip.SeparatingLeft ↔ B.SeparatingLeft := ⟨SeparatingLeft.flip, SeparatingLeft.flip⟩

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Finite ι]

/-- The `B`-dual basis `B.dualBasis hB b` to a finite basis `b` satisfies
`B (B.dualBasis hB b i) (b j) = B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0`,
where `B` is a left-separating (symmetric) bilinear form and `b` is a finite basis. -/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.SeparatingLeft) (b : Basis ι K V) :
    Basis ι K V :=
  haveI := FiniteDimensional.of_fintype_basis b
  b.dualBasis.map (B.toDual hB).symm
#align bilin_form.dual_basis LinearMap.BilinForm.dualBasis

@[simp]
theorem dualBasis_repr_apply (B : BilinForm K V) (hB : B.SeparatingLeft) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  rw [dualBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, toDual_def]
#align bilin_form.dual_basis_repr_apply LinearMap.BilinForm.dualBasis_repr_apply

theorem apply_dualBasis_left (B : BilinForm K V) (hB : B.SeparatingLeft) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  have := FiniteDimensional.of_fintype_basis b
  rw [dualBasis, Basis.map_apply, Basis.coe_dualBasis, ← toDual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
#align bilin_form.apply_dual_basis_left LinearMap.BilinForm.apply_dualBasis_left

theorem apply_dualBasis_right (B : BilinForm K V) (hB : B.SeparatingLeft) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [← sym.eq, apply_dualBasis_left]
  rfl
#align bilin_form.apply_dual_basis_right LinearMap.BilinForm.apply_dualBasis_right

@[simp]
lemma dualBasis_dualBasis_flip (B : BilinForm K V) (hB : B.SeparatingLeft) {ι}
    [Finite ι] [DecidableEq ι] (b : Basis ι K V) :
    B.dualBasis hB (dualBasis B.flip (LinearMap.BilinForm.SeparatingLeft.flip hB) b) = b := by
  ext i
  refine LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hB)
    ((dualBasis B.flip (LinearMap.BilinForm.SeparatingLeft.flip hB) b).ext (fun j ↦ ?_))
  rw [apply_dualBasis_left, ← B.flip_apply (R₂ := K),
    apply_dualBasis_left]
  simp_rw [@eq_comm _ i j]

@[simp]
lemma dualBasis_flip_dualBasis (B : BilinForm K V) (hB : B.SeparatingLeft) {ι}
    [Finite ι] [DecidableEq ι] [FiniteDimensional K V] (b : Basis ι K V) :
    LinearMap.BilinForm.dualBasis B.flip (LinearMap.BilinForm.SeparatingLeft.flip hB)
    (B.dualBasis hB b) = b :=
  dualBasis_dualBasis_flip _ (LinearMap.BilinForm.SeparatingLeft.flip hB) b

@[simp]
lemma dualBasis_dualBasis (B : BilinForm K V) (hB : B.SeparatingLeft) (hB' : B.IsSymm) {ι}
    [Finite ι] [DecidableEq ι] [FiniteDimensional K V] (b : Basis ι K V) :
    B.dualBasis hB (B.dualBasis hB b) = b := by
  convert dualBasis_dualBasis_flip _ (LinearMap.BilinForm.SeparatingLeft.flip hB) b
  exact isSymm_iff_eq_flip.mp hB'

end DualBasis

section LinearAdjoints

/-- Given bilinear forms `B₁, B₂` where `B₂` is left-separating, `symmCompOfSeparatingLeft`
is the linear map `B₂.toLin⁻¹ ∘ B₁.toLin`. -/
noncomputable def symmCompOfSeparatingLeft (B₁ B₂ : BilinForm K V) (b₂ : B₂.SeparatingLeft) :
    V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁
#align bilin_form.symm_comp_of_nondegenerate LinearMap.BilinForm.symmCompOfSeparatingLeft

theorem comp_symmCompOfSeparatingLeft_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.SeparatingLeft) (v : V) :
    B₂ (B₁.symmCompOfSeparatingLeft B₂ b₂ v) = B₁ v := by
  erw [symmCompOfSeparatingLeft, LinearEquiv.apply_symm_apply (B₂.toDual b₂) _]
#align bilin_form.comp_symm_comp_of_nondegenerate_apply LinearMap.BilinForm.comp_symmCompOfSeparatingLeft_apply

@[simp]
theorem symmCompOfSeparatingLeft_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.SeparatingLeft) (v w : V) : B₂ (symmCompOfSeparatingLeft B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [comp_symmCompOfSeparatingLeft_apply]
#align bilin_form.symm_comp_of_nondegenerate_left_apply LinearMap.BilinForm.symmCompOfSeparatingLeft_left_apply

/-- Given the left-separating bilinear form `B` and the linear map `φ`,
`leftAdjointOfSeparatingLeft` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `BilinForm.isAdjointPairLeftAdjointOfSeparatingLeft`. -/
noncomputable def leftAdjointOfSeparatingLeft (B : BilinForm K V) (b : B.SeparatingLeft)
    (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfSeparatingLeft (B.compRight φ) B b
#align bilin_form.left_adjoint_of_nondegenerate LinearMap.BilinForm.leftAdjointOfSeparatingLeft

theorem isAdjointPairLeftAdjointOfSeparatingLeft (B : BilinForm K V) (b : B.SeparatingLeft)
    (φ : V →ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfSeparatingLeft b φ) φ := fun x y =>
  LinearMap.BilinForm.symmCompOfSeparatingLeft_left_apply (B.compRight φ) b y x
#align bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate LinearMap.BilinForm.isAdjointPairLeftAdjointOfSeparatingLeft

/-- Given the left-separating bilinear form `B`, the linear map `φ` has a unique left adjoint given
by `BilinForm.leftAdjointOfSeparatingLeft`. -/
theorem isAdjointPair_iff_eq_of_separatingLeft (B : BilinForm K V) (b : B.SeparatingLeft)
    (ψ φ : V →ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfSeparatingLeft b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_separatingLeft b φ ψ _ h
      (isAdjointPairLeftAdjointOfSeparatingLeft _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfSeparatingLeft _ _ _⟩
#align bilin_form.is_adjoint_pair_iff_eq_of_nondegenerate LinearMap.BilinForm.isAdjointPair_iff_eq_of_separatingLeft

end LinearAdjoints

end FiniteDimensional

end BilinForm

end LinearMap
