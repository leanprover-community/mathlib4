/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Dual

/-!
# Bilinear form

This file defines various properties of bilinear forms, including reflexivity, symmetry,
alternativity, adjoint, and non-degeneracy.
For orthogonality, see `LinearAlgebra/BilinearForm/Orthogonal.lean`.

## Notations

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, ie. `B x y = B.bilin x y`.

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

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {M' M'' : Type*}
variable [AddCommMonoid M'] [AddCommMonoid M''] [Module R M'] [Module R M'']
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-! ### Reflexivity, symmetry, and alternativity -/


/-- The proposition that a bilinear form is reflexive -/
def IsRefl (B : BilinForm R M) : Prop := LinearMap.IsRefl B
#align bilin_form.is_refl LinearMap.BilinForm.IsRefl

namespace IsRefl

variable (H : B.IsRefl)

theorem eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun {x y} => H x y
#align bilin_form.is_refl.eq_zero LinearMap.BilinForm.IsRefl.eq_zero

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp
#align bilin_form.is_refl.neg LinearMap.BilinForm.IsRefl.neg

protected theorem smul {α} [CommSemiring α] [Module α R] [SMulCommClass R α R]
    [NoZeroSMulDivisors α R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) :
    (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)
#align bilin_form.is_refl.smul LinearMap.BilinForm.IsRefl.smul

protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp
#align bilin_form.is_refl.group_smul LinearMap.BilinForm.IsRefl.groupSMul

end IsRefl

@[simp]
theorem isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl
#align bilin_form.is_refl_zero LinearMap.BilinForm.isRefl_zero

@[simp]
theorem isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩
#align bilin_form.is_refl_neg LinearMap.BilinForm.isRefl_neg

/-- The proposition that a bilinear form is symmetric -/
def IsSymm (B : BilinForm R M) : Prop := LinearMap.IsSymm B
#align bilin_form.is_symm LinearMap.BilinForm.IsSymm

namespace IsSymm

variable (H : B.IsSymm)

protected theorem eq (x y : M) : B x y = B y x :=
  H x y
#align bilin_form.is_symm.eq LinearMap.BilinForm.IsSymm.eq

theorem isRefl : B.IsRefl := fun x y H1 => H x y ▸ H1
#align bilin_form.is_symm.is_refl LinearMap.BilinForm.IsSymm.isRefl

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ + B₂).IsSymm := fun x y => (congr_arg₂ (· + ·) (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.add LinearMap.BilinForm.IsSymm.add

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ - B₂).IsSymm := fun x y => (congr_arg₂ Sub.sub (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.sub LinearMap.BilinForm.IsSymm.sub

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) : (-B).IsSymm := fun x y =>
  congr_arg Neg.neg (hB x y)
#align bilin_form.is_symm.neg LinearMap.BilinForm.IsSymm.neg

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := fun x y =>
  congr_arg (a • ·) (hB x y)
#align bilin_form.is_symm.smul LinearMap.BilinForm.IsSymm.smul

/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
theorem restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := fun x y => b x y
#align bilin_form.restrict_symm LinearMap.BilinForm.IsSymm.restrict

end IsSymm

@[simp]
theorem isSymm_zero : (0 : BilinForm R M).IsSymm := fun _ _ => rfl
#align bilin_form.is_symm_zero LinearMap.BilinForm.isSymm_zero

@[simp]
theorem isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩
#align bilin_form.is_symm_neg LinearMap.BilinForm.isSymm_neg

variable (R₂) in
theorem isSymm_iff_flip : B.IsSymm ↔ flipHom B = B :=
  (forall₂_congr fun _ _ => by exact eq_comm).trans ext_iff.symm
#align bilin_form.is_symm_iff_flip' LinearMap.BilinForm.isSymm_iff_flip

/-- The proposition that a bilinear form is alternating -/
def IsAlt (B : BilinForm R M) : Prop := LinearMap.IsAlt B
#align bilin_form.is_alt LinearMap.BilinForm.IsAlt

namespace IsAlt

theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 := LinearMap.IsAlt.self_eq_zero H x
#align bilin_form.is_alt.self_eq_zero LinearMap.BilinForm.IsAlt.self_eq_zero

theorem neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := LinearMap.IsAlt.neg H x y
#align bilin_form.is_alt.neg_eq LinearMap.BilinForm.IsAlt.neg_eq

theorem isRefl (H : B₁.IsAlt) : B₁.IsRefl := LinearMap.IsAlt.isRefl H
#align bilin_form.is_alt.is_refl LinearMap.BilinForm.IsAlt.isRefl

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
  fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) : _).trans <| add_zero _
#align bilin_form.is_alt.add LinearMap.BilinForm.IsAlt.add

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
    (B₁ - B₂).IsAlt := fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans <| sub_zero _
#align bilin_form.is_alt.sub LinearMap.BilinForm.IsAlt.sub

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt := fun x =>
  neg_eq_zero.mpr <| hB x
#align bilin_form.is_alt.neg LinearMap.BilinForm.IsAlt.neg

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
  (congr_arg (a • ·) (hB x)).trans <| smul_zero _
#align bilin_form.is_alt.smul LinearMap.BilinForm.IsAlt.smul

end IsAlt

@[simp]
theorem isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl
#align bilin_form.is_alt_zero LinearMap.BilinForm.isAlt_zero

@[simp]
theorem isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩
#align bilin_form.is_alt_neg LinearMap.BilinForm.isAlt_neg

/-! ### Linear adjoints -/


section LinearAdjoints

variable (B) (F : BilinForm R M)
variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable (B' : BilinForm R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def IsAdjointPair :=
  ∀ ⦃x y⦄, B' (f x) y = B x (g y)
#align bilin_form.is_adjoint_pair LinearMap.BilinForm.IsAdjointPair

variable {B B' f f' g g'}

theorem IsAdjointPair.eq (h : IsAdjointPair B B' f g) : ∀ {x y}, B' (f x) y = B x (g y) :=
  @h
#align bilin_form.is_adjoint_pair.eq LinearMap.BilinForm.IsAdjointPair.eq

theorem isAdjointPair_iff_compLeft_eq_compRight (f g : Module.End R M) :
    IsAdjointPair B F f g ↔ F.compLeft f = B.compRight g := by
  constructor <;> intro h
  · ext x
    simp only [compLeft_apply, compRight_apply]
    apply h
  · intro x y
    rw [← compLeft_apply, ← compRight_apply]
    rw [h]
#align bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right LinearMap.BilinForm.isAdjointPair_iff_compLeft_eq_compRight

theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun x y => by
  simp only [BilinForm.zero_left, BilinForm.zero_right, LinearMap.zero_apply]
#align bilin_form.is_adjoint_pair_zero LinearMap.BilinForm.isAdjointPair_zero

theorem isAdjointPair_id : IsAdjointPair B B 1 1 := fun _ _ => rfl
#align bilin_form.is_adjoint_pair_id LinearMap.BilinForm.isAdjointPair_id

theorem IsAdjointPair.add (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x y => by
  rw [LinearMap.add_apply, LinearMap.add_apply, add_left, add_right, h, h']
#align bilin_form.is_adjoint_pair.add LinearMap.BilinForm.IsAdjointPair.add

variable {M₁' : Type*} [AddCommGroup M₁'] [Module R₁ M₁']
variable {B₁' : BilinForm R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}

theorem IsAdjointPair.sub (h : IsAdjointPair B₁ B₁' f₁ g₁) (h' : IsAdjointPair B₁ B₁' f₁' g₁') :
    IsAdjointPair B₁ B₁' (f₁ - f₁') (g₁ - g₁') := fun x y => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_left, sub_right, h, h']
#align bilin_form.is_adjoint_pair.sub LinearMap.BilinForm.IsAdjointPair.sub

variable {B₂' : BilinForm R M'} {f₂ f₂' : M →ₗ[R] M'} {g₂ g₂' : M' →ₗ[R] M}

theorem IsAdjointPair.smul (c : R) (h : IsAdjointPair B B₂' f₂ g₂) :
    IsAdjointPair B B₂' (c • f₂) (c • g₂) := fun x y => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_left, smul_right, h]
#align bilin_form.is_adjoint_pair.smul LinearMap.BilinForm.IsAdjointPair.smul

variable {M'' : Type*} [AddCommMonoid M''] [Module R M'']
variable (B'' : BilinForm R M'')

theorem IsAdjointPair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B' B'' f' g') : IsAdjointPair B B'' (f'.comp f) (g.comp g') := fun x y => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h', h]
#align bilin_form.is_adjoint_pair.comp LinearMap.BilinForm.IsAdjointPair.comp

theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) := fun x y => by
  rw [LinearMap.mul_apply, LinearMap.mul_apply, h, h']
#align bilin_form.is_adjoint_pair.mul LinearMap.BilinForm.IsAdjointPair.mul

variable (B B' B₁ B₂) (F₂ : BilinForm R M)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def IsPairSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B F f f
#align bilin_form.is_pair_self_adjoint LinearMap.BilinForm.IsPairSelfAdjoint

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where
  carrier := { f | IsPairSelfAdjoint B₂ F₂ f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c
#align bilin_form.is_pair_self_adjoint_submodule LinearMap.BilinForm.isPairSelfAdjointSubmodule

@[simp]
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R M) :
    f ∈ isPairSelfAdjointSubmodule B₂ F₂ ↔ IsPairSelfAdjoint B₂ F₂ f := Iff.rfl
#align bilin_form.mem_is_pair_self_adjoint_submodule LinearMap.BilinForm.mem_isPairSelfAdjointSubmodule

theorem isPairSelfAdjoint_equiv (e : M' ≃ₗ[R] M) (f : Module.End R M) :
    IsPairSelfAdjoint B₂ F₂ f ↔
      IsPairSelfAdjoint (B₂.comp ↑e ↑e) (F₂.comp ↑e ↑e) (e.symm.conj f) := by
  have hₗ : (F₂.comp ↑e ↑e).compLeft (e.symm.conj f) = (F₂.compLeft f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.symm_conj_apply]
  have hᵣ : (B₂.comp ↑e ↑e).compRight (e.symm.conj f) = (B₂.compRight f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.conj_apply]
  have he : Function.Surjective (⇑(↑e : M' →ₗ[R] M) : M' → M) := e.surjective
  show BilinForm.IsAdjointPair _ _ _ _ ↔ BilinForm.IsAdjointPair _ _ _ _
  rw [isAdjointPair_iff_compLeft_eq_compRight, isAdjointPair_iff_compLeft_eq_compRight, hᵣ,
    hₗ, comp_inj _ _ he he]
#align bilin_form.is_pair_self_adjoint_equiv LinearMap.BilinForm.isPairSelfAdjoint_equiv

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def IsSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f f
#align bilin_form.is_self_adjoint LinearMap.BilinForm.IsSelfAdjoint

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def IsSkewAdjoint (f : Module.End R₁ M₁) :=
  IsAdjointPair B₁ B₁ f (-f)
#align bilin_form.is_skew_adjoint LinearMap.BilinForm.IsSkewAdjoint

theorem isSkewAdjoint_iff_neg_self_adjoint (f : Module.End R₁ M₁) :
    B₁.IsSkewAdjoint f ↔ IsAdjointPair (-B₁) B₁ f f :=
  show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y) by
    simp only [LinearMap.neg_apply, BilinForm.neg_apply, BilinForm.neg_right]
#align bilin_form.is_skew_adjoint_iff_neg_self_adjoint LinearMap.BilinForm.isSkewAdjoint_iff_neg_self_adjoint

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B B
#align bilin_form.self_adjoint_submodule LinearMap.BilinForm.selfAdjointSubmodule

@[simp]
theorem mem_selfAdjointSubmodule (f : Module.End R M) :
    f ∈ B.selfAdjointSubmodule ↔ B.IsSelfAdjoint f :=
  Iff.rfl
#align bilin_form.mem_self_adjoint_submodule LinearMap.BilinForm.mem_selfAdjointSubmodule

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B₁) B₁
#align bilin_form.skew_adjoint_submodule LinearMap.BilinForm.skewAdjointSubmodule

@[simp]
theorem mem_skewAdjointSubmodule (f : Module.End R₁ M₁) :
    f ∈ B₁.skewAdjointSubmodule ↔ B₁.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl
#align bilin_form.mem_skew_adjoint_submodule LinearMap.BilinForm.mem_skewAdjointSubmodule

end LinearAdjoints

end BilinForm

namespace BilinForm

/-- A nondegenerate bilinear form is a bilinear form such that the only element that is orthogonal
to every other element is `0`; i.e., for all nonzero `m` in `M`, there exists `n` in `M` with
`B m n ≠ 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" nondegeneracy condition one could define a "right"
nondegeneracy condition that in the situation described, `B n m ≠ 0`.  This variant definition is
not currently provided in mathlib. In finite dimension either definition implies the other. -/
def Nondegenerate (B : BilinForm R M) : Prop :=
  ∀ m : M, (∀ n : M, B m n = 0) → m = 0
#align bilin_form.nondegenerate LinearMap.BilinForm.Nondegenerate

section

variable (R M)

/-- In a non-trivial module, zero is not non-degenerate. -/
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h m fun _ => rfl)
#align bilin_form.not_nondegenerate_zero LinearMap.BilinForm.not_nondegenerate_zero

end

variable {M' : Type*}
variable [AddCommMonoid M'] [Module R M']

theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B ≠ 0 :=
  fun h0 => not_nondegenerate_zero R M <| h0 ▸ h
#align bilin_form.nondegenerate.ne_zero LinearMap.BilinForm.Nondegenerate.ne_zero

theorem Nondegenerate.congr {B : BilinForm R M} (e : M ≃ₗ[R] M') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate := fun m hm =>
  e.symm.map_eq_zero_iff.1 <|
    h (e.symm m) fun n => (congr_arg _ (e.symm_apply_apply n).symm).trans (hm (e n))
#align bilin_form.nondegenerate.congr LinearMap.BilinForm.Nondegenerate.congr

@[simp]
theorem nondegenerate_congr_iff {B : BilinForm R M} (e : M ≃ₗ[R] M') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply], Nondegenerate.congr e⟩
#align bilin_form.nondegenerate_congr_iff LinearMap.BilinForm.nondegenerate_congr_iff

/-- A bilinear form is nondegenerate if and only if it has a trivial kernel. -/
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R M} :
    B.Nondegenerate ↔ LinearMap.ker B = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  constructor <;> intro h
  · refine fun m hm => h _ fun x => ?_
    rw [hm]
    rfl
  · intro m hm
    apply h
    ext x
    exact hm x
#align bilin_form.nondegenerate_iff_ker_eq_bot LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot

theorem Nondegenerate.ker_eq_bot {B : BilinForm R M} (h : B.Nondegenerate) :
    LinearMap.ker B = ⊥ := nondegenerate_iff_ker_eq_bot.mp h
#align bilin_form.nondegenerate.ker_eq_bot LinearMap.BilinForm.Nondegenerate.ker_eq_bot

theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h => by
  ext w
  refine eq_of_sub_eq_zero (b _ ?_)
  intro v
  rw [sub_left, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]
#align bilin_form.comp_left_injective LinearMap.BilinForm.compLeft_injective

theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
  B.compLeft_injective b <| ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
#align bilin_form.is_adjoint_pair_unique_of_nondegenerate LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate

section FiniteDimensional

variable [FiniteDimensional K V]

/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.toDual` is
the linear equivalence between a vector space and its dual. -/
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm
#align bilin_form.to_dual LinearMap.BilinForm.toDual

theorem toDual_def {B : BilinForm K V} (b : B.SeparatingLeft) {m n : V} : B.toDual b m n = B m n :=
  rfl
#align bilin_form.to_dual_def LinearMap.BilinForm.toDual_def

@[simp]
lemma apply_toDual_symm_apply {B : BilinForm K V} {hB : B.Nondegenerate}
    (f : Module.Dual K V) (v : V) :
    B ((B.toDual hB).symm f) v = f v := by
  change B.toDual hB ((B.toDual hB).symm f) v = f v
  simp only [LinearEquiv.apply_symm_apply]

lemma Nondegenerate.flip {B : BilinForm K V} (hB : B.Nondegenerate) :
    B.flip.Nondegenerate := by
  intro x hx
  apply (Module.evalEquiv K V).injective
  ext f
  obtain ⟨y, rfl⟩ := (B.toDual hB).surjective f
  simpa using hx y

lemma nonDegenerateFlip_iff {B : BilinForm K V} :
    B.flip.Nondegenerate ↔ B.Nondegenerate := ⟨Nondegenerate.flip, Nondegenerate.flip⟩

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Finite ι]

/-- The `B`-dual basis `B.dualBasis hB b` to a finite basis `b` satisfies
`B (B.dualBasis hB b i) (b j) = B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis. -/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    Basis ι K V :=
  haveI := FiniteDimensional.of_fintype_basis b
  b.dualBasis.map (B.toDual hB).symm
#align bilin_form.dual_basis LinearMap.BilinForm.dualBasis

@[simp]
theorem dualBasis_repr_apply (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  rw [dualBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, toDual_def]
#align bilin_form.dual_basis_repr_apply LinearMap.BilinForm.dualBasis_repr_apply

theorem apply_dualBasis_left (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  have := FiniteDimensional.of_fintype_basis b
  rw [dualBasis, Basis.map_apply, Basis.coe_dualBasis, ← toDual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
#align bilin_form.apply_dual_basis_left LinearMap.BilinForm.apply_dualBasis_left

theorem apply_dualBasis_right (B : BilinForm K V) (hB : B.Nondegenerate) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [sym.eq, apply_dualBasis_left]
#align bilin_form.apply_dual_basis_right LinearMap.BilinForm.apply_dualBasis_right

@[simp]
lemma dualBasis_dualBasis_flip (B : BilinForm K V) (hB : B.Nondegenerate) {ι}
    [Finite ι] [DecidableEq ι] (b : Basis ι K V) :
    B.dualBasis hB (B.flip.dualBasis hB.flip b) = b := by
  ext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((B.flip.dualBasis hB.flip b).ext (fun j ↦ ?_))
  simp_rw [apply_dualBasis_left, ← B.flip_apply, apply_dualBasis_left, @eq_comm _ i j]

@[simp]
lemma dualBasis_flip_dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) {ι}
    [Finite ι] [DecidableEq ι] [FiniteDimensional K V] (b : Basis ι K V) :
    B.flip.dualBasis hB.flip (B.dualBasis hB b) = b :=
  dualBasis_dualBasis_flip _ hB.flip b

@[simp]
lemma dualBasis_dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (hB' : B.IsSymm) {ι}
    [Finite ι] [DecidableEq ι] [FiniteDimensional K V] (b : Basis ι K V) :
    B.dualBasis hB (B.dualBasis hB b) = b := by
  convert dualBasis_dualBasis_flip _ hB.flip b
  rwa [eq_comm, ← isSymm_iff_flip]

end DualBasis

section LinearAdjoints

/-- Given bilinear forms `B₁, B₂` where `B₂` is nondegenerate, `symmCompOfNondegenerate`
is the linear map `B₂ ∘ B₁`. -/
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) :
    V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁
#align bilin_form.symm_comp_of_nondegenerate LinearMap.BilinForm.symmCompOfNondegenerate

theorem comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v : V) :
    B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = B₁ v := by
  erw [symmCompOfNondegenerate]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, DFunLike.coe_fn_eq]
  erw [LinearEquiv.apply_symm_apply (B₂.toDual b₂)]
#align bilin_form.comp_symm_comp_of_nondegenerate_apply LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply

@[simp]
theorem symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [comp_symmCompOfNondegenerate_apply]
#align bilin_form.symm_comp_of_nondegenerate_left_apply LinearMap.BilinForm.symmCompOfNondegenerate_left_apply

/-- Given the nondegenerate bilinear form `B` and the linear map `φ`,
`leftAdjointOfNondegenerate` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `BilinForm.isAdjointPairLeftAdjointOfNondegenerate`. -/
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b
#align bilin_form.left_adjoint_of_nondegenerate LinearMap.BilinForm.leftAdjointOfNondegenerate

theorem isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x
#align bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate

/-- Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left adjoint given by
`BilinForm.leftAdjointOfNondegenerate`. -/
theorem isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (ψ φ : V →ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩
#align bilin_form.is_adjoint_pair_iff_eq_of_nondegenerate LinearMap.BilinForm.isAdjointPair_iff_eq_of_nondegenerate

end LinearAdjoints

end FiniteDimensional

end BilinForm

end LinearMap
