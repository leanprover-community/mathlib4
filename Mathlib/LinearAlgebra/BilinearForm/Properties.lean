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
 - `M`, `M'`, ... are modules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/


open BigOperators

universe u v w

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type*} {M₁ : Type*} [Ring R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]

variable {R₃ : Type*} {M₃ : Type*} [CommRing R₃] [AddCommGroup M₃] [Module R₃ M₃]

variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {M₂' M₂'' : Type*}
variable [AddCommMonoid M₂'] [AddCommMonoid M₂''] [Module R₂ M₂'] [Module R₂ M₂'']

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁} {B₂ : BilinForm R₂ M₂}

namespace BilinForm

/-! ### Reflexivity, symmetry, and alternativity -/


/-- The proposition that a bilinear form is reflexive -/
def IsRefl (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = 0 → B y x = 0
#align bilin_form.is_refl BilinForm.IsRefl

namespace IsRefl

variable (H : B.IsRefl)

theorem eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun {x y} => H x y
#align bilin_form.is_refl.eq_zero BilinForm.IsRefl.eq_zero

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp
#align bilin_form.is_refl.neg BilinForm.IsRefl.neg

protected theorem smul {α} [Semiring α] [Module α R] [SMulCommClass α R R] [NoZeroSMulDivisors α R]
    (a : α) {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)
#align bilin_form.is_refl.smul BilinForm.IsRefl.smul

protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp
#align bilin_form.is_refl.group_smul BilinForm.IsRefl.groupSMul

end IsRefl

@[simp]
theorem isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl
#align bilin_form.is_refl_zero BilinForm.isRefl_zero

@[simp]
theorem isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩
#align bilin_form.is_refl_neg BilinForm.isRefl_neg

/-- The proposition that a bilinear form is symmetric -/
def IsSymm (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = B y x
#align bilin_form.is_symm BilinForm.IsSymm

namespace IsSymm

variable (H : B.IsSymm)

protected theorem eq (x y : M) : B x y = B y x :=
  H x y
#align bilin_form.is_symm.eq BilinForm.IsSymm.eq

theorem isRefl : B.IsRefl := fun x y H1 => H x y ▸ H1
#align bilin_form.is_symm.is_refl BilinForm.IsSymm.isRefl

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ + B₂).IsSymm := fun x y => (congr_arg₂ (· + ·) (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.add BilinForm.IsSymm.add

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ - B₂).IsSymm := fun x y => (congr_arg₂ Sub.sub (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.sub BilinForm.IsSymm.sub

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) : (-B).IsSymm := fun x y =>
  congr_arg Neg.neg (hB x y)
#align bilin_form.is_symm.neg BilinForm.IsSymm.neg

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := fun x y =>
  congr_arg (a • ·) (hB x y)
#align bilin_form.is_symm.smul BilinForm.IsSymm.smul

/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
theorem restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := fun x y => b x y
#align bilin_form.restrict_symm BilinForm.IsSymm.restrict

end IsSymm

@[simp]
theorem isSymm_zero : (0 : BilinForm R M).IsSymm := fun _ _ => rfl
#align bilin_form.is_symm_zero BilinForm.isSymm_zero

@[simp]
theorem isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩
#align bilin_form.is_symm_neg BilinForm.isSymm_neg

variable (R₂) in
theorem isSymm_iff_flip [Algebra R₂ R] : B.IsSymm ↔ flipHom R₂ B = B :=
  (forall₂_congr fun _ _ => by exact eq_comm).trans ext_iff.symm
#align bilin_form.is_symm_iff_flip' BilinForm.isSymm_iff_flip

/-- The proposition that a bilinear form is alternating -/
def IsAlt (B : BilinForm R M) : Prop :=
  ∀ x : M, B x x = 0
#align bilin_form.is_alt BilinForm.IsAlt

namespace IsAlt

theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 :=
  H x
#align bilin_form.is_alt.self_eq_zero BilinForm.IsAlt.self_eq_zero

theorem neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := by
  have H1 : B₁ (x + y) (x + y) = 0 := self_eq_zero H (x + y)
  rw [add_left, add_right, add_right, self_eq_zero H, self_eq_zero H, zero_add, add_zero,
    add_eq_zero_iff_neg_eq] at H1
  exact H1
#align bilin_form.is_alt.neg_eq BilinForm.IsAlt.neg_eq

theorem isRefl (H : B₁.IsAlt) : B₁.IsRefl := by
  intro x y h
  rw [← neg_eq H, h, neg_zero]
#align bilin_form.is_alt.is_refl BilinForm.IsAlt.isRefl

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
  fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) : _).trans <| add_zero _
#align bilin_form.is_alt.add BilinForm.IsAlt.add

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
    (B₁ - B₂).IsAlt := fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans <| sub_zero _
#align bilin_form.is_alt.sub BilinForm.IsAlt.sub

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt := fun x =>
  neg_eq_zero.mpr <| hB x
#align bilin_form.is_alt.neg BilinForm.IsAlt.neg

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
  (congr_arg (a • ·) (hB x)).trans <| smul_zero _
#align bilin_form.is_alt.smul BilinForm.IsAlt.smul

end IsAlt

@[simp]
theorem isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl
#align bilin_form.is_alt_zero BilinForm.isAlt_zero

@[simp]
theorem isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩
#align bilin_form.is_alt_neg BilinForm.isAlt_neg

/-! ### Linear adjoints -/


section LinearAdjoints

variable (B) (F : BilinForm R M)

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

variable (B' : BilinForm R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def IsAdjointPair :=
  ∀ ⦃x y⦄, B' (f x) y = B x (g y)
#align bilin_form.is_adjoint_pair BilinForm.IsAdjointPair

variable {B B' f f' g g'}

theorem IsAdjointPair.eq (h : IsAdjointPair B B' f g) : ∀ {x y}, B' (f x) y = B x (g y) :=
  @h
#align bilin_form.is_adjoint_pair.eq BilinForm.IsAdjointPair.eq

theorem isAdjointPair_iff_compLeft_eq_compRight (f g : Module.End R M) :
    IsAdjointPair B F f g ↔ F.compLeft f = B.compRight g := by
  constructor <;> intro h
  · ext x
    simp only [compLeft_apply, compRight_apply]
    apply h
  · intro x y
    rw [← compLeft_apply, ← compRight_apply]
    rw [h]
#align bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right BilinForm.isAdjointPair_iff_compLeft_eq_compRight

theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun x y => by
  simp only [BilinForm.zero_left, BilinForm.zero_right, LinearMap.zero_apply]
#align bilin_form.is_adjoint_pair_zero BilinForm.isAdjointPair_zero

theorem isAdjointPair_id : IsAdjointPair B B 1 1 := fun _ _ => rfl
#align bilin_form.is_adjoint_pair_id BilinForm.isAdjointPair_id

theorem IsAdjointPair.add (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x y => by
  rw [LinearMap.add_apply, LinearMap.add_apply, add_left, add_right, h, h']
#align bilin_form.is_adjoint_pair.add BilinForm.IsAdjointPair.add

variable {M₁' : Type*} [AddCommGroup M₁'] [Module R₁ M₁']

variable {B₁' : BilinForm R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}

theorem IsAdjointPair.sub (h : IsAdjointPair B₁ B₁' f₁ g₁) (h' : IsAdjointPair B₁ B₁' f₁' g₁') :
    IsAdjointPair B₁ B₁' (f₁ - f₁') (g₁ - g₁') := fun x y => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_left, sub_right, h, h']
#align bilin_form.is_adjoint_pair.sub BilinForm.IsAdjointPair.sub

variable {B₂' : BilinForm R₂ M₂'} {f₂ f₂' : M₂ →ₗ[R₂] M₂'} {g₂ g₂' : M₂' →ₗ[R₂] M₂}

theorem IsAdjointPair.smul (c : R₂) (h : IsAdjointPair B₂ B₂' f₂ g₂) :
    IsAdjointPair B₂ B₂' (c • f₂) (c • g₂) := fun x y => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_left, smul_right, h]
#align bilin_form.is_adjoint_pair.smul BilinForm.IsAdjointPair.smul

variable {M'' : Type*} [AddCommMonoid M''] [Module R M'']

variable (B'' : BilinForm R M'')

theorem IsAdjointPair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B' B'' f' g') : IsAdjointPair B B'' (f'.comp f) (g.comp g') := fun x y => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h', h]
#align bilin_form.is_adjoint_pair.comp BilinForm.IsAdjointPair.comp

theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) := fun x y => by
  rw [LinearMap.mul_apply, LinearMap.mul_apply, h, h']
#align bilin_form.is_adjoint_pair.mul BilinForm.IsAdjointPair.mul

variable (B B' B₁ B₂) (F₂ : BilinForm R₂ M₂)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def IsPairSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B F f f
#align bilin_form.is_pair_self_adjoint BilinForm.IsPairSelfAdjoint

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def isPairSelfAdjointSubmodule : Submodule R₂ (Module.End R₂ M₂) where
  carrier := { f | IsPairSelfAdjoint B₂ F₂ f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c
#align bilin_form.is_pair_self_adjoint_submodule BilinForm.isPairSelfAdjointSubmodule

@[simp]
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R₂ M₂) :
    f ∈ isPairSelfAdjointSubmodule B₂ F₂ ↔ IsPairSelfAdjoint B₂ F₂ f := Iff.rfl
#align bilin_form.mem_is_pair_self_adjoint_submodule BilinForm.mem_isPairSelfAdjointSubmodule

theorem isPairSelfAdjoint_equiv (e : M₂' ≃ₗ[R₂] M₂) (f : Module.End R₂ M₂) :
    IsPairSelfAdjoint B₂ F₂ f ↔
      IsPairSelfAdjoint (B₂.comp ↑e ↑e) (F₂.comp ↑e ↑e) (e.symm.conj f) := by
  have hₗ : (F₂.comp ↑e ↑e).compLeft (e.symm.conj f) = (F₂.compLeft f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.symm_conj_apply]
  have hᵣ : (B₂.comp ↑e ↑e).compRight (e.symm.conj f) = (B₂.compRight f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.conj_apply]
  have he : Function.Surjective (⇑(↑e : M₂' →ₗ[R₂] M₂) : M₂' → M₂) := e.surjective
  show BilinForm.IsAdjointPair _ _ _ _ ↔ BilinForm.IsAdjointPair _ _ _ _
  rw [isAdjointPair_iff_compLeft_eq_compRight, isAdjointPair_iff_compLeft_eq_compRight, hᵣ,
    hₗ, comp_inj _ _ he he]
#align bilin_form.is_pair_self_adjoint_equiv BilinForm.isPairSelfAdjoint_equiv

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def IsSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f f
#align bilin_form.is_self_adjoint BilinForm.IsSelfAdjoint

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def IsSkewAdjoint (f : Module.End R₁ M₁) :=
  IsAdjointPair B₁ B₁ f (-f)
#align bilin_form.is_skew_adjoint BilinForm.IsSkewAdjoint

theorem isSkewAdjoint_iff_neg_self_adjoint (f : Module.End R₁ M₁) :
    B₁.IsSkewAdjoint f ↔ IsAdjointPair (-B₁) B₁ f f :=
  show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y) by
    simp only [LinearMap.neg_apply, BilinForm.neg_apply, BilinForm.neg_right]
#align bilin_form.is_skew_adjoint_iff_neg_self_adjoint BilinForm.isSkewAdjoint_iff_neg_self_adjoint

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B₂ B₂
#align bilin_form.self_adjoint_submodule BilinForm.selfAdjointSubmodule

@[simp]
theorem mem_selfAdjointSubmodule (f : Module.End R₂ M₂) :
    f ∈ B₂.selfAdjointSubmodule ↔ B₂.IsSelfAdjoint f :=
  Iff.rfl
#align bilin_form.mem_self_adjoint_submodule BilinForm.mem_selfAdjointSubmodule

variable (B₃ : BilinForm R₃ M₃)

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B₃) B₃
#align bilin_form.skew_adjoint_submodule BilinForm.skewAdjointSubmodule

@[simp]
theorem mem_skewAdjointSubmodule (f : Module.End R₃ M₃) :
    f ∈ B₃.skewAdjointSubmodule ↔ B₃.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl
#align bilin_form.mem_skew_adjoint_submodule BilinForm.mem_skewAdjointSubmodule

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
#align bilin_form.nondegenerate BilinForm.Nondegenerate

section

variable (R M)

/-- In a non-trivial module, zero is not non-degenerate. -/
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h m fun _ => rfl)
#align bilin_form.not_nondegenerate_zero BilinForm.not_nondegenerate_zero

end

variable {M₂' : Type*}

variable [AddCommMonoid M₂'] [Module R₂ M₂']

theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B ≠ 0 :=
  fun h0 => not_nondegenerate_zero R M <| h0 ▸ h
#align bilin_form.nondegenerate.ne_zero BilinForm.Nondegenerate.ne_zero

theorem Nondegenerate.congr {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate := fun m hm =>
  e.symm.map_eq_zero_iff.1 <|
    h (e.symm m) fun n => (congr_arg _ (e.symm_apply_apply n).symm).trans (hm (e n))
#align bilin_form.nondegenerate.congr BilinForm.Nondegenerate.congr

@[simp]
theorem nondegenerate_congr_iff {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply], Nondegenerate.congr e⟩
#align bilin_form.nondegenerate_congr_iff BilinForm.nondegenerate_congr_iff

/-- A bilinear form is nondegenerate if and only if it has a trivial kernel. -/
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R₂ M₂} :
    B.Nondegenerate ↔ LinearMap.ker (BilinForm.toLin B) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  constructor <;> intro h
  · refine' fun m hm => h _ fun x => _
    rw [← toLin_apply, hm]
    rfl
  · intro m hm
    apply h
    ext x
    exact hm x
#align bilin_form.nondegenerate_iff_ker_eq_bot BilinForm.nondegenerate_iff_ker_eq_bot

theorem Nondegenerate.ker_eq_bot {B : BilinForm R₂ M₂} (h : B.Nondegenerate) :
    LinearMap.ker (BilinForm.toLin B) = ⊥ :=
  nondegenerate_iff_ker_eq_bot.mp h
#align bilin_form.nondegenerate.ker_eq_bot BilinForm.Nondegenerate.ker_eq_bot

theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h => by
  ext w
  refine' eq_of_sub_eq_zero (b _ _)
  intro v
  rw [sub_left, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]
#align bilin_form.comp_left_injective BilinForm.compLeft_injective

theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
  B.compLeft_injective b <| ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
#align bilin_form.is_adjoint_pair_unique_of_nondegenerate BilinForm.isAdjointPair_unique_of_nondegenerate

section FiniteDimensional

variable [FiniteDimensional K V]

/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.toDual` is
the linear equivalence between a vector space and its dual with the underlying linear map
`B.toLin`. -/
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.toLin.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm
#align bilin_form.to_dual BilinForm.toDual

theorem toDual_def {B : BilinForm K V} (b : B.Nondegenerate) {m n : V} : B.toDual b m n = B m n :=
  rfl
#align bilin_form.to_dual_def BilinForm.toDual_def

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
#align bilin_form.dual_basis BilinForm.dualBasis

@[simp]
theorem dualBasis_repr_apply (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  rw [dualBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, toDual_def]
#align bilin_form.dual_basis_repr_apply BilinForm.dualBasis_repr_apply

theorem apply_dualBasis_left (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  have := FiniteDimensional.of_fintype_basis b
  rw [dualBasis, Basis.map_apply, Basis.coe_dualBasis, ← toDual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
#align bilin_form.apply_dual_basis_left BilinForm.apply_dualBasis_left

theorem apply_dualBasis_right (B : BilinForm K V) (hB : B.Nondegenerate) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [sym, apply_dualBasis_left]
#align bilin_form.apply_dual_basis_right BilinForm.apply_dualBasis_right

@[simp]
lemma dualBasis_dualBasis_flip (B : BilinForm K V) (hB : B.Nondegenerate) {ι}
    [Finite ι] [DecidableEq ι] (b : Basis ι K V) :
    B.dualBasis hB (B.flip.dualBasis hB.flip b) = b := by
  ext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((B.flip.dualBasis hB.flip b).ext (fun j ↦ ?_))
  rw [toLin_apply, apply_dualBasis_left, toLin_apply, ← B.flip_apply (R₂ := K),
    apply_dualBasis_left]
  simp_rw [@eq_comm _ i j]

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
is the linear map `B₂.toLin⁻¹ ∘ B₁.toLin`. -/
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) :
    V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp (BilinForm.toLin B₁)
#align bilin_form.symm_comp_of_nondegenerate BilinForm.symmCompOfNondegenerate

theorem comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v : V) :
    toLin B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = toLin B₁ v := by
  erw [symmCompOfNondegenerate, LinearEquiv.apply_symm_apply (B₂.toDual b₂) _]
#align bilin_form.comp_symm_comp_of_nondegenerate_apply BilinForm.comp_symmCompOfNondegenerate_apply

@[simp]
theorem symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [← BilinForm.toLin_apply, comp_symmCompOfNondegenerate_apply]
#align bilin_form.symm_comp_of_nondegenerate_left_apply BilinForm.symmCompOfNondegenerate_left_apply

/-- Given the nondegenerate bilinear form `B` and the linear map `φ`,
`leftAdjointOfNondegenerate` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `BilinForm.isAdjointPairLeftAdjointOfNondegenerate`. -/
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b
#align bilin_form.left_adjoint_of_nondegenerate BilinForm.leftAdjointOfNondegenerate

theorem isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x
#align bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate BilinForm.isAdjointPairLeftAdjointOfNondegenerate

/-- Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left adjoint given by
`BilinForm.leftAdjointOfNondegenerate`. -/
theorem isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (ψ φ : V →ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩
#align bilin_form.is_adjoint_pair_iff_eq_of_nondegenerate BilinForm.isAdjointPair_iff_eq_of_nondegenerate

end LinearAdjoints

end FiniteDimensional

end BilinForm
