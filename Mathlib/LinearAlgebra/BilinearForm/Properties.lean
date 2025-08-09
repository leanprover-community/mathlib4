/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Bilinear form

This file defines various properties of bilinear forms, including reflexivity, symmetry,
alternativity, adjoint, and non-degeneracy.
For orthogonality, see `Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean`.

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
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-! ### Reflexivity, symmetry, and alternativity -/


/-- The proposition that a bilinear form is reflexive -/
def IsRefl (B : BilinForm R M) : Prop := LinearMap.IsRefl B

namespace IsRefl

theorem eq_zero (H : B.IsRefl) : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun {x y} => H x y

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp

protected theorem smul {α} [Semiring α] [Module α R] [SMulCommClass R α R]
    [NoZeroSMulDivisors α R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) :
    (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)

protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp

end IsRefl

@[simp]
theorem isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl

@[simp]
theorem isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩

/-- The proposition that a bilinear form is symmetric -/
structure IsSymm (B : BilinForm R M) : Prop where
  protected eq : ∀ x y, B x y = B y x

theorem isSymm_def : IsSymm B ↔ ∀ x y, B x y = B y x where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

theorem isSymm_iff : IsSymm B ↔ LinearMap.IsSymm B := by
  simp [isSymm_def, LinearMap.isSymm_def]

namespace IsSymm

theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 => H.eq x y ▸ H1

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ + B₂).IsSymm := ⟨fun x y => (congr_arg₂ (· + ·) (hB₁.eq x y) (hB₂.eq x y) :)⟩

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ - B₂).IsSymm := ⟨fun x y => (congr_arg₂ Sub.sub (hB₁.eq x y) (hB₂.eq x y) :)⟩

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) : (-B).IsSymm := ⟨fun x y =>
  congr_arg Neg.neg (hB.eq x y)⟩

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := ⟨fun x y =>
  congr_arg (a • ·) (hB.eq x y)⟩

/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
theorem restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := ⟨fun x y => b.eq x y⟩

end IsSymm

@[simp]
theorem isSymm_zero : (0 : BilinForm R M).IsSymm := ⟨fun _ _ => rfl⟩

@[simp]
theorem isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩

theorem isSymm_iff_flip : B.IsSymm ↔ flipHom B = B where
  mp := fun ⟨h⟩ ↦ by ext; simp [h]
  mpr h := ⟨fun x y ↦ by rw [← flip_apply, h]⟩

section polarization

variable {R : Type*} [Field R] [NeZero (2 : R)] [Module R M] {B C : BilinForm R M}

/-- Polarization identity: a symmetric bilinear form can be expressed through the values
it takes on the diagonal. -/
lemma IsSymm.polarization (x y : M) (hB : B.IsSymm) :
    B x y = (B (x + y) (x + y) - B x x - B y y) / 2 := by
  simp only [map_add, LinearMap.add_apply]
  rw [hB.eq y x]
  ring_nf
  rw [mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one]

/-- A symmetric bilinear form is characterized by the values it takes on the diagonal. -/
lemma ext_of_isSymm (hB : IsSymm B) (hC : IsSymm C)
    (h : ∀ x, B x x = C x x) : B = C := by
  ext x y
  rw [hB.polarization, hC.polarization]
  simp_rw [h]

/-- A symmetric bilinear form is characterized by the values it takes on the diagonal. -/
lemma ext_iff_of_isSymm (hB : IsSymm B) (hC : IsSymm C) :
    B = C ↔ ∀ x, B x x = C x x where
  mp h := by simp [h]
  mpr := ext_of_isSymm hB hC

end polarization

lemma isSymm_iff_basis {ι : Type*} (b : Basis ι R M) :
    IsSymm B ↔ ∀ i j, B (b i) (b j) = B (b j) (b i) where
  mp := fun ⟨h⟩ i j ↦ h _ _
  mpr := by
    refine fun h ↦ ⟨fun x y ↦ ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x ∈ Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y ∈ Submodule.span R (Set.range b))
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, coeFn_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ ↦ Finset.sum_congr rfl fun b₂ h₂ ↦ ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

/-- The proposition that a bilinear form is alternating -/
def IsAlt (B : BilinForm R M) : Prop := LinearMap.IsAlt B

namespace IsAlt

theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 := LinearMap.IsAlt.self_eq_zero H x

theorem neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := LinearMap.IsAlt.neg H x y

theorem isRefl (H : B₁.IsAlt) : B₁.IsRefl := LinearMap.IsAlt.isRefl H

theorem eq_of_add_add_eq_zero [IsCancelAdd R] {a b c : M} (H : B.IsAlt) (hAdd : a + b + c = 0) :
    B a b = B b c := LinearMap.IsAlt.eq_of_add_add_eq_zero H hAdd

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
  fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) :).trans <| add_zero _

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
    (B₁ - B₂).IsAlt := fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans <| sub_zero _

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt := fun x =>
  neg_eq_zero.mpr <| hB x

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
  (congr_arg (a • ·) (hB x)).trans <| smul_zero _

end IsAlt

@[simp]
theorem isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl

@[simp]
theorem isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩

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

section

variable (R M)

/-- In a non-trivial module, zero is not non-degenerate. -/
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h m fun _ => rfl)

end

variable {M' : Type*}
variable [AddCommMonoid M'] [Module R M']

theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B ≠ 0 :=
  fun h0 => not_nondegenerate_zero R M <| h0 ▸ h

theorem Nondegenerate.congr {B : BilinForm R M} (e : M ≃ₗ[R] M') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate := fun m hm =>
  e.symm.map_eq_zero_iff.1 <|
    h (e.symm m) fun n => (congr_arg _ (e.symm_apply_apply n).symm).trans (hm (e n))

@[simp]
theorem nondegenerate_congr_iff {B : BilinForm R M} (e : M ≃ₗ[R] M') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply], Nondegenerate.congr e⟩

/-- A bilinear form is nondegenerate if and only if it has a trivial kernel. -/
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R M} :
    B.Nondegenerate ↔ LinearMap.ker B = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  simp [Nondegenerate, LinearMap.ext_iff]

theorem Nondegenerate.ker_eq_bot {B : BilinForm R M} (h : B.Nondegenerate) :
    LinearMap.ker B = ⊥ := nondegenerate_iff_ker_eq_bot.mp h

theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h => by
  ext w
  refine eq_of_sub_eq_zero (b _ ?_)
  intro v
  rw [sub_left, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]

theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
  B.compLeft_injective b <| ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]

section FiniteDimensional

variable [FiniteDimensional K V]

/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.toDual` is
the linear equivalence between a vector space and its dual. -/
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm

theorem toDual_def {B : BilinForm K V} (b : B.SeparatingLeft) {m n : V} : B.toDual b m n = B m n :=
  rfl

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

end FiniteDimensional

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Finite ι]

/-- The `B`-dual basis `B.dualBasis hB b` to a finite basis `b` satisfies
`B (B.dualBasis hB b i) (b j) = B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis. -/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    Basis ι K V :=
  haveI := FiniteDimensional.of_fintype_basis b
  b.dualBasis.map (B.toDual hB).symm

@[simp]
theorem dualBasis_repr_apply
    (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  have := FiniteDimensional.of_fintype_basis b
  rw [dualBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, toDual_def]

theorem apply_dualBasis_left (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  have := FiniteDimensional.of_fintype_basis b
  rw [dualBasis, Basis.map_apply, Basis.coe_dualBasis, ← toDual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

theorem apply_dualBasis_right (B : BilinForm K V) (hB : B.Nondegenerate) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [sym.eq, apply_dualBasis_left]

@[simp]
lemma dualBasis_dualBasis_flip [FiniteDimensional K V]
    (B : BilinForm K V) (hB : B.Nondegenerate) {ι : Type*}
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

variable [FiniteDimensional K V]

/-- Given bilinear forms `B₁, B₂` where `B₂` is nondegenerate, `symmCompOfNondegenerate`
is the linear map `B₂ ∘ B₁`. -/
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) :
    V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁

theorem comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v : V) :
    B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = B₁ v := by
  rw [symmCompOfNondegenerate]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  erw [LinearEquiv.apply_symm_apply (B₂.toDual b₂)]

@[simp]
theorem symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [comp_symmCompOfNondegenerate_apply]

/-- Given the nondegenerate bilinear form `B` and the linear map `φ`,
`leftAdjointOfNondegenerate` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `BilinForm.isAdjointPairLeftAdjointOfNondegenerate`. -/
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b

theorem isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x

/-- Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left adjoint given by
`BilinForm.leftAdjointOfNondegenerate`. -/
theorem isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (ψ φ : V →ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩

end LinearAdjoints

end BilinForm

end LinearMap
