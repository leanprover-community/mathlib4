/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
module

public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Real.Pointwise

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets, and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For a module over a normed ring:
* `Seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `normSeminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm, locally convex, LCTVS
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists balancedCore

open NormedField Set Filter

open scoped NNReal Pointwise Topology Uniformity

variable {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F ι : Type*}

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
structure Seminorm (𝕜 : Type*) (E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] extends
  AddGroupSeminorm E where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  smul' : ∀ (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x

attribute [nolint docBlame] Seminorm.toAddGroupSeminorm

/-- `SeminormClass F 𝕜 E` states that `F` is a type of seminorms on the `𝕜`-module `E`.

You should extend this class when you extend `Seminorm`. -/
class SeminormClass (F : Type*) (𝕜 E : outParam Type*) [SeminormedRing 𝕜] [AddGroup E]
  [SMul 𝕜 E] [FunLike F E ℝ] : Prop extends AddGroupSeminormClass F E ℝ where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  map_smul_eq_mul (f : F) (a : 𝕜) (x : E) : f (a • x) = ‖a‖ * f x

export SeminormClass (map_smul_eq_mul)

section Of

/-- Alternative constructor for a `Seminorm` on an `AddCommGroup E` that is a module over a
`SeminormedRing 𝕜`. -/
def Seminorm.of [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ)
    (add_le : ∀ x y : E, f (x + y) ≤ f x + f y) (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x) :
    Seminorm 𝕜 E where
  toFun := f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]

/-- Alternative constructor for a `Seminorm` over a normed field `𝕜` that only assumes `f 0 = 0`
and an inequality for the scalar multiplication. -/
def Seminorm.ofSMulLE [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ) (map_zero : f 0 = 0)
    (add_le : ∀ x y, f (x + y) ≤ f x + f y) (smul_le : ∀ (r : 𝕜) (x), f (r • x) ≤ ‖r‖ * f x) :
    Seminorm 𝕜 E :=
  Seminorm.of f add_le fun r x => by
    refine le_antisymm (smul_le r x) ?_
    by_cases h : r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] at smul_le
    convert smul_le
    simp [h]

end Of

namespace Seminorm

section SeminormedRing

variable [SeminormedRing 𝕜]

section AddGroup

variable [AddGroup E]

section SMul

variable [SMul 𝕜 E]

instance instFunLike : FunLike (Seminorm 𝕜 E) E ℝ where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨_⟩⟩
    rcases g with ⟨⟨_⟩⟩
    congr

instance instSeminormClass : SeminormClass (Seminorm 𝕜 E) 𝕜 E where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_neg_eq_map f := f.neg'
  map_smul_eq_mul f := f.smul'

@[ext]
theorem ext {p q : Seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
  DFunLike.ext p q h

instance instZero : Zero (Seminorm 𝕜 E) :=
  ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with
    smul' := fun _ _ => (mul_zero _).symm }⟩

@[simp]
theorem coe_zero : ⇑(0 : Seminorm 𝕜 E) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : E) : (0 : Seminorm 𝕜 E) x = 0 :=
  rfl

instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨0⟩

variable (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance instSMul [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] : SMul R (Seminorm 𝕜 E) where
  smul r p :=
    { r • p.toAddGroupSeminorm with
      toFun := fun x => r • p x
      smul' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul]
        rw [map_smul_eq_mul, mul_left_comm] }

instance [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] [SMul R' ℝ] [SMul R' ℝ≥0]
    [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (Seminorm 𝕜 E) where
  smul_assoc r a p := ext fun x => smul_assoc r a (p x)

theorem coe_smul [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) :
    ⇑(r • p) = r • ⇑p :=
  rfl

@[simp]
theorem smul_apply [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E)
    (x : E) : (r • p) x = r • p x :=
  rfl

instance instAdd : Add (Seminorm 𝕜 E) where
  add p q :=
    { p.toAddGroupSeminorm + q.toAddGroupSeminorm with
      toFun := fun x => p x + q x
      smul' := fun a x => by simp only [map_smul_eq_mul, map_smul_eq_mul, mul_add] }

theorem coe_add (p q : Seminorm 𝕜 E) : ⇑(p + q) = p + q :=
  rfl

@[simp]
theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
  rfl

instance instAddMonoid : AddMonoid (Seminorm 𝕜 E) :=
  DFunLike.coe_injective.addMonoid _ rfl coe_add fun _ _ => by rfl

instance instAddCommMonoid : AddCommMonoid (Seminorm 𝕜 E) :=
  DFunLike.coe_injective.addCommMonoid _ rfl coe_add fun _ _ => by rfl

instance instPartialOrder : PartialOrder (Seminorm 𝕜 E) :=
  PartialOrder.lift _ DFunLike.coe_injective

instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid (Seminorm 𝕜 E) :=
  Function.Injective.isOrderedCancelAddMonoid DFunLike.coe coe_add .rfl

instance instMulAction [Monoid R] [MulAction R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] :
    MulAction R (Seminorm 𝕜 E) :=
  DFunLike.coe_injective.mulAction _ (by intros; rfl)

variable (𝕜 E)

/-- `coeFn` as an `AddMonoidHom`. Helper definition for showing that `Seminorm 𝕜 E` is a module. -/
@[simps]
def coeFnAddMonoidHom : AddMonoidHom (Seminorm 𝕜 E) (E → ℝ) where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

theorem coeFnAddMonoidHom_injective : Function.Injective (coeFnAddMonoidHom 𝕜 E) :=
  show @Function.Injective (Seminorm 𝕜 E) (E → ℝ) (↑) from DFunLike.coe_injective

variable {𝕜 E}

instance instDistribMulAction [Monoid R] [DistribMulAction R ℝ] [SMul R ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ] : DistribMulAction R (Seminorm 𝕜 E) :=
  (coeFnAddMonoidHom_injective 𝕜 E).distribMulAction _ (by intros; rfl)

instance instModule [Semiring R] [Module R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] :
    Module R (Seminorm 𝕜 E) :=
  (coeFnAddMonoidHom_injective 𝕜 E).module R _ (by intros; rfl)

instance instSup : Max (Seminorm 𝕜 E) where
  max p q :=
    { p.toAddGroupSeminorm ⊔ q.toAddGroupSeminorm with
      toFun := p ⊔ q
      smul' := fun x v =>
        (congr_arg₂ max (map_smul_eq_mul p x v) (map_smul_eq_mul q x v)).trans <|
          (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]
theorem coe_sup (p q : Seminorm 𝕜 E) : ⇑(p ⊔ q) = (p : E → ℝ) ⊔ (q : E → ℝ) :=
  rfl

theorem sup_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

theorem smul_sup [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun _ => real.smul_max _ _

@[simp, norm_cast]
theorem coe_le_coe {p q : Seminorm 𝕜 E} : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe {p q : Seminorm 𝕜 E} : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl

theorem le_def {p q : Seminorm 𝕜 E} : p ≤ q ↔ ∀ x, p x ≤ q x :=
  Iff.rfl

theorem lt_def {p q : Seminorm 𝕜 E} : p < q ↔ p ≤ q ∧ ∃ x, p x < q x :=
  @Pi.lt_def _ _ _ p q

instance instSemilatticeSup : SemilatticeSup (Seminorm 𝕜 E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

end SMul

end AddGroup

section Module

variable [SeminormedRing 𝕜₂] [SeminormedRing 𝕜₃]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₂₃]
variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomIsometric σ₁₃]
variable [AddCommGroup E] [AddCommGroup E₂] [AddCommGroup E₃]
variable [Module 𝕜 E] [Module 𝕜₂ E₂] [Module 𝕜₃ E₃]
variable [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E :=
  { p.toAddGroupSeminorm.comp f.toAddMonoidHom with
    toFun := fun x => p (f x)
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` to `map_smulₛₗ _`
    smul' _ _ := by simp only [map_smulₛₗ _, map_smul_eq_mul, RingHomIsometric.norm_map] }

theorem coe_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : ⇑(p.comp f) = p ∘ f :=
  rfl

@[simp]
theorem comp_apply (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) : (p.comp f) x = p (f x) :=
  rfl

@[simp]
theorem comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p :=
  ext fun _ => rfl

@[simp]
theorem comp_zero (p : Seminorm 𝕜₂ E₂) : p.comp (0 : E →ₛₗ[σ₁₂] E₂) = 0 :=
  ext fun _ => map_zero p

@[simp]
theorem zero_comp (f : E →ₛₗ[σ₁₂] E₂) : (0 : Seminorm 𝕜₂ E₂).comp f = 0 :=
  ext fun _ => rfl

theorem comp_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (p : Seminorm 𝕜₃ E₃) (g : E₂ →ₛₗ[σ₂₃] E₃)
    (f : E →ₛₗ[σ₁₂] E₂) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

theorem add_comp (p q : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) :
    (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

theorem comp_add_le (p : Seminorm 𝕜₂ E₂) (f g : E →ₛₗ[σ₁₂] E₂) :
    p.comp (f + g) ≤ p.comp f + p.comp g := fun _ => map_add_le_add p _ _

theorem smul_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : R) :
    (c • p).comp f = c • p.comp f :=
  ext fun _ => rfl

theorem comp_mono {p q : Seminorm 𝕜₂ E₂} (f : E →ₛₗ[σ₁₂] E₂) (hp : p ≤ q) : p.comp f ≤ q.comp f :=
  fun _ => hp _

/-- The composition as an `AddMonoidHom`. -/
@[simps]
def pullback (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜₂ E₂ →+ Seminorm 𝕜 E where
  toFun := fun p => p.comp f
  map_zero' := zero_comp f
  map_add' := fun p q => add_comp p q f

instance instOrderBot : OrderBot (Seminorm 𝕜 E) where
  bot := 0
  bot_le := apply_nonneg

@[simp]
theorem coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem smul_le_smul {p q : Seminorm 𝕜 E} {a b : ℝ≥0} (hpq : p ≤ q) (hab : a ≤ b) :
    a • p ≤ b • q := by
  simp_rw [le_def]
  intro x
  exact mul_le_mul hab (hpq x) (apply_nonneg p x) (NNReal.coe_nonneg b)

theorem finset_sup_apply (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonneg (p i) x)) := by
  induction s using Finset.cons_induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.sup_empty, coe_bot, _root_.bot_eq_zero, Pi.zero_apply]
    norm_cast
  | cons a s ha ih =>
    rw [Finset.sup_cons, Finset.sup_cons, coe_sup, Pi.sup_apply, NNReal.coe_max, NNReal.coe_mk, ih]

theorem exists_apply_eq_finset_sup (p : ι → Seminorm 𝕜 E) {s : Finset ι} (hs : s.Nonempty) (x : E) :
    ∃ i ∈ s, s.sup p x = p i x := by
  rcases Finset.exists_mem_eq_sup s hs (fun i ↦ (⟨p i x, apply_nonneg _ _⟩ : ℝ≥0)) with ⟨i, hi, hix⟩
  rw [finset_sup_apply]
  exact ⟨i, hi, congr_arg _ hix⟩

theorem zero_or_exists_apply_eq_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = 0 ∨ ∃ i ∈ s, s.sup p x = p i x := by
  rcases Finset.eq_empty_or_nonempty s with (rfl | hs)
  · left; rfl
  · right; exact exists_apply_eq_finset_sup p hs x

theorem finset_sup_smul (p : ι → Seminorm 𝕜 E) (s : Finset ι) (C : ℝ≥0) :
    s.sup (C • p) = C • s.sup p := by
  ext x
  rw [smul_apply, finset_sup_apply, finset_sup_apply]
  symm
  exact congr_arg ((↑) : ℝ≥0 → ℝ) (NNReal.mul_finset_sup C s (fun i ↦ ⟨p i x, apply_nonneg _ _⟩))

theorem finset_sup_le_sum (p : ι → Seminorm 𝕜 E) (s : Finset ι) : s.sup p ≤ ∑ i ∈ s, p i := by
  classical
  refine Finset.sup_le_iff.mpr ?_
  intro i hi
  rw [Finset.sum_eq_sum_diff_singleton_add hi, le_add_iff_nonneg_left]
  exact bot_le

theorem finset_sup_apply_le {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, i ∈ s → p i x ≤ a) : s.sup p x ≤ a := by
  lift a to ℝ≥0 using ha
  rw [finset_sup_apply, NNReal.coe_le_coe]
  exact Finset.sup_le h

theorem le_finset_sup_apply {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {i : ι}
    (hi : i ∈ s) : p i x ≤ s.sup p x :=
  (Finset.le_sup hi : p i ≤ s.sup p) x

theorem finset_sup_apply_lt {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 < a)
    (h : ∀ i, i ∈ s → p i x < a) : s.sup p x < a := by
  lift a to ℝ≥0 using ha.le
  rw [finset_sup_apply, NNReal.coe_lt_coe, Finset.sup_lt_iff]
  · exact h
  · exact NNReal.coe_pos.mpr ha

theorem norm_sub_map_le_sub (p : Seminorm 𝕜 E) (x y : E) : ‖p x - p y‖ ≤ p (x - y) :=
  abs_sub_map_le_sub p x y

end Module

end SeminormedRing

section SeminormedCommRing

variable [SeminormedRing 𝕜] [SeminormedCommRing 𝕜₂]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable [AddCommGroup E] [AddCommGroup E₂] [Module 𝕜 E] [Module 𝕜₂ E₂]

theorem comp_smul (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : 𝕜₂) :
    p.comp (c • f) = ‖c‖₊ • p.comp f :=
  ext fun _ => by
    rw [comp_apply, smul_apply, LinearMap.smul_apply, map_smul_eq_mul, NNReal.smul_def, coe_nnnorm,
      smul_eq_mul, comp_apply]

theorem comp_smul_apply (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E) :
    p.comp (c • f) x = ‖c‖ * p (f x) :=
  map_smul_eq_mul p _ _

end SeminormedCommRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {p q : Seminorm 𝕜 E} {x : E}

/-- Auxiliary lemma to show that the infimum of seminorms is well-defined. -/
theorem bddBelow_range_add : BddBelow (range fun u => p u + q (x - u)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp; positivity⟩

noncomputable instance instInf : Min (Seminorm 𝕜 E) where
  min p q :=
    { p.toAddGroupSeminorm ⊓ q.toAddGroupSeminorm with
      toFun := fun x => ⨅ u : E, p u + q (x - u)
      smul' := by
        intro a x
        obtain rfl | ha := eq_or_ne a 0
        · rw [norm_zero, zero_mul, zero_smul]
          refine
            ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
              (fun i => by positivity)
              fun x hx => ⟨0, by rwa [map_zero, sub_zero, map_zero, add_zero]⟩
        simp_rw [Real.mul_iInf_of_nonneg (norm_nonneg a), mul_add, ← map_smul_eq_mul p, ←
          map_smul_eq_mul q, smul_sub]
        refine
          Function.Surjective.iInf_congr ((a⁻¹ • ·) : E → E)
            (fun u => ⟨a • u, inv_smul_smul₀ ha u⟩) fun u => ?_
        rw [smul_inv_smul₀ ha] }

@[simp]
theorem inf_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊓ q) x = ⨅ u : E, p u + q (x - u) :=
  rfl

noncomputable instance instLattice : Lattice (Seminorm 𝕜 E) :=
  { Seminorm.instSemilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
      ciInf_le_of_le bddBelow_range_add x <| by
        simp only [sub_self, map_zero, add_zero]; rfl
    inf_le_right := fun p q x =>
      ciInf_le_of_le bddBelow_range_add 0 <| by
        simp only [map_zero, zero_add, sub_zero]; rfl
    le_inf := fun a _ _ hab hac _ =>
      le_ciInf fun _ => (le_map_add_map_sub a _ _).trans <| add_le_add (hab _) (hac _) }

theorem smul_inf [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊓ q) = r • p ⊓ r • q := by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def,
    smul_eq_mul, Real.mul_iInf_of_nonneg (NNReal.coe_nonneg _), mul_add]

section Classical

open Classical in
/-- We define the supremum of an arbitrary subset of `Seminorm 𝕜 E` as follows:
* if `s` is `BddAbove` *as a set of functions `E → ℝ`* (that is, if `s` is pointwise bounded
  above), we take the pointwise supremum of all elements of `s`, and we prove that it is indeed a
  seminorm.
* otherwise, we take the zero seminorm `⊥`.

There are two things worth mentioning here:
* First, it is not trivial at first that `s` being bounded above *by a function* implies
  being bounded above *as a seminorm*. We show this in `Seminorm.bddAbove_iff` by using
  that the `Sup s` as defined here is then a bounding seminorm for `s`. So it is important to make
  the case disjunction on `BddAbove ((↑) '' s : Set (E → ℝ))` and not `BddAbove s`.
* Since the pointwise `Sup` already gives `0` at points where a family of functions is
  not bounded above, one could hope that just using the pointwise `Sup` would work here, without the
  need for an additional case disjunction. As discussed on Zulip, this doesn't work because this can
  give a function which does *not* satisfy the seminorm axioms (typically sub-additivity).
-/
noncomputable instance instSupSet : SupSet (Seminorm 𝕜 E) where
  sSup s :=
    if h : BddAbove ((↑) '' s : Set (E → ℝ)) then
      { toFun := ⨆ p : s, ((p : Seminorm 𝕜 E) : E → ℝ)
        map_zero' := by
          rw [iSup_apply, ← @Real.iSup_const_zero s]
          congr!
          rename_i _ _ _ i
          exact map_zero i.1
        add_le' := fun x y => by
          rcases h with ⟨q, hq⟩
          obtain rfl | h := s.eq_empty_or_nonempty
          · simp [Real.iSup_of_isEmpty]
          haveI : Nonempty ↑s := h.coe_sort
          simp only [iSup_apply]
          refine ciSup_le fun i =>
            ((i : Seminorm 𝕜 E).add_le' x y).trans <| add_le_add
              -- Porting note: `f` is provided to force `Subtype.val` to appear.
              -- A type ascription on `_` would have also worked, but would have been more verbose.
              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun x) ⟨q x, ?_⟩ i)
              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun y) ⟨q y, ?_⟩ i)
          <;> rw [mem_upperBounds, forall_mem_range]
          <;> exact fun j => hq (mem_image_of_mem _ j.2) _
        neg' := fun x => by
          simp only [iSup_apply]
          congr! 2
          rename_i _ _ _ i
          exact i.1.neg' _
        smul' := fun a x => by
          simp only [iSup_apply]
          rw [← smul_eq_mul,
            Real.smul_iSup_of_nonneg (norm_nonneg a) fun i : s => (i : Seminorm 𝕜 E) x]
          congr!
          rename_i _ _ _ i
          exact i.1.smul' a x }
    else ⊥

protected theorem coe_sSup_eq' {s : Set <| Seminorm 𝕜 E}
    (hs : BddAbove ((↑) '' s : Set (E → ℝ))) : ↑(sSup s) = ⨆ p : s, ((p : Seminorm 𝕜 E) : E → ℝ) :=
  congr_arg _ (dif_pos hs)

protected theorem bddAbove_iff {s : Set <| Seminorm 𝕜 E} :
    BddAbove s ↔ BddAbove ((↑) '' s : Set (E → ℝ)) :=
  ⟨fun ⟨q, hq⟩ => ⟨q, forall_mem_image.2 fun _ hp => hq hp⟩, fun H =>
    ⟨sSup s, fun p hp x => by
      dsimp
      rw [Seminorm.coe_sSup_eq' H, iSup_apply]
      rcases H with ⟨q, hq⟩
      exact
        le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩⟩⟩

protected theorem bddAbove_range_iff {ι : Sort*} {p : ι → Seminorm 𝕜 E} :
    BddAbove (range p) ↔ ∀ x, BddAbove (range fun i ↦ p i x) := by
  rw [Seminorm.bddAbove_iff, ← range_comp, bddAbove_range_pi]; rfl

protected theorem coe_sSup_eq {s : Set <| Seminorm 𝕜 E} (hs : BddAbove s) :
    ↑(sSup s) = ⨆ p : s, ((p : Seminorm 𝕜 E) : E → ℝ) :=
  Seminorm.coe_sSup_eq' (Seminorm.bddAbove_iff.mp hs)

protected theorem coe_iSup_eq {ι : Sort*} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) :
    ↑(⨆ i, p i) = ⨆ i, ((p i : Seminorm 𝕜 E) : E → ℝ) := by
  rw [← sSup_range, Seminorm.coe_sSup_eq hp]
  exact iSup_range' (fun p : Seminorm 𝕜 E => (p : E → ℝ)) p

protected theorem sSup_apply {s : Set (Seminorm 𝕜 E)} (hp : BddAbove s) {x : E} :
    (sSup s) x = ⨆ p : s, (p : E → ℝ) x := by
  rw [Seminorm.coe_sSup_eq hp, iSup_apply]

protected theorem iSup_apply {ι : Sort*} {p : ι → Seminorm 𝕜 E}
    (hp : BddAbove (range p)) {x : E} : (⨆ i, p i) x = ⨆ i, p i x := by
  rw [Seminorm.coe_iSup_eq hp, iSup_apply]

protected theorem sSup_empty : sSup (∅ : Set (Seminorm 𝕜 E)) = ⊥ := by
  ext
  rw [Seminorm.sSup_apply bddAbove_empty, Real.iSup_of_isEmpty]
  rfl

set_option backward.privateInPublic true in
private theorem isLUB_sSup (s : Set (Seminorm 𝕜 E)) (hs₁ : BddAbove s) (hs₂ : s.Nonempty) :
    IsLUB s (sSup s) := by
  refine ⟨fun p hp x => ?_, fun p hp x => ?_⟩ <;> haveI : Nonempty ↑s := hs₂.coe_sort <;>
    dsimp <;> rw [Seminorm.coe_sSup_eq hs₁, iSup_apply]
  · rcases hs₁ with ⟨q, hq⟩
    exact le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq i.2 x⟩ ⟨p, hp⟩
  · exact ciSup_le fun q => hp q.2 x

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `Seminorm 𝕜 E` is a conditionally complete lattice.

Note that, while `inf`, `sup` and `sSup` have good definitional properties (corresponding to
the instances given here for `Inf`, `Sup` and `SupSet` respectively), `sInf s` is just
defined as the supremum of the lower bounds of `s`, which is not really useful in practice. If you
need to use `sInf` on seminorms, then you should probably provide a more workable definition first,
but this is unlikely to happen so we keep the "bad" definition for now. -/
noncomputable instance instConditionallyCompleteLattice :
    ConditionallyCompleteLattice (Seminorm 𝕜 E) :=
  conditionallyCompleteLatticeOfLatticeOfsSup (Seminorm 𝕜 E) Seminorm.isLUB_sSup

end Classical

end NormedField

/-! ### Seminorm ball -/


section SeminormedRing

variable [SeminormedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E]

section SMul

variable [SMul 𝕜 E] (p : Seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < r`. -/
def ball (x : E) (r : ℝ) :=
  { y : E | p (y - x) < r }

/-- The closed ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y`
with `p (y - x) ≤ r`. -/
def closedBall (x : E) (r : ℝ) :=
  { y : E | p (y - x) ≤ r }

variable {x y : E} {r : ℝ}

@[simp]
theorem mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
  Iff.rfl

@[simp]
theorem mem_closedBall : y ∈ closedBall p x r ↔ p (y - x) ≤ r :=
  Iff.rfl

theorem mem_ball_self (hr : 0 < r) : x ∈ ball p x r := by simp [hr]

theorem mem_closedBall_self (hr : 0 ≤ r) : x ∈ closedBall p x r := by simp [hr]

theorem mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]

theorem mem_closedBall_zero : y ∈ closedBall p 0 r ↔ p y ≤ r := by rw [mem_closedBall, sub_zero]

theorem ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
  Set.ext fun _ => p.mem_ball_zero

theorem closedBall_zero_eq : closedBall p 0 r = { y : E | p y ≤ r } :=
  Set.ext fun _ => p.mem_closedBall_zero

theorem ball_subset_closedBall (x r) : ball p x r ⊆ closedBall p x r := fun _ h =>
  (mem_closedBall _).mpr ((mem_ball _).mp h).le

theorem closedBall_eq_biInter_ball (x r) : closedBall p x r = ⋂ ρ > r, ball p x ρ := by
  ext y; simp_rw [mem_closedBall, mem_iInter₂, mem_ball, ← forall_gt_iff_le]

@[simp]
theorem ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminorm 𝕜 E) x r = Set.univ := by
  rw [Set.eq_univ_iff_forall, ball]
  simp [hr]

@[simp]
theorem closedBall_zero' (x : E) (hr : 0 < r) : closedBall (0 : Seminorm 𝕜 E) x r = Set.univ :=
  eq_univ_of_subset (ball_subset_closedBall _ _ _) (ball_zero' x hr)

theorem ball_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : ℝ) (x : E) :
    (c • p).ball x r = p.ball x (r / c) := by
  ext
  rw [mem_ball, mem_ball, smul_apply, NNReal.smul_def, smul_eq_mul, mul_comm,
    lt_div_iff₀ (NNReal.coe_pos.mpr hc)]

theorem closedBall_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : ℝ) (x : E) :
    (c • p).closedBall x r = p.closedBall x (r / c) := by
  ext
  rw [mem_closedBall, mem_closedBall, smul_apply, NNReal.smul_def, smul_eq_mul, mul_comm,
    le_div_iff₀ (NNReal.coe_pos.mpr hc)]

theorem ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) :
    ball (p ⊔ q) e r = ball p e r ∩ ball q e r := by
  simp_rw [ball, ← Set.setOf_and, coe_sup, Pi.sup_apply, sup_lt_iff]

theorem closedBall_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) :
    closedBall (p ⊔ q) e r = closedBall p e r ∩ closedBall q e r := by
  simp_rw [closedBall, ← Set.setOf_and, coe_sup, Pi.sup_apply, sup_le_iff]

theorem ball_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E) (r : ℝ) :
    ball (s.sup' H p) e r = s.inf' H fun i => ball (p i) e r := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]

theorem closedBall_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E)
    (r : ℝ) : closedBall (s.sup' H p) e r = s.inf' H fun i => closedBall (p i) e r := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, closedBall_sup, inf_eq_inter, ih]

@[gcongr]
theorem ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ :=
  fun _ (hx : _ < _) => hx.trans_le h

@[gcongr]
theorem closedBall_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    p.closedBall x r₁ ⊆ p.closedBall x r₂ := fun _ (hx : _ ≤ _) => hx.trans h

theorem ball_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r := fun _ =>
  (h _).trans_lt

theorem closedBall_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) :
    p.closedBall x r ⊆ q.closedBall x r := fun _ => (h _).trans

theorem ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_ball, add_sub_add_comm]
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂)

theorem closedBall_add_closedBall_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.closedBall (x₁ : E) r₁ + p.closedBall (x₂ : E) r₂ ⊆ p.closedBall (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_closedBall, add_sub_add_comm]
  exact (map_add_le_add p _ _).trans (add_le_add hy₁ hy₂)

theorem sub_mem_ball (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : ℝ) :
    x₁ - x₂ ∈ p.ball y r ↔ x₁ ∈ p.ball (x₂ + y) r := by simp_rw [mem_ball, sub_sub]

theorem sub_mem_closedBall (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : ℝ) :
    x₁ - x₂ ∈ p.closedBall y r ↔ x₁ ∈ p.closedBall (x₂ + y) r := by
  simp_rw [mem_closedBall, sub_sub]

lemma ball_eq_metric :
    letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.ball x r = Metric.ball x r := by
  ext
  simp only [mem_ball_iff_norm]
  rfl

lemma closedBall_eq_metric :
    letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.closedBall x r = Metric.closedBall x r := by
  ext
  simp only [mem_closedBall_iff_norm]
  rfl

/-- The image of a ball under addition with a singleton is another ball. -/
theorem vadd_ball (p : Seminorm 𝕜 E) : x +ᵥ p.ball y r = p.ball (x +ᵥ y) r := by
  letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [ball_eq_metric]

/-- The image of a closed ball under addition with a singleton is another closed ball. -/
theorem vadd_closedBall (p : Seminorm 𝕜 E) : x +ᵥ p.closedBall y r = p.closedBall (x +ᵥ y) r := by
  letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [closedBall_eq_metric]

end SMul

section Module

variable [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup E₂] [Module 𝕜₂ E₂]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

theorem ball_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
    (p.comp f).ball x r = f ⁻¹' p.ball (f x) r := by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_setOf_eq, map_sub]

theorem closedBall_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
    (p.comp f).closedBall x r = f ⁻¹' p.closedBall (f x) r := by
  ext
  simp_rw [closedBall, mem_preimage, comp_apply, Set.mem_setOf_eq, map_sub]

variable (p : Seminorm 𝕜 E)

theorem preimage_metric_ball {r : ℝ} : p ⁻¹' Metric.ball 0 r = { x | p x < r } := by
  ext x
  simp only [mem_setOf, mem_preimage, mem_ball_zero_iff, Real.norm_of_nonneg (apply_nonneg p _)]

theorem preimage_metric_closedBall {r : ℝ} : p ⁻¹' Metric.closedBall 0 r = { x | p x ≤ r } := by
  ext x
  simp only [mem_setOf, mem_preimage, mem_closedBall_zero_iff,
    Real.norm_of_nonneg (apply_nonneg p _)]

theorem ball_zero_eq_preimage_ball {r : ℝ} : p.ball 0 r = p ⁻¹' Metric.ball 0 r := by
  rw [ball_zero_eq, preimage_metric_ball]

theorem closedBall_zero_eq_preimage_closedBall {r : ℝ} :
    p.closedBall 0 r = p ⁻¹' Metric.closedBall 0 r := by
  rw [closedBall_zero_eq, preimage_metric_closedBall]

@[simp]
theorem ball_bot {r : ℝ} (x : E) (hr : 0 < r) : ball (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  ball_zero' x hr

@[simp]
theorem closedBall_bot {r : ℝ} (x : E) (hr : 0 < r) :
    closedBall (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  closedBall_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero (r : ℝ) : Balanced 𝕜 (ball p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero, ← hx, map_smul_eq_mul]
  calc
    _ ≤ p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ < r := by rwa [mem_ball_zero] at hy

/-- Closed seminorm-balls at the origin are balanced. -/
theorem balanced_closedBall_zero (r : ℝ) : Balanced 𝕜 (closedBall p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_closedBall_zero, ← hx, map_smul_eq_mul]
  calc
    _ ≤ p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ ≤ r := by rwa [mem_closedBall_zero] at hy

theorem ball_finset_sup_eq_iInter (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ}
    (hr : 0 < r) : ball (s.sup p) x r = ⋂ i ∈ s, ball (p i) x r := by
  lift r to NNReal using hr.le
  simp_rw [ball, iInter_setOf, finset_sup_apply, NNReal.coe_lt_coe,
    Finset.sup_lt_iff (show ⊥ < r from hr), ← NNReal.coe_lt_coe, NNReal.coe_mk]

theorem closedBall_finset_sup_eq_iInter (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ}
    (hr : 0 ≤ r) : closedBall (s.sup p) x r = ⋂ i ∈ s, closedBall (p i) x r := by
  lift r to NNReal using hr
  simp_rw [closedBall, iInter_setOf, finset_sup_apply, NNReal.coe_le_coe, Finset.sup_le_iff, ←
    NNReal.coe_le_coe, NNReal.coe_mk]

theorem ball_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
    ball (s.sup p) x r = s.inf fun i => ball (p i) x r := by
  rw [Finset.inf_eq_iInf]
  exact ball_finset_sup_eq_iInter _ _ _ hr

theorem closedBall_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    closedBall (s.sup p) x r = s.inf fun i => closedBall (p i) x r := by
  rw [Finset.inf_eq_iInf]
  exact closedBall_finset_sup_eq_iInter _ _ _ hr

@[simp]
theorem ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ := by
  ext
  rw [Seminorm.mem_ball, Set.mem_empty_iff_false, iff_false, not_lt]
  exact hr.trans (apply_nonneg p _)

@[simp]
theorem closedBall_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r < 0) :
    p.closedBall x r = ∅ := by
  ext
  rw [Seminorm.mem_closedBall, Set.mem_empty_iff_false, iff_false, not_le]
  exact hr.trans_le (apply_nonneg _ _)

theorem closedBall_smul_ball (p : Seminorm 𝕜 E) {r₁ : ℝ} (hr₁ : r₁ ≠ 0) (r₂ : ℝ) :
    Metric.closedBall (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  refine fun a ha b hb ↦ mul_lt_mul' ha hb (apply_nonneg _ _) ?_
  exact hr₁.lt_or_gt.resolve_left <| ((norm_nonneg a).trans ha).not_gt

theorem ball_smul_closedBall (p : Seminorm 𝕜 E) (r₁ : ℝ) {r₂ : ℝ} (hr₂ : r₂ ≠ 0) :
    Metric.ball (0 : 𝕜) r₁ • p.closedBall 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero, mem_ball_zero_iff,
    map_smul_eq_mul]
  intro a ha b hb
  rw [mul_comm, mul_comm r₁]
  refine mul_lt_mul' hb ha (norm_nonneg _) (hr₂.lt_or_gt.resolve_left ?_)
  exact ((apply_nonneg p b).trans hb).not_gt

theorem ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) :
    Metric.ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  rcases eq_or_ne r₂ 0 with rfl | hr₂
  · simp
  · exact (smul_subset_smul_left (ball_subset_closedBall _ _ _)).trans
      (ball_smul_closedBall _ _ hr₂)

theorem closedBall_smul_closedBall (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) :
    Metric.closedBall (0 : 𝕜) r₁ • p.closedBall 0 r₂ ⊆ p.closedBall 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_closedBall_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  intro a ha b hb
  gcongr
  exact (norm_nonneg _).trans ha

theorem neg_mem_ball_zero {r : ℝ} {x : E} : -x ∈ ball p 0 r ↔ x ∈ ball p 0 r := by
  simp only [mem_ball_zero, map_neg_eq_map]

theorem neg_mem_closedBall_zero {r : ℝ} {x : E} : -x ∈ closedBall p 0 r ↔ x ∈ closedBall p 0 r := by
  simp only [mem_closedBall_zero, map_neg_eq_map]

@[simp]
theorem neg_ball (p : Seminorm 𝕜 E) (r : ℝ) (x : E) : -ball p x r = ball p (-x) r := by
  ext
  rw [Set.mem_neg, mem_ball, mem_ball, ← neg_add', sub_neg_eq_add, map_neg_eq_map]

@[simp]
theorem neg_closedBall (p : Seminorm 𝕜 E) (r : ℝ) (x : E) :
    -closedBall p x r = closedBall p (-x) r := by
  ext
  rw [Set.mem_neg, mem_closedBall, mem_closedBall, ← neg_add', sub_neg_eq_add, map_neg_eq_map]

end Module

end AddCommGroup

end SeminormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {r : ℝ} {x : E}

theorem closedBall_iSup {ι : Sort*} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) (e : E)
    {r : ℝ} (hr : 0 < r) : closedBall (⨆ i, p i) e r = ⋂ i, closedBall (p i) e r := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iInter_of_empty, Seminorm.sSup_empty]
    exact closedBall_bot _ hr
  · ext x
    have := Seminorm.bddAbove_range_iff.mp hp (x - e)
    simp only [mem_closedBall, mem_iInter, Seminorm.iSup_apply hp, ciSup_le_iff this]

theorem ball_norm_mul_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
    p.ball 0 (‖k‖ * r) ⊆ k • p.ball 0 r := by
  rcases eq_or_ne k 0 with (rfl | hk)
  · rw [norm_zero, zero_mul, ball_eq_emptyset _ le_rfl]
    exact empty_subset _
  · intro x
    rw [Set.mem_smul_set, Seminorm.mem_ball_zero]
    refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
    · rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ←
        mul_lt_mul_iff_right₀ <| norm_pos_iff.mpr hk, ← mul_assoc, ← div_eq_mul_inv ‖k‖ ‖k‖,
        div_self (ne_of_gt <| norm_pos_iff.mpr hk), one_mul]
    rw [← smul_assoc, smul_eq_mul, ← div_eq_mul_inv, div_self hk, one_smul]

theorem smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : k ≠ 0) :
    k • p.ball 0 r = p.ball 0 (‖k‖ * r) := by
  ext
  rw [mem_smul_set_iff_inv_smul_mem₀ hk, p.mem_ball_zero, p.mem_ball_zero, map_smul_eq_mul,
    norm_inv, ← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.2 hk), mul_comm]

theorem smul_closedBall_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
    k • p.closedBall 0 r ⊆ p.closedBall 0 (‖k‖ * r) := by
  rintro x ⟨y, hy, h⟩
  rw [Seminorm.mem_closedBall_zero, ← h, map_smul_eq_mul]
  rw [Seminorm.mem_closedBall_zero] at hy
  gcongr

theorem smul_closedBall_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : 0 < ‖k‖) :
    k • p.closedBall 0 r = p.closedBall 0 (‖k‖ * r) := by
  refine subset_antisymm smul_closedBall_subset ?_
  intro x
  rw [Set.mem_smul_set, Seminorm.mem_closedBall_zero]
  refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
  · rwa [Seminorm.mem_closedBall_zero, map_smul_eq_mul, norm_inv, inv_mul_le_iff₀ hk]
  rw [← smul_assoc, smul_eq_mul, ← div_eq_mul_inv, div_self (norm_pos_iff.mp hk), one_smul]

theorem ball_zero_absorbs_ball_zero (p : Seminorm 𝕜 E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) := by
  rcases exists_pos_lt_mul hr₁ r₂ with ⟨r, hr₀, hr⟩
  refine .of_norm ⟨r, fun a ha x hx => ?_⟩
  rw [smul_ball_zero (norm_pos_iff.1 <| hr₀.trans_le ha), p.mem_ball_zero]
  rw [p.mem_ball_zero] at hx
  exact hx.trans (hr.trans_le <| by gcongr)

/-- Seminorm-balls at the origin are absorbent. -/
protected theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (ball p (0 : E) r) :=
  absorbent_iff_forall_absorbs_singleton.2 fun _ =>
    (p.ball_zero_absorbs_ball_zero hr).mono_right <|
      singleton_subset_iff.2 <| p.mem_ball_zero.2 <| lt_add_one _

/-- Closed seminorm-balls at the origin are absorbent. -/
protected theorem absorbent_closedBall_zero (hr : 0 < r) : Absorbent 𝕜 (closedBall p (0 : E) r) :=
  (p.absorbent_ball_zero hr).mono (p.ball_subset_closedBall _ _)

/-- Seminorm-balls containing the origin are absorbent. -/
protected theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (ball p x r) := by
  refine (p.absorbent_ball_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt <| add_lt_of_lt_sub_right hy)

/-- Seminorm-balls containing the origin are absorbent. -/
protected theorem absorbent_closedBall (hpr : p x < r) : Absorbent 𝕜 (closedBall p x r) := by
  refine (p.absorbent_closedBall_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_closedBall_zero] at hy
  exact p.mem_closedBall.2 ((map_sub_le_add p _ _).trans <| add_le_of_le_sub_right hy)

@[simp]
theorem smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (a • ·) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ‖a‖) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_ball, mem_ball, lt_div_iff₀ (norm_pos_iff.mpr ha), mul_comm, ←
      map_smul_eq_mul p, smul_sub, smul_inv_smul₀ ha]

@[simp]
theorem smul_closedBall_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (a • ·) ⁻¹' p.closedBall y r = p.closedBall (a⁻¹ • y) (r / ‖a‖) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_closedBall, mem_closedBall, le_div_iff₀ (norm_pos_iff.mpr ha), mul_comm, ←
      map_smul_eq_mul p, smul_sub, smul_inv_smul₀ ha]

end NormedField

section Convex

variable [NormedField 𝕜] [AddCommGroup E] [NormedSpace ℝ 𝕜] [Module 𝕜 E]

section SMul

variable [SMul ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convexOn_norm`. -/
protected theorem convexOn : ConvexOn ℝ univ p := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc
    p (a • x + b • y) ≤ p (a • x) + p (b • y) := map_add_le_add p _ _
    _ = ‖a • (1 : 𝕜)‖ * p x + ‖b • (1 : 𝕜)‖ * p y := by
      rw [← map_smul_eq_mul p, ← map_smul_eq_mul p, smul_one_smul, smul_one_smul]
    _ = a * p x + b * p y := by
      rw [norm_smul, norm_smul, norm_one, mul_one, mul_one, Real.norm_of_nonneg ha,
        Real.norm_of_nonneg hb]

end SMul

section Module

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
theorem convex_ball : Convex ℝ (ball p x r) := by
  convert (p.convexOn.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg]
  rfl

/-- Closed seminorm-balls are convex. -/
theorem convex_closedBall : Convex ℝ (closedBall p x r) := by
  rw [closedBall_eq_biInter_ball]
  exact convex_iInter₂ fun _ _ => convex_ball _ _ _

end Module

end Convex

section RestrictScalars

variable (𝕜) {𝕜' : Type*} [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormOneClass 𝕜'] [AddCommGroup E] [Module 𝕜' E] [SMul 𝕜 E] [IsScalarTower 𝕜 𝕜' E]

/-- Reinterpret a seminorm over a field `𝕜'` as a seminorm over a smaller field `𝕜`. This will
typically be used with `RCLike 𝕜'` and `𝕜 = ℝ`. -/
protected def restrictScalars (p : Seminorm 𝕜' E) : Seminorm 𝕜 E :=
  { p with
    smul' := fun a x => by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one] }

@[simp]
theorem coe_restrictScalars (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜 : E → ℝ) = p :=
  rfl

@[simp]
theorem restrictScalars_ball (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜).ball = p.ball :=
  rfl

@[simp]
theorem restrictScalars_closedBall (p : Seminorm 𝕜' E) :
    (p.restrictScalars 𝕜).closedBall = p.closedBall :=
  rfl

end RestrictScalars

/-! ### Continuity criteria for seminorms -/


section Continuity

variable [NontriviallyNormedField 𝕜] [SeminormedRing 𝕝] [AddCommGroup E] [Module 𝕜 E]
variable [Module 𝕝 E]

/-- A seminorm is continuous at `0` if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuousAt_zero'`. -/
theorem continuousAt_zero_of_forall' [TopologicalSpace E] {p : Seminorm 𝕝 E}
    (hp : ∀ r > 0, p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    ContinuousAt p 0 := by
  simp_rw [Seminorm.closedBall_zero_eq_preimage_closedBall] at hp
  rwa [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff, map_zero]

theorem continuousAt_zero' [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E}
    {r : ℝ} (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) : ContinuousAt p 0 := by
  refine continuousAt_zero_of_forall' fun ε hε ↦ ?_
  obtain ⟨k, hk₀, hk⟩ : ∃ k : 𝕜, 0 < ‖k‖ ∧ ‖k‖ * r < ε := by
    rcases le_or_gt r 0 with hr | hr
    · use 1; simpa using hr.trans_lt hε
    · simpa [lt_div_iff₀ hr] using exists_norm_lt 𝕜 (div_pos hε hr)
  grw [← hk]
  rwa [← set_smul_mem_nhds_zero_iff (norm_pos_iff.1 hk₀), smul_closedBall_zero hk₀] at hp

/-- A seminorm is continuous at `0` if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuousAt_zero'`. -/
theorem continuousAt_zero_of_forall [TopologicalSpace E] {p : Seminorm 𝕝 E}
    (hp : ∀ r > 0, p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    ContinuousAt p 0 :=
  continuousAt_zero_of_forall'
    (fun r hr ↦ Filter.mem_of_superset (hp r hr) <| p.ball_subset_closedBall _ _)

theorem continuousAt_zero [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) : ContinuousAt p 0 :=
  continuousAt_zero' (Filter.mem_of_superset hp <| p.ball_subset_closedBall _ _)

protected theorem uniformContinuous_of_continuousAt_zero [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : UniformContinuous p := by
  have hp : Filter.Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero_swapped,
    Metric.uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp.comp Filter.tendsto_comap)
      (fun xy => dist_nonneg) fun xy => p.norm_sub_map_le_sub _ _

protected theorem continuous_of_continuousAt_zero [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : Continuous p := by
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact (Seminorm.uniformContinuous_of_continuousAt_zero hp).continuous

/-- A seminorm is uniformly continuous if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.uniformContinuous`. -/
protected theorem uniformContinuous_of_forall [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)

protected theorem uniformContinuous [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ} (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero hp)

/-- A seminorm is uniformly continuous if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.uniformContinuous'`. -/
protected theorem uniformContinuous_of_forall' [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)

protected theorem uniformContinuous' [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) : UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero' hp)

/-- A seminorm is continuous if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuous`. -/
protected theorem continuous_of_forall [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)

protected theorem continuous [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ} (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero hp)

protected theorem continuous_iff [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ} (hr : 0 < r) :
    Continuous p ↔ p.ball 0 r ∈ 𝓝 0 :=
  ⟨fun H ↦ p.ball_zero_eq ▸ (H.tendsto' 0 0 (map_zero p)).eventually_lt_const hr, p.continuous⟩

/-- A seminorm is continuous if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuous'`. -/
protected theorem continuous_of_forall' [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)

protected theorem continuous' [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) : Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero' hp)

theorem continuous_of_le [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p q : Seminorm 𝕝 E} (hq : Continuous q) (hpq : p ≤ q) : Continuous p := by
  refine Seminorm.continuous_of_forall (fun r hr ↦ Filter.mem_of_superset
    (IsOpen.mem_nhds ?_ <| q.mem_ball_self hr) (ball_antitone hpq))
  rw [ball_zero_eq]
  exact isOpen_lt hq continuous_const

lemma ball_mem_nhds [TopologicalSpace E] {p : Seminorm 𝕝 E} (hp : Continuous p) {r : ℝ}
    (hr : 0 < r) : p.ball 0 r ∈ (𝓝 0 : Filter E) := by
  have this : Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp.tendsto 0
  simpa only [p.ball_zero_eq] using this (Iio_mem_nhds hr)

lemma uniformSpace_eq_of_hasBasis
    {ι} [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p' : ι → Prop} {s : ι → Set E} (p : Seminorm 𝕜 E) (hb : (𝓝 0 : Filter E).HasBasis p' s)
    (h₁ : ∃ r, p.closedBall 0 r ∈ 𝓝 0) (h₂ : ∀ i, p' i → ∃ r > 0, p.ball 0 r ⊆ s i) :
    ‹UniformSpace E› = p.toAddGroupSeminorm.toSeminormedAddGroup.toUniformSpace := by
  refine IsUniformAddGroup.ext ‹_›
    p.toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup ?_
  apply le_antisymm
  · rw [← @comap_norm_nhds_zero E p.toAddGroupSeminorm.toSeminormedAddGroup, ← tendsto_iff_comap]
    suffices Continuous p from this.tendsto' 0 _ (map_zero p)
    rcases h₁ with ⟨r, hr⟩
    exact p.continuous' hr
  · rw [(@NormedAddGroup.nhds_zero_basis_norm_lt E
      p.toAddGroupSeminorm.toSeminormedAddGroup).le_basis_iff hb]
    simpa only [subset_def, mem_ball_zero] using h₂

lemma uniformity_eq_of_hasBasis
    {ι} [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p' : ι → Prop} {s : ι → Set E} (p : Seminorm 𝕜 E) (hb : (𝓝 0 : Filter E).HasBasis p' s)
    (h₁ : ∃ r, p.closedBall 0 r ∈ 𝓝 0) (h₂ : ∀ i, p' i → ∃ r > 0, p.ball 0 r ⊆ s i) :
    𝓤 E = ⨅ r > 0, 𝓟 {x | p (x.1 - x.2) < r} := by
  rw [uniformSpace_eq_of_hasBasis p hb h₁ h₂]
  simp only [sub_eq_add_neg, ← map_neg_add p]
  rfl

end Continuity

section ShellLemmas

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Let `p` be a seminorm on a vector space over a `NormedField`.
If there is a scalar `c` with `‖c‖>1`, then any `x` such that `p x ≠ 0` can be
moved by scalar multiplication to any `p`-shell of width `‖c‖`. Also recap information on the
value of `p` on the rescaling element that shows up in applications. -/
lemma rescale_to_shell_zpow (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ}
    (εpos : 0 < ε) {x : E} (hx : p x ≠ 0) : ∃ n : ℤ, c ^ n ≠ 0 ∧
    p (c ^ n • x) < ε ∧ (ε / ‖c‖ ≤ p (c ^ n • x)) ∧ (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * p x) := by
  have xεpos : 0 < (p x) / ε := by positivity
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := by positivity
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by rw [norm_zpow]; exact xεpos.trans hn.2
  refine ⟨-(n + 1), ?_, ?_, ?_, ?_⟩
  · show c ^ (-(n + 1)) ≠ 0; exact zpow_ne_zero _ (norm_pos_iff.1 cpos)
  · show p ((c ^ (-(n + 1))) • x) < ε
    rw [map_smul_eq_mul, zpow_neg, norm_inv, ← div_eq_inv_mul, div_lt_iff₀ cnpos, mul_comm,
        norm_zpow]
    exact (div_lt_iff₀ εpos).1 (hn.2)
  · show ε / ‖c‖ ≤ p (c ^ (-(n + 1)) • x)
    rw [zpow_neg, div_le_iff₀ cpos, map_smul_eq_mul, norm_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos),
        zpow_one, mul_inv_rev, mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt cpos),
        one_mul, ← div_eq_inv_mul, le_div_iff₀ (zpow_pos cpos _), mul_comm]
    exact (le_div_iff₀ εpos).1 hn.1
  · show ‖(c ^ (-(n + 1)))‖⁻¹ ≤ ε⁻¹ * ‖c‖ * p x
    have : ε⁻¹ * ‖c‖ * p x = ε⁻¹ * p x * ‖c‖ := by ring
    rw [zpow_neg, norm_inv, inv_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos), zpow_one, this,
        ← div_eq_inv_mul]
    gcongr; exact hn.1

/-- Let `p` be a seminorm on a vector space over a `NormedField`.
If there is a scalar `c` with `‖c‖>1`, then any `x` such that `p x ≠ 0` can be
moved by scalar multiplication to any `p`-shell of width `‖c‖`. Also recap information on the
value of `p` on the rescaling element that shows up in applications. -/
lemma rescale_to_shell (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : p x ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ p (d • x) < ε ∧ (ε / ‖c‖ ≤ p (d • x)) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * p x) :=
let ⟨_, hn⟩ := p.rescale_to_shell_zpow hc εpos hx; ⟨_, hn⟩

/-- Let `p` and `q` be two seminorms on a vector space over a `NontriviallyNormedField`.
If we have `q x ≤ C * p x` on some shell of the form `{x | ε/‖c‖ ≤ p x < ε}` (where `ε > 0`
and `‖c‖ > 1`), then we also have `q x ≤ C * p x` for all `x` such that `p x ≠ 0`. -/
lemma bound_of_shell
    (p q : Seminorm 𝕜 E) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ p x → p x < ε → q x ≤ C * p x) {x : E} (hx : p x ≠ 0) :
    q x ≤ C * p x := by
  rcases p.rescale_to_shell hc ε_pos hx with ⟨δ, hδ, δxle, leδx, -⟩
  simpa only [map_smul_eq_mul, mul_left_comm C, mul_le_mul_iff_right₀ (norm_pos_iff.2 hδ)]
    using hf (δ • x) leδx δxle

/-- A version of `Seminorm.bound_of_shell` expressed using pointwise scalar multiplication of
seminorms. -/
lemma bound_of_shell_smul
    (p q : Seminorm 𝕜 E) {ε : ℝ} {C : ℝ≥0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ p x → p x < ε → q x ≤ (C • p) x) {x : E} (hx : p x ≠ 0) :
    q x ≤ (C • p) x :=
  Seminorm.bound_of_shell p q ε_pos hc hf hx

lemma bound_of_shell_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι)
    (q : Seminorm 𝕜 E) {ε : ℝ} {C : ℝ≥0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, (∀ i ∈ s, p i x < ε) → ∀ j ∈ s, ε / ‖c‖ ≤ p j x → q x ≤ (C • p j) x)
    {x : E} (hx : ∃ j, j ∈ s ∧ p j x ≠ 0) :
    q x ≤ (C • s.sup p) x := by
  rcases hx with ⟨j, hj, hjx⟩
  have : (s.sup p) x ≠ 0 :=
    ne_of_gt ((hjx.symm.lt_of_le <| apply_nonneg _ _).trans_le (le_finset_sup_apply hj))
  refine (s.sup p).bound_of_shell_smul q ε_pos hc (fun y hle hlt ↦ ?_) this
  rcases exists_apply_eq_finset_sup p ⟨j, hj⟩ y with ⟨i, hi, hiy⟩
  rw [smul_apply, hiy]
  exact hf y (fun k hk ↦ (le_finset_sup_apply hk).trans_lt hlt) i hi (hiy ▸ hle)

end ShellLemmas

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Let `p i` be a family of seminorms on `E`. Let `s` be an absorbent set in `𝕜`.
If all seminorms are uniformly bounded at every point of `s`,
then they are bounded in the space of seminorms. -/
lemma bddAbove_of_absorbent {ι : Sort*} {p : ι → Seminorm 𝕜 E} {s : Set E} (hs : Absorbent 𝕜 s)
    (h : ∀ x ∈ s, BddAbove (range (p · x))) : BddAbove (range p) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨c, hc₀, hc⟩ : ∃ c ≠ 0, (c : 𝕜) • x ∈ s :=
    (eventually_mem_nhdsWithin.and (hs.eventually_nhdsNE_zero x)).exists
  rcases h _ hc with ⟨M, hM⟩
  refine ⟨M / ‖c‖, forall_mem_range.mpr fun i ↦ (le_div_iff₀' (norm_pos_iff.2 hc₀)).2 ?_⟩
  exact hM ⟨i, map_smul_eq_mul ..⟩

end NontriviallyNormedField

end Seminorm

/-! ### The norm as a seminorm -/


section normSeminorm

variable (𝕜) (E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }

@[simp]
theorem coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm :=
  rfl

@[simp]
theorem ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.ball := by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]

@[simp]
theorem closedBall_normSeminorm : (normSeminorm 𝕜 E).closedBall = Metric.closedBall := by
  ext x r y
  simp only [Seminorm.mem_closedBall, Metric.mem_closedBall, coe_normSeminorm, dist_eq_norm]

variable {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball_zero hr

/-- Balls containing the origin are absorbent. -/
theorem absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball x r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball hx

/-- Balls at the origin are balanced. -/
theorem balanced_ball_zero : Balanced 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

/-- Closed balls at the origin are balanced. -/
theorem balanced_closedBall_zero : Balanced 𝕜 (Metric.closedBall (0 : E) r) := by
  rw [← closedBall_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_closedBall_zero r

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed_zpow {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : ‖x‖ ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell_zpow hc εpos hx

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε)
    {x : E} (hx : ‖x‖ ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell hc εpos hx

lemma rescale_to_shell_zpow [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : ℝ} (εpos : 0 < ε) {x : F} (hx : x ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed_zpow hc εpos (norm_ne_zero_iff.mpr hx)

/-- If there is a scalar `c` with `‖c‖>1`, then any element can be moved by scalar multiplication to
any shell of width `‖c‖`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
lemma rescale_to_shell [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : ℝ} (εpos : 0 < ε) {x : F} (hx : x ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed hc εpos (norm_ne_zero_iff.mpr hx)

end normSeminorm
