/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll

! This file was ported from Lean 3 source module analysis.seminorm
! leanprover-community/mathlib commit 7ebf83ed9c262adbf983ef64d5e8c2ae94b625f4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Pointwise
import Mathbin.Analysis.Convex.Function
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Analysis.Normed.Group.AddTorsor

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For a module over a normed ring:
* `seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `norm_seminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm, locally convex, LCTVS
-/


open NormedField Set

open BigOperators NNReal Pointwise Topology

variable {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F G ι : Type _}

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
structure Seminorm (𝕜 : Type _) (E : Type _) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] extends
  AddGroupSeminorm E where
  smul' : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ‖a‖ * to_fun x
#align seminorm Seminorm

attribute [nolint doc_blame] Seminorm.toAddGroupSeminorm

/-- `seminorm_class F 𝕜 E` states that `F` is a type of seminorms on the `𝕜`-module E.

You should extend this class when you extend `seminorm`. -/
class SeminormClass (F : Type _) (𝕜 E : outParam <| Type _) [SeminormedRing 𝕜] [AddGroup E]
  [SMul 𝕜 E] extends AddGroupSeminormClass F E ℝ where
  map_smul_eq_mul (f : F) (a : 𝕜) (x : E) : f (a • x) = ‖a‖ * f x
#align seminorm_class SeminormClass

export SeminormClass (map_smul_eq_mul)

-- `𝕜` is an `out_param`, so this is a false positive.
attribute [nolint dangerous_instance] SeminormClass.toAddGroupSeminormClass

section Of

/-- Alternative constructor for a `seminorm` on an `add_comm_group E` that is a module over a
`semi_norm_ring 𝕜`. -/
def Seminorm.of [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ)
    (add_le : ∀ x y : E, f (x + y) ≤ f x + f y) (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x) :
    Seminorm 𝕜 E where
  toFun := f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, MulZeroClass.zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]
#align seminorm.of Seminorm.of

/-- Alternative constructor for a `seminorm` over a normed field `𝕜` that only assumes `f 0 = 0`
and an inequality for the scalar multiplication. -/
def Seminorm.ofSmulLe [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ) (map_zero : f 0 = 0)
    (add_le : ∀ x y, f (x + y) ≤ f x + f y) (smul_le : ∀ (r : 𝕜) (x), f (r • x) ≤ ‖r‖ * f x) :
    Seminorm 𝕜 E :=
  Seminorm.of f add_le fun r x =>
    by
    refine' le_antisymm (smul_le r x) _
    by_cases r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_left (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] at smul_le
    convert smul_le
    simp [h]
#align seminorm.of_smul_le Seminorm.ofSmulLe

end Of

namespace Seminorm

section SeminormedRing

variable [SeminormedRing 𝕜]

section AddGroup

variable [AddGroup E]

section SMul

variable [SMul 𝕜 E]

instance seminormClass : SeminormClass (Seminorm 𝕜 E) 𝕜 E
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_neg_eq_map f := f.neg'
  map_smul_eq_mul f := f.smul'
#align seminorm.seminorm_class Seminorm.seminormClass

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (Seminorm 𝕜 E) fun _ => E → ℝ :=
  FunLike.hasCoeToFun

@[ext]
theorem ext {p q : Seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
  FunLike.ext p q h
#align seminorm.ext Seminorm.ext

instance : Zero (Seminorm 𝕜 E) :=
  ⟨{ AddGroupSeminorm.hasZero.zero with smul' := fun _ _ => (MulZeroClass.mul_zero _).symm }⟩

@[simp]
theorem coe_zero : ⇑(0 : Seminorm 𝕜 E) = 0 :=
  rfl
#align seminorm.coe_zero Seminorm.coe_zero

@[simp]
theorem zero_apply (x : E) : (0 : Seminorm 𝕜 E) x = 0 :=
  rfl
#align seminorm.zero_apply Seminorm.zero_apply

instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨0⟩

variable (p : Seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] : SMul R (Seminorm 𝕜 E)
    where smul r p :=
    { r • p.toAddGroupSeminorm with
      toFun := fun x => r • p x
      smul' := fun _ _ =>
        by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul]
        rw [map_smul_eq_mul, mul_left_comm] }

instance [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] [SMul R' ℝ] [SMul R' ℝ≥0]
    [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] : IsScalarTower R R' (Seminorm 𝕜 E)
    where smul_assoc r a p := ext fun x => smul_assoc r a (p x)

theorem coe_smul [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) :
    ⇑(r • p) = r • p :=
  rfl
#align seminorm.coe_smul Seminorm.coe_smul

@[simp]
theorem smul_apply [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E)
    (x : E) : (r • p) x = r • p x :=
  rfl
#align seminorm.smul_apply Seminorm.smul_apply

instance : Add (Seminorm 𝕜 E)
    where add p q :=
    {
      p.toAddGroupSeminorm +
        q.toAddGroupSeminorm with
      toFun := fun x => p x + q x
      smul' := fun a x => by simp only [map_smul_eq_mul, map_smul_eq_mul, mul_add] }

theorem coe_add (p q : Seminorm 𝕜 E) : ⇑(p + q) = p + q :=
  rfl
#align seminorm.coe_add Seminorm.coe_add

@[simp]
theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
  rfl
#align seminorm.add_apply Seminorm.add_apply

instance : AddMonoid (Seminorm 𝕜 E) :=
  FunLike.coe_injective.AddMonoid _ rfl coe_add fun p n => coe_smul n p

instance : OrderedCancelAddCommMonoid (Seminorm 𝕜 E) :=
  FunLike.coe_injective.OrderedCancelAddCommMonoid _ rfl coe_add fun p n => coe_smul n p

instance [Monoid R] [MulAction R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] :
    MulAction R (Seminorm 𝕜 E) :=
  FunLike.coe_injective.MulAction _ coe_smul

variable (𝕜 E)

/-- `coe_fn` as an `add_monoid_hom`. Helper definition for showing that `seminorm 𝕜 E` is
a module. -/
@[simps]
def coeFnAddMonoidHom : AddMonoidHom (Seminorm 𝕜 E) (E → ℝ) :=
  ⟨coeFn, coe_zero, coe_add⟩
#align seminorm.coe_fn_add_monoid_hom Seminorm.coeFnAddMonoidHom

theorem coeFnAddMonoidHom_injective : Function.Injective (coeFnAddMonoidHom 𝕜 E) :=
  show @Function.Injective (Seminorm 𝕜 E) (E → ℝ) coeFn from FunLike.coe_injective
#align seminorm.coe_fn_add_monoid_hom_injective Seminorm.coeFnAddMonoidHom_injective

variable {𝕜 E}

instance [Monoid R] [DistribMulAction R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] :
    DistribMulAction R (Seminorm 𝕜 E) :=
  (coeFnAddMonoidHom_injective 𝕜 E).DistribMulAction _ coe_smul

instance [Semiring R] [Module R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] : Module R (Seminorm 𝕜 E) :=
  (coeFnAddMonoidHom_injective 𝕜 E).Module R _ coe_smul

instance : Sup (Seminorm 𝕜 E)
    where sup p q :=
    {
      p.toAddGroupSeminorm ⊔ q.toAddGroupSeminorm with
      toFun := p ⊔ q
      smul' := fun x v =>
        (congr_arg₂ max (map_smul_eq_mul p x v) (map_smul_eq_mul q x v)).trans <|
          (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]
theorem coe_sup (p q : Seminorm 𝕜 E) : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align seminorm.coe_sup Seminorm.coe_sup

theorem sup_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align seminorm.sup_apply Seminorm.sup_apply

theorem smul_sup [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0).Prop
  ext fun x => real.smul_max _ _
#align seminorm.smul_sup Seminorm.smul_sup

instance : PartialOrder (Seminorm 𝕜 E) :=
  PartialOrder.lift _ FunLike.coe_injective

@[simp, norm_cast]
theorem coe_le_coe {p q : Seminorm 𝕜 E} : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align seminorm.coe_le_coe Seminorm.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe {p q : Seminorm 𝕜 E} : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align seminorm.coe_lt_coe Seminorm.coe_lt_coe

theorem le_def {p q : Seminorm 𝕜 E} : p ≤ q ↔ ∀ x, p x ≤ q x :=
  Iff.rfl
#align seminorm.le_def Seminorm.le_def

theorem lt_def {p q : Seminorm 𝕜 E} : p < q ↔ p ≤ q ∧ ∃ x, p x < q x :=
  Pi.lt_def
#align seminorm.lt_def Seminorm.lt_def

instance : SemilatticeSup (Seminorm 𝕜 E) :=
  Function.Injective.semilatticeSup _ FunLike.coe_injective coe_sup

end SMul

end AddGroup

section Module

variable [SeminormedRing 𝕜₂] [SeminormedRing 𝕜₃]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

variable {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₂₃]

variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomIsometric σ₁₃]

variable [AddCommGroup E] [AddCommGroup E₂] [AddCommGroup E₃]

variable [AddCommGroup F] [AddCommGroup G]

variable [Module 𝕜 E] [Module 𝕜₂ E₂] [Module 𝕜₃ E₃] [Module 𝕜 F] [Module 𝕜 G]

variable [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E :=
  {
    p.toAddGroupSeminorm.comp
      f.toAddMonoidHom with
    toFun := fun x => p (f x)
    smul' := fun _ _ => by rw [map_smulₛₗ, map_smul_eq_mul, RingHomIsometric.is_iso] }
#align seminorm.comp Seminorm.comp

theorem coe_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : ⇑(p.comp f) = p ∘ f :=
  rfl
#align seminorm.coe_comp Seminorm.coe_comp

@[simp]
theorem comp_apply (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) : (p.comp f) x = p (f x) :=
  rfl
#align seminorm.comp_apply Seminorm.comp_apply

@[simp]
theorem comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p :=
  ext fun _ => rfl
#align seminorm.comp_id Seminorm.comp_id

@[simp]
theorem comp_zero (p : Seminorm 𝕜₂ E₂) : p.comp (0 : E →ₛₗ[σ₁₂] E₂) = 0 :=
  ext fun _ => map_zero p
#align seminorm.comp_zero Seminorm.comp_zero

@[simp]
theorem zero_comp (f : E →ₛₗ[σ₁₂] E₂) : (0 : Seminorm 𝕜₂ E₂).comp f = 0 :=
  ext fun _ => rfl
#align seminorm.zero_comp Seminorm.zero_comp

theorem comp_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (p : Seminorm 𝕜₃ E₃) (g : E₂ →ₛₗ[σ₂₃] E₃)
    (f : E →ₛₗ[σ₁₂] E₂) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl
#align seminorm.comp_comp Seminorm.comp_comp

theorem add_comp (p q : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) :
    (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl
#align seminorm.add_comp Seminorm.add_comp

theorem comp_add_le (p : Seminorm 𝕜₂ E₂) (f g : E →ₛₗ[σ₁₂] E₂) :
    p.comp (f + g) ≤ p.comp f + p.comp g := fun _ => map_add_le_add p _ _
#align seminorm.comp_add_le Seminorm.comp_add_le

theorem smul_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : R) :
    (c • p).comp f = c • p.comp f :=
  ext fun _ => rfl
#align seminorm.smul_comp Seminorm.smul_comp

theorem comp_mono {p q : Seminorm 𝕜₂ E₂} (f : E →ₛₗ[σ₁₂] E₂) (hp : p ≤ q) : p.comp f ≤ q.comp f :=
  fun _ => hp _
#align seminorm.comp_mono Seminorm.comp_mono

/-- The composition as an `add_monoid_hom`. -/
@[simps]
def pullback (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜₂ E₂ →+ Seminorm 𝕜 E :=
  ⟨fun p => p.comp f, zero_comp f, fun p q => add_comp p q f⟩
#align seminorm.pullback Seminorm.pullback

instance : OrderBot (Seminorm 𝕜 E) :=
  ⟨0, map_nonneg⟩

@[simp]
theorem coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0 :=
  rfl
#align seminorm.coe_bot Seminorm.coe_bot

theorem bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0 :=
  rfl
#align seminorm.bot_eq_zero Seminorm.bot_eq_zero

theorem smul_le_smul {p q : Seminorm 𝕜 E} {a b : ℝ≥0} (hpq : p ≤ q) (hab : a ≤ b) : a • p ≤ b • q :=
  by
  simp_rw [le_def, coe_smul]
  intro x
  simp_rw [Pi.smul_apply, NNReal.smul_def, smul_eq_mul]
  exact mul_le_mul hab (hpq x) (map_nonneg p x) (NNReal.coe_nonneg b)
#align seminorm.smul_le_smul Seminorm.smul_le_smul

theorem finset_sup_apply (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = ↑(s.sup fun i => ⟨p i x, map_nonneg (p i) x⟩ : ℝ≥0) :=
  by
  induction' s using Finset.cons_induction_on with a s ha ih
  ·
    rw [Finset.sup_empty, Finset.sup_empty, coe_bot, _root_.bot_eq_zero, Pi.zero_apply,
      Nonneg.coe_zero]
  ·
    rw [Finset.sup_cons, Finset.sup_cons, coe_sup, sup_eq_max, Pi.sup_apply, sup_eq_max,
      NNReal.coe_max, Subtype.coe_mk, ih]
#align seminorm.finset_sup_apply Seminorm.finset_sup_apply

theorem finset_sup_le_sum (p : ι → Seminorm 𝕜 E) (s : Finset ι) : s.sup p ≤ ∑ i in s, p i := by
  classical
    refine' finset.sup_le_iff.mpr _
    intro i hi
    rw [Finset.sum_eq_sum_diff_singleton_add hi, le_add_iff_nonneg_left]
    exact bot_le
#align seminorm.finset_sup_le_sum Seminorm.finset_sup_le_sum

theorem finset_sup_apply_le {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, i ∈ s → p i x ≤ a) : s.sup p x ≤ a :=
  by
  lift a to ℝ≥0 using ha
  rw [finset_sup_apply, NNReal.coe_le_coe]
  exact Finset.sup_le h
#align seminorm.finset_sup_apply_le Seminorm.finset_sup_apply_le

theorem finset_sup_apply_lt {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 < a)
    (h : ∀ i, i ∈ s → p i x < a) : s.sup p x < a :=
  by
  lift a to ℝ≥0 using ha.le
  rw [finset_sup_apply, NNReal.coe_lt_coe, Finset.sup_lt_iff]
  · exact h
  · exact nnreal.coe_pos.mpr ha
#align seminorm.finset_sup_apply_lt Seminorm.finset_sup_apply_lt

theorem norm_sub_map_le_sub (p : Seminorm 𝕜 E) (x y : E) : ‖p x - p y‖ ≤ p (x - y) :=
  abs_sub_map_le_sub p x y
#align seminorm.norm_sub_map_le_sub Seminorm.norm_sub_map_le_sub

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
#align seminorm.comp_smul Seminorm.comp_smul

theorem comp_smul_apply (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E) :
    p.comp (c • f) x = ‖c‖ * p (f x) :=
  map_smul_eq_mul p _ _
#align seminorm.comp_smul_apply Seminorm.comp_smul_apply

end SeminormedCommRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {p q : Seminorm 𝕜 E} {x : E}

/-- Auxiliary lemma to show that the infimum of seminorms is well-defined. -/
theorem bddBelow_range_add : BddBelow (range fun u => p u + q (x - u)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩
#align seminorm.bdd_below_range_add Seminorm.bddBelow_range_add

noncomputable instance : Inf (Seminorm 𝕜 E)
    where inf p q :=
    {
      p.toAddGroupSeminorm ⊓
        q.toAddGroupSeminorm with
      toFun := fun x => ⨅ u : E, p u + q (x - u)
      smul' := by
        intro a x
        obtain rfl | ha := eq_or_ne a 0
        · rw [norm_zero, MulZeroClass.zero_mul, zero_smul]
          refine'
            cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt (fun i => by positivity) fun x hx =>
              ⟨0, by rwa [map_zero, sub_zero, map_zero, add_zero]⟩
        simp_rw [Real.mul_infᵢ_of_nonneg (norm_nonneg a), mul_add, ← map_smul_eq_mul p, ←
          map_smul_eq_mul q, smul_sub]
        refine'
          Function.Surjective.infᵢ_congr ((· • ·) a⁻¹ : E → E)
            (fun u => ⟨a • u, inv_smul_smul₀ ha u⟩) fun u => _
        rw [smul_inv_smul₀ ha] }

@[simp]
theorem inf_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊓ q) x = ⨅ u : E, p u + q (x - u) :=
  rfl
#align seminorm.inf_apply Seminorm.inf_apply

noncomputable instance : Lattice (Seminorm 𝕜 E) :=
  { Seminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
      cinfᵢ_le_of_le bddBelow_range_add x <| by simp only [sub_self, map_zero, add_zero]
    inf_le_right := fun p q x =>
      cinfᵢ_le_of_le bddBelow_range_add 0 <| by simp only [sub_self, map_zero, zero_add, sub_zero]
    le_inf := fun a b c hab hac x =>
      le_cinfᵢ fun u => (le_map_add_map_sub a _ _).trans <| add_le_add (hab _) (hac _) }

theorem smul_inf [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊓ q) = r • p ⊓ r • q := by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def,
    smul_eq_mul, Real.mul_infᵢ_of_nonneg (Subtype.prop _), mul_add]
#align seminorm.smul_inf Seminorm.smul_inf

section Classical

open Classical

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr⨆ , »((i), _)]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr⨆ , »((i), _)]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr⨆ , »((i), _)]] -/
/-- We define the supremum of an arbitrary subset of `seminorm 𝕜 E` as follows:
* if `s` is `bdd_above` *as a set of functions `E → ℝ`* (that is, if `s` is pointwise bounded
above), we take the pointwise supremum of all elements of `s`, and we prove that it is indeed a
seminorm.
* otherwise, we take the zero seminorm `⊥`.

There are two things worth mentionning here:
* First, it is not trivial at first that `s` being bounded above *by a function* implies
being bounded above *as a seminorm*. We show this in `seminorm.bdd_above_iff` by using
that the `Sup s` as defined here is then a bounding seminorm for `s`. So it is important to make
the case disjunction on `bdd_above (coe_fn '' s : set (E → ℝ))` and not `bdd_above s`.
* Since the pointwise `Sup` already gives `0` at points where a family of functions is
not bounded above, one could hope that just using the pointwise `Sup` would work here, without the
need for an additional case disjunction. As discussed on Zulip, this doesn't work because this can
give a function which does *not* satisfy the seminorm axioms (typically sub-additivity).
-/
noncomputable instance : SupSet (Seminorm 𝕜 E)
    where supₛ s :=
    if h : BddAbove (coeFn '' s : Set (E → ℝ)) then
      { toFun := ⨆ p : s, ((p : Seminorm 𝕜 E) : E → ℝ)
        map_zero' := by
          rw [supᵢ_apply, ← @Real.csupᵢ_const_zero s]
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr⨆ , »((i), _)]]"
          exact map_zero i.1
        add_le' := fun x y => by
          rcases h with ⟨q, hq⟩
          obtain rfl | h := s.eq_empty_or_nonempty
          · simp [Real.csupᵢ_empty]
          haveI : Nonempty ↥s := h.coe_sort
          simp only [supᵢ_apply]
          refine'
                csupᵢ_le fun i =>
                  ((i : Seminorm 𝕜 E).add_le' x y).trans <|
                    add_le_add (le_csupᵢ ⟨q x, _⟩ i) (le_csupᵢ ⟨q y, _⟩ i) <;>
              rw [mem_upperBounds, forall_range_iff] <;>
            exact fun j => hq (mem_image_of_mem _ j.2) _
        neg' := fun x => by
          simp only [supᵢ_apply]
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr⨆ , »((i), _)]]"
          exact i.1.neg' _
        smul' := fun a x => by
          simp only [supᵢ_apply]
          rw [← smul_eq_mul,
            Real.smul_supᵢ_of_nonneg (norm_nonneg a) fun i : s => (i : Seminorm 𝕜 E) x]
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr⨆ , »((i), _)]]"
          exact i.1.smul' a x }
    else ⊥

protected theorem coe_supₛ_eq' {s : Set <| Seminorm 𝕜 E}
    (hs : BddAbove (coeFn '' s : Set (E → ℝ))) : coeFn (supₛ s) = ⨆ p : s, p :=
  congr_arg _ (dif_pos hs)
#align seminorm.coe_Sup_eq' Seminorm.coe_supₛ_eq'

protected theorem bddAbove_iff {s : Set <| Seminorm 𝕜 E} :
    BddAbove s ↔ BddAbove (coeFn '' s : Set (E → ℝ)) :=
  ⟨fun ⟨q, hq⟩ => ⟨q, ball_image_of_ball fun p hp => hq hp⟩, fun H =>
    ⟨supₛ s, fun p hp x => by
      rw [Seminorm.coe_supₛ_eq' H, supᵢ_apply]
      rcases H with ⟨q, hq⟩
      exact
        le_csupᵢ ⟨q x, forall_range_iff.mpr fun i : s => hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩⟩⟩
#align seminorm.bdd_above_iff Seminorm.bddAbove_iff

protected theorem coe_supₛ_eq {s : Set <| Seminorm 𝕜 E} (hs : BddAbove s) :
    coeFn (supₛ s) = ⨆ p : s, p :=
  Seminorm.coe_supₛ_eq' (Seminorm.bddAbove_iff.mp hs)
#align seminorm.coe_Sup_eq Seminorm.coe_supₛ_eq

protected theorem coe_supᵢ_eq {ι : Type _} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) :
    coeFn (⨆ i, p i) = ⨆ i, p i := by
  rw [← supₛ_range, Seminorm.coe_supₛ_eq hp] <;> exact supᵢ_range' (coeFn : Seminorm 𝕜 E → E → ℝ) p
#align seminorm.coe_supr_eq Seminorm.coe_supᵢ_eq

private theorem seminorm.is_lub_Sup (s : Set (Seminorm 𝕜 E)) (hs₁ : BddAbove s) (hs₂ : s.Nonempty) :
    IsLUB s (supₛ s) :=
  by
  refine' ⟨fun p hp x => _, fun p hp x => _⟩ <;> haveI : Nonempty ↥s := hs₂.coe_sort <;>
    rw [Seminorm.coe_supₛ_eq hs₁, supᵢ_apply]
  · rcases hs₁ with ⟨q, hq⟩
    exact le_csupᵢ ⟨q x, forall_range_iff.mpr fun i : s => hq i.2 x⟩ ⟨p, hp⟩
  · exact csupᵢ_le fun q => hp q.2 x
#align seminorm.seminorm.is_lub_Sup seminorm.seminorm.is_lub_Sup

/-- `seminorm 𝕜 E` is a conditionally complete lattice.

Note that, while `inf`, `sup` and `Sup` have good definitional properties (corresponding to
`seminorm.has_inf`, `seminorm.has_sup` and `seminorm.has_Sup` respectively), `Inf s` is just
defined as the supremum of the lower bounds of `s`, which is not really useful in practice. If you
need to use `Inf` on seminorms, then you should probably provide a more workable definition first,
but this is unlikely to happen so we keep the "bad" definition for now. -/
noncomputable instance : ConditionallyCompleteLattice (Seminorm 𝕜 E) :=
  conditionallyCompleteLatticeOfLatticeOfSupₛ (Seminorm 𝕜 E) Seminorm.isLUB_supₛ

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
#align seminorm.ball Seminorm.ball

/-- The closed ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y`
with `p (y - x) ≤ r`. -/
def closedBall (x : E) (r : ℝ) :=
  { y : E | p (y - x) ≤ r }
#align seminorm.closed_ball Seminorm.closedBall

variable {x y : E} {r : ℝ}

@[simp]
theorem mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
  Iff.rfl
#align seminorm.mem_ball Seminorm.mem_ball

@[simp]
theorem mem_closedBall : y ∈ closedBall p x r ↔ p (y - x) ≤ r :=
  Iff.rfl
#align seminorm.mem_closed_ball Seminorm.mem_closedBall

theorem mem_ball_self (hr : 0 < r) : x ∈ ball p x r := by simp [hr]
#align seminorm.mem_ball_self Seminorm.mem_ball_self

theorem mem_closedBall_self (hr : 0 ≤ r) : x ∈ closedBall p x r := by simp [hr]
#align seminorm.mem_closed_ball_self Seminorm.mem_closedBall_self

theorem mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]
#align seminorm.mem_ball_zero Seminorm.mem_ball_zero

theorem mem_closedBall_zero : y ∈ closedBall p 0 r ↔ p y ≤ r := by rw [mem_closed_ball, sub_zero]
#align seminorm.mem_closed_ball_zero Seminorm.mem_closedBall_zero

theorem ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
  Set.ext fun x => p.mem_ball_zero
#align seminorm.ball_zero_eq Seminorm.ball_zero_eq

theorem closedBall_zero_eq : closedBall p 0 r = { y : E | p y ≤ r } :=
  Set.ext fun x => p.mem_closedBall_zero
#align seminorm.closed_ball_zero_eq Seminorm.closedBall_zero_eq

theorem ball_subset_closedBall (x r) : ball p x r ⊆ closedBall p x r := fun y (hy : _ < _) => hy.le
#align seminorm.ball_subset_closed_ball Seminorm.ball_subset_closedBall

theorem closedBall_eq_bInter_ball (x r) : closedBall p x r = ⋂ ρ > r, ball p x ρ := by
  ext y <;> simp_rw [mem_closed_ball, mem_Inter₂, mem_ball, ← forall_lt_iff_le']
#align seminorm.closed_ball_eq_bInter_ball Seminorm.closedBall_eq_bInter_ball

@[simp]
theorem ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminorm 𝕜 E) x r = Set.univ :=
  by
  rw [Set.eq_univ_iff_forall, ball]
  simp [hr]
#align seminorm.ball_zero' Seminorm.ball_zero'

@[simp]
theorem closedBall_zero' (x : E) (hr : 0 < r) : closedBall (0 : Seminorm 𝕜 E) x r = Set.univ :=
  eq_univ_of_subset (ball_subset_closedBall _ _ _) (ball_zero' x hr)
#align seminorm.closed_ball_zero' Seminorm.closedBall_zero'

theorem ball_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : ℝ) (x : E) :
    (c • p).ball x r = p.ball x (r / c) := by
  ext
  rw [mem_ball, mem_ball, smul_apply, NNReal.smul_def, smul_eq_mul, mul_comm,
    lt_div_iff (nnreal.coe_pos.mpr hc)]
#align seminorm.ball_smul Seminorm.ball_smul

theorem closedBall_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : ℝ) (x : E) :
    (c • p).closedBall x r = p.closedBall x (r / c) :=
  by
  ext
  rw [mem_closed_ball, mem_closed_ball, smul_apply, NNReal.smul_def, smul_eq_mul, mul_comm,
    le_div_iff (nnreal.coe_pos.mpr hc)]
#align seminorm.closed_ball_smul Seminorm.closedBall_smul

theorem ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) :
    ball (p ⊔ q) e r = ball p e r ∩ ball q e r := by
  simp_rw [ball, ← Set.setOf_and, coe_sup, Pi.sup_apply, sup_lt_iff]
#align seminorm.ball_sup Seminorm.ball_sup

theorem closedBall_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) :
    closedBall (p ⊔ q) e r = closedBall p e r ∩ closedBall q e r := by
  simp_rw [closed_ball, ← Set.setOf_and, coe_sup, Pi.sup_apply, sup_le_iff]
#align seminorm.closed_ball_sup Seminorm.closedBall_sup

theorem ball_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E) (r : ℝ) :
    ball (s.sup' H p) e r = s.inf' H fun i => ball (p i) e r :=
  by
  induction' H using Finset.Nonempty.cons_induction with a a s ha hs ih
  · classical simp
  · rw [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]
#align seminorm.ball_finset_sup' Seminorm.ball_finset_sup'

theorem closedBall_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E)
    (r : ℝ) : closedBall (s.sup' H p) e r = s.inf' H fun i => closedBall (p i) e r :=
  by
  induction' H using Finset.Nonempty.cons_induction with a a s ha hs ih
  · classical simp
  · rw [Finset.sup'_cons hs, Finset.inf'_cons hs, closed_ball_sup, inf_eq_inter, ih]
#align seminorm.closed_ball_finset_sup' Seminorm.closedBall_finset_sup'

theorem ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ :=
  fun _ (hx : _ < _) => hx.trans_le h
#align seminorm.ball_mono Seminorm.ball_mono

theorem closedBall_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    p.closedBall x r₁ ⊆ p.closedBall x r₂ := fun _ (hx : _ ≤ _) => hx.trans h
#align seminorm.closed_ball_mono Seminorm.closedBall_mono

theorem ball_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r := fun _ =>
  (h _).trans_lt
#align seminorm.ball_antitone Seminorm.ball_antitone

theorem closedBall_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) :
    p.closedBall x r ⊆ q.closedBall x r := fun _ => (h _).trans
#align seminorm.closed_ball_antitone Seminorm.closedBall_antitone

theorem ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) :=
  by
  rintro x ⟨y₁, y₂, hy₁, hy₂, rfl⟩
  rw [mem_ball, add_sub_add_comm]
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂)
#align seminorm.ball_add_ball_subset Seminorm.ball_add_ball_subset

theorem closedBall_add_closedBall_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.closedBall (x₁ : E) r₁ + p.closedBall (x₂ : E) r₂ ⊆ p.closedBall (x₁ + x₂) (r₁ + r₂) :=
  by
  rintro x ⟨y₁, y₂, hy₁, hy₂, rfl⟩
  rw [mem_closed_ball, add_sub_add_comm]
  exact (map_add_le_add p _ _).trans (add_le_add hy₁ hy₂)
#align seminorm.closed_ball_add_closed_ball_subset Seminorm.closedBall_add_closedBall_subset

theorem sub_mem_ball (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : ℝ) :
    x₁ - x₂ ∈ p.ball y r ↔ x₁ ∈ p.ball (x₂ + y) r := by simp_rw [mem_ball, sub_sub]
#align seminorm.sub_mem_ball Seminorm.sub_mem_ball

/-- The image of a ball under addition with a singleton is another ball. -/
theorem vadd_ball (p : Seminorm 𝕜 E) : x +ᵥ p.ball y r = p.ball (x +ᵥ y) r :=
  letI := AddGroupSeminorm.toSeminormedAddCommGroup p.to_add_group_seminorm
  Metric.vadd_ball x y r
#align seminorm.vadd_ball Seminorm.vadd_ball

/-- The image of a closed ball under addition with a singleton is another closed ball. -/
theorem vadd_closedBall (p : Seminorm 𝕜 E) : x +ᵥ p.closedBall y r = p.closedBall (x +ᵥ y) r :=
  letI := AddGroupSeminorm.toSeminormedAddCommGroup p.to_add_group_seminorm
  Metric.vadd_closedBall x y r
#align seminorm.vadd_closed_ball Seminorm.vadd_closedBall

end SMul

section Module

variable [Module 𝕜 E]

variable [SeminormedRing 𝕜₂] [AddCommGroup E₂] [Module 𝕜₂ E₂]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

theorem ball_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
    (p.comp f).ball x r = f ⁻¹' p.ball (f x) r :=
  by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_setOf_eq, map_sub]
#align seminorm.ball_comp Seminorm.ball_comp

theorem closedBall_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
    (p.comp f).closedBall x r = f ⁻¹' p.closedBall (f x) r :=
  by
  ext
  simp_rw [closed_ball, mem_preimage, comp_apply, Set.mem_setOf_eq, map_sub]
#align seminorm.closed_ball_comp Seminorm.closedBall_comp

variable (p : Seminorm 𝕜 E)

theorem preimage_metric_ball {r : ℝ} : p ⁻¹' Metric.ball 0 r = { x | p x < r } :=
  by
  ext x
  simp only [mem_set_of, mem_preimage, mem_ball_zero_iff, Real.norm_of_nonneg (map_nonneg p _)]
#align seminorm.preimage_metric_ball Seminorm.preimage_metric_ball

theorem preimage_metric_closedBall {r : ℝ} : p ⁻¹' Metric.closedBall 0 r = { x | p x ≤ r } :=
  by
  ext x
  simp only [mem_set_of, mem_preimage, mem_closedBall_zero_iff,
    Real.norm_of_nonneg (map_nonneg p _)]
#align seminorm.preimage_metric_closed_ball Seminorm.preimage_metric_closedBall

theorem ball_zero_eq_preimage_ball {r : ℝ} : p.ball 0 r = p ⁻¹' Metric.ball 0 r := by
  rw [ball_zero_eq, preimage_metric_ball]
#align seminorm.ball_zero_eq_preimage_ball Seminorm.ball_zero_eq_preimage_ball

theorem closedBall_zero_eq_preimage_closedBall {r : ℝ} :
    p.closedBall 0 r = p ⁻¹' Metric.closedBall 0 r := by
  rw [closed_ball_zero_eq, preimage_metric_closed_ball]
#align seminorm.closed_ball_zero_eq_preimage_closed_ball Seminorm.closedBall_zero_eq_preimage_closedBall

@[simp]
theorem ball_bot {r : ℝ} (x : E) (hr : 0 < r) : ball (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  ball_zero' x hr
#align seminorm.ball_bot Seminorm.ball_bot

@[simp]
theorem closedBall_bot {r : ℝ} (x : E) (hr : 0 < r) :
    closedBall (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  closedBall_zero' x hr
#align seminorm.closed_ball_bot Seminorm.closedBall_bot

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero (r : ℝ) : Balanced 𝕜 (ball p 0 r) :=
  by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero, ← hx, map_smul_eq_mul]
  calc
    _ ≤ p y := mul_le_of_le_one_left (map_nonneg p _) ha
    _ < r := by rwa [mem_ball_zero] at hy
    
#align seminorm.balanced_ball_zero Seminorm.balanced_ball_zero

/-- Closed seminorm-balls at the origin are balanced. -/
theorem balanced_closedBall_zero (r : ℝ) : Balanced 𝕜 (closedBall p 0 r) :=
  by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_closed_ball_zero, ← hx, map_smul_eq_mul]
  calc
    _ ≤ p y := mul_le_of_le_one_left (map_nonneg p _) ha
    _ ≤ r := by rwa [mem_closed_ball_zero] at hy
    
#align seminorm.balanced_closed_ball_zero Seminorm.balanced_closedBall_zero

theorem ball_finset_sup_eq_interᵢ (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ}
    (hr : 0 < r) : ball (s.sup p) x r = ⋂ i ∈ s, ball (p i) x r :=
  by
  lift r to NNReal using hr.le
  simp_rw [ball, Inter_set_of, finset_sup_apply, NNReal.coe_lt_coe,
    Finset.sup_lt_iff (show ⊥ < r from hr), ← NNReal.coe_lt_coe, Subtype.coe_mk]
#align seminorm.ball_finset_sup_eq_Inter Seminorm.ball_finset_sup_eq_interᵢ

theorem closedBall_finset_sup_eq_interᵢ (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ}
    (hr : 0 ≤ r) : closedBall (s.sup p) x r = ⋂ i ∈ s, closedBall (p i) x r :=
  by
  lift r to NNReal using hr
  simp_rw [closed_ball, Inter_set_of, finset_sup_apply, NNReal.coe_le_coe, Finset.sup_le_iff, ←
    NNReal.coe_le_coe, Subtype.coe_mk]
#align seminorm.closed_ball_finset_sup_eq_Inter Seminorm.closedBall_finset_sup_eq_interᵢ

theorem ball_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
    ball (s.sup p) x r = s.inf fun i => ball (p i) x r :=
  by
  rw [Finset.inf_eq_infᵢ]
  exact ball_finset_sup_eq_Inter _ _ _ hr
#align seminorm.ball_finset_sup Seminorm.ball_finset_sup

theorem closedBall_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    closedBall (s.sup p) x r = s.inf fun i => closedBall (p i) x r :=
  by
  rw [Finset.inf_eq_infᵢ]
  exact closed_ball_finset_sup_eq_Inter _ _ _ hr
#align seminorm.closed_ball_finset_sup Seminorm.closedBall_finset_sup

theorem ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) :
    Metric.ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) :=
  by
  rw [Set.subset_def]
  intro x hx
  rw [Set.mem_smul] at hx
  rcases hx with ⟨a, y, ha, hy, hx⟩
  rw [← hx, mem_ball_zero, map_smul_eq_mul]
  exact
    mul_lt_mul'' (mem_ball_zero_iff.mp ha) (p.mem_ball_zero.mp hy) (norm_nonneg a) (map_nonneg p y)
#align seminorm.ball_smul_ball Seminorm.ball_smul_ball

theorem closedBall_smul_closedBall (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) :
    Metric.closedBall (0 : 𝕜) r₁ • p.closedBall 0 r₂ ⊆ p.closedBall 0 (r₁ * r₂) :=
  by
  rw [Set.subset_def]
  intro x hx
  rw [Set.mem_smul] at hx
  rcases hx with ⟨a, y, ha, hy, hx⟩
  rw [← hx, mem_closed_ball_zero, map_smul_eq_mul]
  rw [mem_closedBall_zero_iff] at ha
  exact mul_le_mul ha (p.mem_closed_ball_zero.mp hy) (map_nonneg _ y) ((norm_nonneg a).trans ha)
#align seminorm.closed_ball_smul_closed_ball Seminorm.closedBall_smul_closedBall

@[simp]
theorem ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ :=
  by
  ext
  rw [Seminorm.mem_ball, Set.mem_empty_iff_false, iff_false_iff, not_lt]
  exact hr.trans (map_nonneg p _)
#align seminorm.ball_eq_emptyset Seminorm.ball_eq_emptyset

@[simp]
theorem closedBall_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r < 0) :
    p.closedBall x r = ∅ := by
  ext
  rw [Seminorm.mem_closedBall, Set.mem_empty_iff_false, iff_false_iff, not_le]
  exact hr.trans_le (map_nonneg _ _)
#align seminorm.closed_ball_eq_emptyset Seminorm.closedBall_eq_emptyset

end Module

end AddCommGroup

end SeminormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {A B : Set E} {a : 𝕜}
  {r : ℝ} {x : E}

theorem ball_norm_mul_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
    p.ball 0 (‖k‖ * r) ⊆ k • p.ball 0 r :=
  by
  rcases eq_or_ne k 0 with (rfl | hk)
  · rw [norm_zero, MulZeroClass.zero_mul, ball_eq_emptyset _ le_rfl]
    exact empty_subset _
  · intro x
    rw [Set.mem_smul_set, Seminorm.mem_ball_zero]
    refine' fun hx => ⟨k⁻¹ • x, _, _⟩
    ·
      rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ←
        mul_lt_mul_left <| norm_pos_iff.mpr hk, ← mul_assoc, ← div_eq_mul_inv ‖k‖ ‖k‖,
        div_self (ne_of_gt <| norm_pos_iff.mpr hk), one_mul]
    rw [← smul_assoc, smul_eq_mul, ← div_eq_mul_inv, div_self hk, one_smul]
#align seminorm.ball_norm_mul_subset Seminorm.ball_norm_mul_subset

theorem smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : k ≠ 0) :
    k • p.ball 0 r = p.ball 0 (‖k‖ * r) := by
  ext
  rw [mem_smul_set_iff_inv_smul_mem₀ hk, p.mem_ball_zero, p.mem_ball_zero, map_smul_eq_mul,
    norm_inv, ← div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hk), mul_comm]
#align seminorm.smul_ball_zero Seminorm.smul_ball_zero

theorem smul_closedBall_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
    k • p.closedBall 0 r ⊆ p.closedBall 0 (‖k‖ * r) :=
  by
  rintro x ⟨y, hy, h⟩
  rw [Seminorm.mem_closedBall_zero, ← h, map_smul_eq_mul]
  rw [Seminorm.mem_closedBall_zero] at hy
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
#align seminorm.smul_closed_ball_subset Seminorm.smul_closedBall_subset

theorem smul_closedBall_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : 0 < ‖k‖) :
    k • p.closedBall 0 r = p.closedBall 0 (‖k‖ * r) :=
  by
  refine' subset_antisymm smul_closed_ball_subset _
  intro x
  rw [Set.mem_smul_set, Seminorm.mem_closedBall_zero]
  refine' fun hx => ⟨k⁻¹ • x, _, _⟩
  ·
    rwa [Seminorm.mem_closedBall_zero, map_smul_eq_mul, norm_inv, ← mul_le_mul_left hk, ← mul_assoc,
      ← div_eq_mul_inv ‖k‖ ‖k‖, div_self (ne_of_gt hk), one_mul]
  rw [← smul_assoc, smul_eq_mul, ← div_eq_mul_inv, div_self (norm_pos_iff.mp hk), one_smul]
#align seminorm.smul_closed_ball_zero Seminorm.smul_closedBall_zero

theorem ball_zero_absorbs_ball_zero (p : Seminorm 𝕜 E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) :=
  by
  rcases exists_pos_lt_mul hr₁ r₂ with ⟨r, hr₀, hr⟩
  refine' ⟨r, hr₀, fun a ha x hx => _⟩
  rw [smul_ball_zero (norm_pos_iff.1 <| hr₀.trans_le ha), p.mem_ball_zero]
  rw [p.mem_ball_zero] at hx
  exact hx.trans (hr.trans_le <| mul_le_mul_of_nonneg_right ha hr₁.le)
#align seminorm.ball_zero_absorbs_ball_zero Seminorm.ball_zero_absorbs_ball_zero

/-- Seminorm-balls at the origin are absorbent. -/
protected theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (ball p (0 : E) r) :=
  absorbent_iff_forall_absorbs_singleton.2 fun x =>
    (p.ball_zero_absorbs_ball_zero hr).mono_right <|
      singleton_subset_iff.2 <| p.mem_ball_zero.2 <| lt_add_one _
#align seminorm.absorbent_ball_zero Seminorm.absorbent_ball_zero

/-- Closed seminorm-balls at the origin are absorbent. -/
protected theorem absorbent_closedBall_zero (hr : 0 < r) : Absorbent 𝕜 (closedBall p (0 : E) r) :=
  (p.absorbent_ball_zero hr).Subset (p.ball_subset_closedBall _ _)
#align seminorm.absorbent_closed_ball_zero Seminorm.absorbent_closedBall_zero

/-- Seminorm-balls containing the origin are absorbent. -/
protected theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (ball p x r) :=
  by
  refine' (p.absorbent_ball_zero <| sub_pos.2 hpr).Subset fun y hy => _
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt <| add_lt_of_lt_sub_right hy)
#align seminorm.absorbent_ball Seminorm.absorbent_ball

/-- Seminorm-balls containing the origin are absorbent. -/
protected theorem absorbent_closedBall (hpr : p x < r) : Absorbent 𝕜 (closedBall p x r) :=
  by
  refine' (p.absorbent_closed_ball_zero <| sub_pos.2 hpr).Subset fun y hy => _
  rw [p.mem_closed_ball_zero] at hy
  exact p.mem_closed_ball.2 ((map_sub_le_add p _ _).trans <| add_le_of_le_sub_right hy)
#align seminorm.absorbent_closed_ball Seminorm.absorbent_closedBall

theorem symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
  balanced_ball_zero p r (-1) (by rw [norm_neg, norm_one]) ⟨x, hx, by rw [neg_smul, one_smul]⟩
#align seminorm.symmetric_ball_zero Seminorm.symmetric_ball_zero

@[simp]
theorem neg_ball (p : Seminorm 𝕜 E) (r : ℝ) (x : E) : -ball p x r = ball p (-x) r :=
  by
  ext
  rw [mem_neg, mem_ball, mem_ball, ← neg_add', sub_neg_eq_add, map_neg_eq_map]
#align seminorm.neg_ball Seminorm.neg_ball

@[simp]
theorem smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (· • ·) a ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ‖a‖) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_ball, mem_ball, lt_div_iff (norm_pos_iff.mpr ha), mul_comm, ←
      map_smul_eq_mul p, smul_sub, smul_inv_smul₀ ha]
#align seminorm.smul_ball_preimage Seminorm.smul_ball_preimage

end NormedField

section Convex

variable [NormedField 𝕜] [AddCommGroup E] [NormedSpace ℝ 𝕜] [Module 𝕜 E]

section SMul

variable [SMul ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected theorem convexOn : ConvexOn ℝ univ p :=
  by
  refine' ⟨convex_univ, fun x _ y _ a b ha hb hab => _⟩
  calc
    p (a • x + b • y) ≤ p (a • x) + p (b • y) := map_add_le_add p _ _
    _ = ‖a • (1 : 𝕜)‖ * p x + ‖b • (1 : 𝕜)‖ * p y := by
      rw [← map_smul_eq_mul p, ← map_smul_eq_mul p, smul_one_smul, smul_one_smul]
    _ = a * p x + b * p y := by
      rw [norm_smul, norm_smul, norm_one, mul_one, mul_one, Real.norm_of_nonneg ha,
        Real.norm_of_nonneg hb]
    
#align seminorm.convex_on Seminorm.convexOn

end SMul

section Module

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
theorem convex_ball : Convex ℝ (ball p x r) :=
  by
  convert(p.convex_on.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg]
  rfl
#align seminorm.convex_ball Seminorm.convex_ball

/-- Closed seminorm-balls are convex. -/
theorem convex_closedBall : Convex ℝ (closedBall p x r) :=
  by
  rw [closed_ball_eq_bInter_ball]
  exact convex_interᵢ₂ fun _ _ => convex_ball _ _ _
#align seminorm.convex_closed_ball Seminorm.convex_closedBall

end Module

end Convex

section RestrictScalars

variable (𝕜) {𝕜' : Type _} [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormOneClass 𝕜'] [AddCommGroup E] [Module 𝕜' E] [SMul 𝕜 E] [IsScalarTower 𝕜 𝕜' E]

/-- Reinterpret a seminorm over a field `𝕜'` as a seminorm over a smaller field `𝕜`. This will
typically be used with `is_R_or_C 𝕜'` and `𝕜 = ℝ`. -/
protected def restrictScalars (p : Seminorm 𝕜' E) : Seminorm 𝕜 E :=
  { p with
    smul' := fun a x => by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one] }
#align seminorm.restrict_scalars Seminorm.restrictScalars

@[simp]
theorem coe_restrictScalars (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜 : E → ℝ) = p :=
  rfl
#align seminorm.coe_restrict_scalars Seminorm.coe_restrictScalars

@[simp]
theorem restrictScalars_ball (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜).ball = p.ball :=
  rfl
#align seminorm.restrict_scalars_ball Seminorm.restrictScalars_ball

@[simp]
theorem restrictScalars_closedBall (p : Seminorm 𝕜' E) :
    (p.restrictScalars 𝕜).closedBall = p.closedBall :=
  rfl
#align seminorm.restrict_scalars_closed_ball Seminorm.restrictScalars_closedBall

end RestrictScalars

/-! ### Continuity criterions for seminorms -/


section Continuity

variable [NontriviallyNormedField 𝕜] [SeminormedRing 𝕝] [AddCommGroup E] [Module 𝕜 E]

variable [Module 𝕝 E]

theorem continuousAt_zero' [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hr : 0 < r) (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) : ContinuousAt p 0 :=
  by
  refine' metric.nhds_basis_closed_ball.tendsto_right_iff.mpr _
  intro ε hε
  rw [map_zero]
  suffices p.closed_ball 0 ε ∈ (𝓝 0 : Filter E) by
    rwa [Seminorm.closedBall_zero_eq_preimage_closedBall] at this
  rcases exists_norm_lt 𝕜 (div_pos hε hr) with ⟨k, hk0, hkε⟩
  have hk0' := norm_pos_iff.mp hk0
  have := (set_smul_mem_nhds_zero_iff hk0').mpr hp
  refine' Filter.mem_of_superset this (smul_set_subset_iff.mpr fun x hx => _)
  rw [mem_closed_ball_zero, map_smul_eq_mul, ← div_mul_cancel ε hr.ne.symm]
  exact mul_le_mul hkε.le (p.mem_closed_ball_zero.mp hx) (map_nonneg _ _) (div_nonneg hε.le hr.le)
#align seminorm.continuous_at_zero' Seminorm.continuousAt_zero'

theorem continuousAt_zero [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hr : 0 < r) (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) : ContinuousAt p 0 :=
  continuousAt_zero' hr (Filter.mem_of_superset hp <| p.ball_subset_closedBall _ _)
#align seminorm.continuous_at_zero Seminorm.continuousAt_zero

protected theorem uniformContinuous_of_continuousAt_zero [UniformSpace E] [UniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : UniformContinuous p :=
  by
  have hp : Filter.Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero_swapped,
    Metric.uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp.comp Filter.tendsto_comap)
      (fun xy => dist_nonneg) fun xy => p.norm_sub_map_le_sub _ _
#align seminorm.uniform_continuous_of_continuous_at_zero Seminorm.uniformContinuous_of_continuousAt_zero

protected theorem continuous_of_continuousAt_zero [TopologicalSpace E] [TopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : Continuous p :=
  by
  letI := TopologicalAddGroup.toUniformSpace E
  haveI : UniformAddGroup E := comm_topologicalAddGroup_is_uniform
  exact (Seminorm.uniformContinuous_of_continuousAt_zero hp).Continuous
#align seminorm.continuous_of_continuous_at_zero Seminorm.continuous_of_continuousAt_zero

protected theorem uniformContinuous [UniformSpace E] [UniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p : Seminorm 𝕜 E} {r : ℝ} (hr : 0 < r) (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero hr hp)
#align seminorm.uniform_continuous Seminorm.uniformContinuous

protected theorem uniform_continuous' [UniformSpace E] [UniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p : Seminorm 𝕜 E} {r : ℝ} (hr : 0 < r) (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero' hr hp)
#align seminorm.uniform_continuous' Seminorm.uniform_continuous'

protected theorem continuous [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p : Seminorm 𝕜 E} {r : ℝ} (hr : 0 < r) (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) : Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero hr hp)
#align seminorm.continuous Seminorm.continuous

protected theorem continuous' [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p : Seminorm 𝕜 E} {r : ℝ} (hr : 0 < r) (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero' hr hp)
#align seminorm.continuous' Seminorm.continuous'

theorem continuous_of_le [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p q : Seminorm 𝕜 E} (hq : Continuous q) (hpq : p ≤ q) : Continuous p :=
  by
  refine'
    Seminorm.continuous one_pos
      (Filter.mem_of_superset (IsOpen.mem_nhds _ <| q.mem_ball_self zero_lt_one)
        (ball_antitone hpq))
  rw [ball_zero_eq]
  exact isOpen_lt hq continuous_const
#align seminorm.continuous_of_le Seminorm.continuous_of_le

end Continuity

end Seminorm

/-! ### The norm as a seminorm -/


section normSeminorm

variable (𝕜) (E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }
#align norm_seminorm normSeminorm

@[simp]
theorem coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm :=
  rfl
#align coe_norm_seminorm coe_normSeminorm

@[simp]
theorem ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.ball :=
  by
  ext (x r y)
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]
#align ball_norm_seminorm ball_normSeminorm

variable {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.ball (0 : E) r) :=
  by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball_zero hr
#align absorbent_ball_zero absorbent_ball_zero

/-- Balls containing the origin are absorbent. -/
theorem absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball x r) :=
  by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball hx
#align absorbent_ball absorbent_ball

/-- Balls at the origin are balanced. -/
theorem balanced_ball_zero : Balanced 𝕜 (Metric.ball (0 : E) r) :=
  by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r
#align balanced_ball_zero balanced_ball_zero

end normSeminorm

-- Guard against import creep.
assert_not_exists balancedCore

