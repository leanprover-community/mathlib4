/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Invariants

/-!
# Induction

This files defines Hecke algebras and Hecke modules.

-/

@[expose] public section

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace Representation


variable {k : Type*} [CommRing k]
variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {W : Type*} [AddCommGroup W] [Module k W]

noncomputable section Hecke

variable (H : Subgroup G) (σ : Representation k H W) (ρ : Representation k G V)

/-- The twisted Hecke algebra with respect to a representation of a subgroup `H`. -/
abbrev HeckeAlgebra := (ind H.subtype σ).IntertwiningMap (ind H.subtype σ)

/-- The opposite algebra of the twisted Hecke algebra. -/
abbrev HeckeAlgebraOp := (MulOpposite (HeckeAlgebra H σ))

/-- The module over the opposite twisted Hecke algebra associated a representation `ρ` of `G`. -/
abbrev HeckeModule := (ind H.subtype σ).IntertwiningMap ρ

variable (k)

/-- The standard Hecke algebra of subgroup `H`. -/
abbrev HeckeAlgebra₁ := HeckeAlgebra H (trivial k H k)

/-- The opposite algebra of the standard Hecke algebra. -/
abbrev HeckeAlgebra₁Op := MulOpposite (HeckeAlgebra₁ k H)

variable {k} in
/-- The module over the opposite standard Hecke algebra associated a representation `ρ` of `G`. -/
abbrev HeckeModule₁ := (ind H.subtype (trivial k H k)).IntertwiningMap ρ

/-- The standard Hecke bimodule. -/
abbrev HeckeBimodule₁ (H₁ H₂ : Subgroup G) := HeckeModule₁ H₁ (ind H₂.subtype (trivial k H₂ k))

section cosetVector

/-- The unit vector supported on the left coset `gH`. -/
abbrev cosetVectorMk (g : G) (H : Subgroup G) :
    IndV H.subtype (trivial k H k) := IndV.mk H.subtype (trivial k H k) g⁻¹ 1

-- `H.subtype h` is not a simp normal form so we need additional simp lemmas.
@[simp]
lemma cosetVectorMk_mem_mul_eq {H : Subgroup G} {h : G} (hh : h ∈ H) (g : G) :
    cosetVectorMk k (g * h) H = cosetVectorMk k g H := by
  convert IndV.mk_map_inv_mul H.subtype (trivial k H k) ⟨h, hh⟩ g⁻¹ 1 <;> simp

@[simp]
lemma cosetVectorMk_mem_eq {H : Subgroup G} {h : G} (hh : h ∈ H) :
    cosetVectorMk k h H = cosetVectorMk k 1 H := by
  rw [← one_mul h]
  exact cosetVectorMk_mem_mul_eq k hh 1

@[simp 2000]
lemma ind_apply_cosetVectorMk {H : Subgroup G} (g x : G) :
    ind H.subtype (trivial k H k) g (cosetVectorMk k x H) = cosetVectorMk k (g * x) H := by
  simp [cosetVectorMk]

lemma cosetVectorMk_eq_ind_apply (H : Subgroup G) (g : G) :
    cosetVectorMk k g H = ind H.subtype (trivial k H k) g (cosetVectorMk k 1 H) := by
  simp

lemma smul_cosetVectorMk_eq {H : Subgroup G} (g : G) (r : k) :
    r • cosetVectorMk k g H = IndV.mk H.subtype (trivial k H k) g⁻¹ r := by
  simp [← map_smul]

lemma ind_trivial.cosetVectorMk_one.surjective {H : Subgroup G} {v : V}
    (f : IntertwiningMap ρ (ind H.subtype (trivial k H k))) (h : f v = cosetVectorMk k 1 H) :
    Function.Surjective f :=
  fun x => IndV.induction_on x
    (fun g r => ⟨ρ g⁻¹ (r • v), by simp [IntertwiningMap.isIntertwining, h, smul_cosetVectorMk_eq]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by simp [hx, hy]⟩)

def cosetVector {H : Subgroup G} :
    G ⧸ H → IndV H.subtype (trivial k H k) :=
  Quotient.lift (fun g => cosetVectorMk k g H) fun x _ h => by
    simpa [eq_comm] using cosetVectorMk_mem_mul_eq k (QuotientGroup.leftRel_apply.mp h) x

lemma cosetVectorMk_eq_cosetVector_mk (g : G) :
    cosetVectorMk k g H = cosetVector k ⟦g⟧ :=
  rfl

lemma cosetVectorMk_out_eq_cosetVector (x : G ⧸ H) :
    cosetVectorMk k x.out H = cosetVector k x := by
  simp [cosetVectorMk_eq_cosetVector_mk]

@[simp]
lemma ind_apply_cosetVector (g : G) (x : G ⧸ H) :
    ind H.subtype (trivial k H k) g (cosetVector k x) = cosetVector k (g • x) := by
  rw [← cosetVectorMk_out_eq_cosetVector, ind_apply_cosetVectorMk, cosetVectorMk_eq_cosetVector_mk]
  exact congrArg _ (MulAction.Quotient.mk_smul_out H g x)

def indTrivialToOfMulActionMap :
    IntertwiningMap (ind H.subtype (trivial k H k)) (ofMulAction k G (G ⧸ H)) where
  toLinearMap := IndV.lift H.subtype (trivial k H k)
    (fun g => LinearMap.toSpanSingleton k _ (MonoidAlgebra.single ⟦g⁻¹⟧ 1))
    (by intros; congr 3; exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simp)))
  isIntertwining' _ := by ext; simp

@[simp]
lemma indTrivialToOfMulActionMap_apply_cosetVector (x : G ⧸ H) :
    (indTrivialToOfMulActionMap k H) (cosetVector k x) = MonoidAlgebra.single x 1 := by
  simp [indTrivialToOfMulActionMap, ← cosetVectorMk_out_eq_cosetVector]

@[simps!]
def indTrivialToOfMulActionInv :
    IntertwiningMap (ofMulAction k G (G ⧸ H)) (ind H.subtype (trivial k H k)) where
  toLinearMap := (Finsupp.lsum k fun x => LinearMap.toSpanSingleton k _ (cosetVector k x)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  isIntertwining' _ := by ext; simp

def indTrivialOfMulActionEquiv :
    (ind H.subtype (trivial k H k)).Equiv (ofMulAction k G (G ⧸ H)) where
  toIntertwiningMap := indTrivialToOfMulActionMap k H
  invFun := (indTrivialToOfMulActionInv k H).toLinearMap
  left_inv x := IndV.induction_on x
    (by simp [indTrivialToOfMulActionMap, ← cosetVectorMk_eq_cosetVector_mk, smul_cosetVectorMk_eq])
    (by simp_all [map_add])
  right_inv x := MonoidAlgebra.induction x (by simp) fun g => Quotient.inductionOn g
    (by simp [indTrivialToOfMulActionMap, map_add, ← cosetVectorMk_eq_cosetVector_mk])

end cosetVector

variable {k}

section HeckeModule₁

@[ext]
lemma HeckeModule₁.ext {H : Subgroup G} (f g : HeckeModule₁ H ρ)
    (h : f (cosetVectorMk k 1 H) = g (cosetVectorMk k 1 H)) : f = g := by
  ext x
  rw [← inv_inv x]
  change f (cosetVectorMk k x⁻¹ H) = g (cosetVectorMk k x⁻¹ H)
  rw [cosetVectorMk_eq_ind_apply]
  simp only [IntertwiningMap.isIntertwining, h]

/-- Construct elements of the standard Hecke module from `H`-invariants. -/
def HeckeModule₁.invariantsMk :
    invariants (ρ.comp H.subtype) →ₗ[k] HeckeModule₁ H ρ where
  toFun v := ind.lift H.subtype
    ⟨LinearMap.toSpanSingleton k _ v.val, fun g => by ext; simpa [eq_comm] using v.prop g⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma HeckeModule₁.invariantsMk_apply (v : invariants (ρ.comp H.subtype)) (g : G) :
    HeckeModule₁.invariantsMk H ρ v (cosetVectorMk k g H) = ρ g v := by
  simp [invariantsMk]

/-- `HeckeModule₁.invariantsMk` is a linear equivalence. -/
def invariantsHeckeModule₁Equiv :
    invariants (ρ.comp H.subtype) ≃ₗ[k] HeckeModule₁ H ρ where
  toLinearMap := HeckeModule₁.invariantsMk H ρ
  invFun f := ⟨f (cosetVectorMk k 1 H), by simp [← IntertwiningMap.isIntertwining]⟩
  left_inv _ := by simp
  right_inv _ := by ext; simp

end HeckeModule₁

variable (k) (H₁ : Subgroup G) (g : G) (H₂ : Subgroup G) (g' : G) (H₃ : Subgroup G)

open Pointwise MonoidAlgebra

section HeckeTriple

lemma mem_conjAct_pointwise_smul_iff {H : Subgroup G} {g x : G} :
    x ∈ ConjAct.toConjAct g • H ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, inv_inv]

abbrev DecompQuotient := H₁ ⧸ ((ConjAct.toConjAct g) • H₂).subgroupOf H₁

lemma DecompQuotient.mul_mk_leftCoset_eq_iff (x x' : H₁) :
    (⟦x.val * g⟧ : G ⧸ H₂) = ⟦x'.val * g⟧ ↔ ⟦x⟧ = (⟦x'⟧ : DecompQuotient H₁ g H₂) := by
  simp [Quotient.eq, QuotientGroup.leftRel_apply, mul_assoc, Subgroup.mem_subgroupOf,
    mem_conjAct_pointwise_smul_iff]

def DecompQuotient.toLeftCoset :
    DecompQuotient H₁ g H₂ → G ⧸ H₂ :=
  Quotient.lift (fun x => ⟦x * g⟧) fun _ _ h => by
    rw [Quotient.eq, QuotientGroup.leftRel_apply]
    have := (QuotientGroup.leftRel_apply.mp h)
    simpa [mul_assoc] using mem_conjAct_pointwise_smul_iff.mp this

@[simp]
lemma DecompQuotient.toLeftCoset_apply (x : DecompQuotient H₁ g H₂) :
    DecompQuotient.toLeftCoset H₁ g H₂ x = ⟦x.out * g⟧ := by
  nth_rw 1 [← Quotient.out_eq x]
  rfl

class IsHeckeTriple : Prop where
  hasFiniteDecompQuotient : (((ConjAct.toConjAct g) • H₂)).IsFiniteRelIndex H₁

instance [h : IsHeckeTriple H₁ g H₂] : Fintype (DecompQuotient H₁ g H₂) := by
  have := h.hasFiniteDecompQuotient
  exact Subgroup.fintypeOfIndexNeZero Subgroup.relIndex_ne_zero

instance instIsHeckeTriple_diag_one (H : Subgroup G) : IsHeckeTriple H 1 H :=
  ⟨⟨by simp⟩⟩

instance instIsHeckeTriple_mulLeft [IsHeckeTriple H₁ g H₂] (h₁ : H₁) :
    IsHeckeTriple H₁ (h₁ * g) H₂ := ⟨by
  have hh : (ConjAct.toConjAct (h₁ : G)) • H₁ = H₁ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer h₁.prop)
  nth_rewrite 2 [← hh]
  simpa [mul_smul, Subgroup.relIndex_pointwise_smul, Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    using IsHeckeTriple.hasFiniteDecompQuotient⟩

lemma isHeckeTriple_mem_left [IsHeckeTriple H₁ 1 H₂] (h₁ : H₁) :
    IsHeckeTriple H₁ h₁ H₂ := by
  simpa using instIsHeckeTriple_mulLeft H₁ 1 H₂ h₁

instance instIsHeckeTriple_mulRight [IsHeckeTriple H₁ g H₂] (h₂ : H₂) :
    IsHeckeTriple H₁ (g * h₂) H₂ := ⟨by
  have hh : (ConjAct.toConjAct (h₂ : G)) • H₂ = H₂ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer h₂.prop)
  simpa [mul_smul, hh] using IsHeckeTriple.hasFiniteDecompQuotient⟩

lemma isHeckeTriple_mem_right [IsHeckeTriple H₁ 1 H₂] (h₂ : H₂) :
    IsHeckeTriple H₁ h₂ H₂ := by
  simpa using instIsHeckeTriple_mulRight H₁ 1 H₂ h₂

lemma isHeckeTriple_trans [IsHeckeTriple H₁ g H₂] [IsHeckeTriple H₂ g' H₃] :
    IsHeckeTriple H₁ (g * g') H₃ := ⟨⟨by
  have h₁₂ : ((ConjAct.toConjAct g) • H₂).relIndex H₁ ≠ 0 :=
    (IsHeckeTriple.hasFiniteDecompQuotient).relIndex_ne_zero
  have h₂₃ : ((ConjAct.toConjAct g) • ((ConjAct.toConjAct g') • H₃)).relIndex
      ((ConjAct.toConjAct g) • H₂) ≠ 0 := by
    rw [Subgroup.relIndex_pointwise_smul]
    exact (IsHeckeTriple.hasFiniteDecompQuotient).relIndex_ne_zero
  simpa [mul_smul] using Subgroup.relIndex_ne_zero_trans h₂₃ h₁₂⟩⟩

instance instIsHeckeTriple_trans [IsHeckeTriple H₁ g H₂]
    [IsHeckeTriple H₂ g' H₃] (h₂ : H₂) : IsHeckeTriple H₁ (g * h₂ * g') H₃ :=
  isHeckeTriple_trans H₁ (g * h₂) H₂ g' H₃

instance instIsHeckeTriple_diag_mul (H : Subgroup G) (g g' : G)
    [IsHeckeTriple H g H] [IsHeckeTriple H g' H] : IsHeckeTriple H (g * g') H := by
  simpa using isHeckeTriple_trans H g H g' H

abbrev HeckeSet : Set G := Set.ofPred (fun g => IsHeckeTriple H₁ g H₂)

instance (g : HeckeSet H₁ H₂) : IsHeckeTriple H₁ g.val H₂ := g.prop

abbrev HeckeSet.Setoid : Setoid (HeckeSet H₁ H₂) :=
  (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

def HeckeCoset := Quotient (HeckeSet.Setoid H₁ H₂)

abbrev HeckeCosetModule := HeckeCoset H₁ H₂ →₀ k

abbrev HeckeCosetVectorMk [hg : IsHeckeTriple H₁ g H₂] :
    IndV H₂.subtype (trivial k H₂ k) :=
  ∑ x, cosetVector k (DecompQuotient.toLeftCoset H₁ g H₂ x)

variable {H₁ H₂}

lemma HeckeCoset.mk_eq_iff (x y : HeckeSet H₁ H₂) :
    (⟦x⟧ : HeckeCoset H₁ H₂) = ⟦y⟧ ↔ ∃ (h₁ : H₁) (h₂ : H₂), y.val = h₁ * x.val * h₂ := by
  simpa [Quotient.eq] using DoubleCoset.rel_iff

lemma HeckeCoset.leftCoset_ne_if_ne {x y : HeckeCoset H₁ H₂} (hxy : x ≠ y) (h₁ : H₁) :
    (⟦h₁ * x.out⟧ : G ⧸ H₂) ≠ ⟦(y.out : G)⟧ := by
  intro h
  apply hxy
  sorry

def HeckeCosetVector : HeckeCoset H₁ H₂ → IndV H₂.subtype (trivial k H₂ k) :=
  fun h => ∑ x, cosetVector k (DecompQuotient.toLeftCoset H₁ h.out H₂ x)

lemma HeckeCosetVectorMk_out_eq_HeckeCosetVector (x : HeckeCoset H₁ H₂) :
    HeckeCosetVectorMk k H₁ x.out H₂ = HeckeCosetVector k x := by
  rfl

lemma HeckeCosetVector_isInvariant (x : HeckeCoset H₁ H₂) (h₁ : H₁) :
    ind H₂.subtype (trivial k H₂ k) h₁ (HeckeCosetVector k x) = HeckeCosetVector k x := by
  simp only [HeckeCosetVector, DecompQuotient.toLeftCoset_apply, map_sum, ind_apply_cosetVector]
  exact Fintype.sum_equiv (MulAction.toPerm h₁) _ _ fun y => by
    congr 1
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc]
    change ⟦(h₁ * y.out : H₁) * (x.out : G)⟧ = _
    rw [DecompQuotient.mul_mk_leftCoset_eq_iff]
    simp [← MulAction.Quotient.mk_smul_out]

lemma HeckeCoset.out_leftCoset.injective :
    Function.Injective (fun x : HeckeCoset H₁ H₂ => (⟦x.out⟧ : G ⧸ H₂)) := by
  intro x y h
  rw [← Quotient.out_eq' x, ← Quotient.out_eq' y]
  exact Quotient.sound <| DoubleCoset.rel_iff.mpr
    ⟨1, by simp, _, QuotientGroup.leftRel_apply.mp (Quotient.exact h), by simp⟩

end HeckeTriple

section bimodule₁

namespace HeckeBimodule₁

variable {H₁ H₂} in
abbrev mk (x : HeckeCoset H₁ H₂) : HeckeBimodule₁ k H₁ H₂ :=
  HeckeModule₁.invariantsMk H₁ _ ⟨HeckeCosetVector k x, HeckeCosetVector_isInvariant k x⟩

def toHeckeCosetModuleLinearMap :
    HeckeBimodule₁ k H₁ H₂ →ₗ[k] k[HeckeCoset H₁ H₂] where
  toFun f := MonoidAlgebra.comapDomain (fun x => ⟦x.out.val⟧) (HeckeCoset.out_leftCoset.injective)
    (indTrivialToOfMulActionMap k H₂ (f (cosetVectorMk k 1 H₁)))
  map_add' := by simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma toHeckeCosetModuleLinearMap_apply_HeckeCosetVector (x : HeckeCoset H₁ H₂) :
    (toHeckeCosetModuleLinearMap k H₁ H₂) (HeckeBimodule₁.mk k x) = single x 1
  := by classical
  ext y
  simp only [toHeckeCosetModuleLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    HeckeModule₁.invariantsMk_apply, map_one, Module.End.one_apply, coeff_comapDomain,
    Finsupp.comapDomain_apply, coeff_single]
  simp only [HeckeCosetVector, DecompQuotient.toLeftCoset_apply, map_sum,
    indTrivialToOfMulActionMap_apply_cosetVector, coeff_sum, coeff_single, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  by_cases hxy : x = y
  · have (g : G) (z : DecompQuotient H₁ g H₂) : (⟦(z.out : G) * g⟧ : G ⧸ H₂) = ⟦g⟧ ↔ z = ⟦1⟧ := by
      constructor
      · rw [← Quotient.out_eq' z, ← DecompQuotient.mul_mk_leftCoset_eq_iff]
        simp
      · rintro rfl
        nth_rw 4 [← one_mul g]
        change ⟦(⟦1⟧.out: H₁) * g⟧ = ⟦(1 : H₁) * g⟧
        rw [DecompQuotient.mul_mk_leftCoset_eq_iff]
        simp
    simp [← hxy, Finsupp.single_apply, this]
  · simp [hxy, HeckeCoset.leftCoset_ne_if_ne]

def toHeckeCosetModuleLinearInv :
    k[HeckeCoset H₁ H₂] →ₗ[k] HeckeBimodule₁ k H₁ H₂ :=
  (MonoidAlgebra.basis (HeckeCoset H₁ H₂) k).constr k fun x => HeckeBimodule₁.mk k x

@[simp]
lemma toHeckeCosetModuleLinearInv_apply_single (x : HeckeCoset H₁ H₂) :
    ((toHeckeCosetModuleLinearInv k H₁ H₂) (single x 1)) = HeckeBimodule₁.mk k x := by
  simp [toHeckeCosetModuleLinearInv, ← MonoidAlgebra.basis_apply]

variable {k H₁ H₂} in
lemma induction_on (f : HeckeBimodule₁ k H₁ H₂) {p : HeckeBimodule₁ k H₁ H₂ → Prop}
    (mk : ∀ (g : HeckeCoset H₁ H₂), p (HeckeBimodule₁.mk k g))
    (smul : ∀ (x : HeckeBimodule₁ k H₁ H₂) (r : k), p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) : p f := by
  sorry

def toHeckeCosetModuleLinearEquiv :
    HeckeBimodule₁ k H₁ H₂ ≃ₗ[k] k[HeckeCoset H₁ H₂] where
  toLinearMap := toHeckeCosetModuleLinearMap k H₁ H₂
  invFun := toHeckeCosetModuleLinearInv k H₁ H₂
  left_inv f := induction_on f
    (p := fun x => (toHeckeCosetModuleLinearInv _ _ _) (toHeckeCosetModuleLinearMap _ _ _ x) = x)
    (by simp) (fun _ _ h => by simp [h]) (fun _ _ hx hy => by simp [hx, hy])
  right_inv x := induction_linear x (by simp) (fun _ _ h h' => by nth_rw 2 [← h, ← h']; simp) <| by
    intro _ r
    rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul]
    simp

end HeckeBimodule₁

end bimodule₁

section HeckeOperator

end HeckeOperator

end Hecke

noncomputable section

namespace Rep

universe u
variable {G : Type u} [Group G]
variable {k : Type u} [CommRing k]
variable (H : Subgroup G)
variable {W : Type u} [AddCommGroup W] [Module k W] (σ : Representation k H W)

open CategoryTheory

/-- The module over the opposite twisted Hecke algebra associated a representation `ρ` of `G`. -/
abbrev toHeckeModule (A : Rep k G) : ModuleCat (HeckeAlgebraOp H σ) :=
  ModuleCat.of (HeckeAlgebraOp H σ) (HeckeModule H σ A.ρ)

/-- The module over the opposite standard Hecke algebra associated a representation `ρ` of `G`. -/
abbrev toHecke₁Module (A : Rep k G) : ModuleCat (HeckeAlgebra₁Op k H) :=
  ModuleCat.of (HeckeAlgebra₁Op k H) (HeckeModule₁ H A.ρ)

/-- The induced map between Hecke modules from a morphism between represeentations. -/
abbrev toHeckeModuleMap {A B : Rep k G} (f : A ⟶ B) : toHeckeModule H σ A ⟶ toHeckeModule H σ B :=
  ModuleCat.ofHom {
    toFun g := f.hom.comp g
    map_add' x y := by rw [IntertwiningMap.add_comp]
    map_smul' _ _ := rfl}

/-- The induced map between Hecke modules over the opposite standard Hecke algebra from a morphism
between representations. -/
abbrev toHecke₁ModuleMap {A B : Rep k G} (f : A ⟶ B) : toHecke₁Module H A ⟶ toHecke₁Module H B :=
  ModuleCat.ofHom {
    toFun g := f.hom.comp g
    map_add' x y := by rw [IntertwiningMap.add_comp]
    map_smul' _ _ := rfl}

/-- The functor sending represenations to Hecke modules over the opposite twisted Hecke algbera. -/
abbrev toHeckeModuleFunctor : Rep k G ⥤ ModuleCat (HeckeAlgebraOp H σ) where
  obj := toHeckeModule H σ
  map := toHeckeModuleMap H σ

/-- The functor sending represenations to Hecke modules over the opposite standard Hecke algbera. -/
abbrev toHecke₁ModuleFunctor : Rep k G ⥤ ModuleCat (HeckeAlgebra₁Op k H) where
  obj := toHecke₁Module H
  map := toHecke₁ModuleMap H

end Rep

end

end Representation
