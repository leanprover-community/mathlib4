/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Trace

/-!
# Induction

This file defines Hecke algebras and Hecke modules. We construct central elements in the standard
Hecke algebra from trace of relatively compact representations under `IsHeckeUnimodular` and
`IsHeckeInvertible` condition. We also prove that such elements are non-zero and idempotent.

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

instance instPrecompSMul (σ : Representation k G W) :
    SMul (MulOpposite (IntertwiningMap σ σ)) (IntertwiningMap σ ρ) where
  smul f g := g.comp f.unop

instance instPrecompModule (σ : Representation k G W) :
    Module (MulOpposite (IntertwiningMap σ σ)) (IntertwiningMap σ ρ) :=
  fast_instance%
  {one_smul _ := rfl, mul_smul _ _ _ := rfl, smul_zero _ := IntertwiningMap.zero_comp _ _ _ _,
    smul_add f x y := IntertwiningMap.comp_add _ _ _ x y f.unop,
    add_smul x y f := IntertwiningMap.add_comp _ _ _ f x.unop y.unop,
    zero_smul := IntertwiningMap.comp_zero _ _ _}

/-- The module over the opposite twisted Hecke algebra associated a representation `ρ` of `G`. -/
abbrev HeckeModule := (ind H.subtype σ).IntertwiningMap ρ

/-- The twisted Hecke algebra with respect to a representation of a subgroup `H`. -/
abbrev HeckeAlgebraUnop := HeckeModule H σ (ind H.subtype σ)

/-- The twisted Hecke algebra. -/
abbrev HeckeAlgebra := (MulOpposite (HeckeAlgebraUnop H σ))

variable (k)

/-- The standard Hecke algebra of subgroup `H`. -/
abbrev HeckeAlgebra₁Unop := HeckeAlgebraUnop H (trivial k H k)

/-- The standard Hecke algebra. -/
abbrev HeckeAlgebra₁ := MulOpposite (HeckeAlgebra₁Unop k H)

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
    r • cosetVectorMk k g⁻¹ H = IndV.mk H.subtype (trivial k H k) g r := by
  simp [← map_smul]

lemma ind_trivial.cosetVectorMk_one.surjective {H : Subgroup G} {v : V}
    (f : IntertwiningMap ρ (ind H.subtype (trivial k H k))) (h : f v = cosetVectorMk k 1 H) :
    Function.Surjective f :=
  fun x => IndV.induction_on x
    (fun g r => ⟨ρ g⁻¹ (r • v), by simp [IntertwiningMap.isIntertwining, h, smul_cosetVectorMk_eq]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by simp [hx, hy]⟩)

/-- tbd -/
def cosetVector {H : Subgroup G} :
    G ⧸ H → IndV H.subtype (trivial k H k) :=
  Quotient.lift (fun g => cosetVectorMk k g H) fun x _ h => by
    simpa [eq_comm] using cosetVectorMk_mem_mul_eq k (QuotientGroup.leftRel_apply.mp h) x

@[simp]
lemma cosetVector_mk_eq_cosetVectorMk (g : G) :
    cosetVector k g = cosetVectorMk k g H :=
  rfl

lemma cosetVector_eq_cosetVectorMk_out (x : G ⧸ H) :
     cosetVector k x = cosetVectorMk k x.out H := by
  simp [← cosetVector_mk_eq_cosetVectorMk]

@[simp 500]
lemma ind_apply_cosetVector (g : G) (x : G ⧸ H) :
    ind H.subtype (trivial k H k) g (cosetVector k x) = cosetVector k (g • x) := by
  rw [cosetVector_eq_cosetVectorMk_out, ind_apply_cosetVectorMk, ← cosetVector_mk_eq_cosetVectorMk]
  exact congrArg _ (MulAction.Quotient.mk_smul_out H g x)

/-- tbd -/
def indTrivialToOfMulActionMap :
    IntertwiningMap (ind H.subtype (trivial k H k)) (ofMulAction k G (G ⧸ H)) where
  toLinearMap := IndV.lift H.subtype (trivial k H k)
    (fun g => LinearMap.toSpanSingleton k _ (MonoidAlgebra.single (QuotientGroup.mk g⁻¹ : G ⧸ H) 1))
    (by intros; congr 3; exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simp)))
  isIntertwining' _ := by ext; simp

@[simp]
lemma indTrivialToOfMulActionMap_apply_cosetVectorMk (g : G) :
    indTrivialToOfMulActionMap k H (cosetVectorMk k g H) = MonoidAlgebra.single (g : G ⧸ H) 1 := by
  simp [indTrivialToOfMulActionMap]

@[simp]
lemma indTrivialToOfMulActionMap_apply_cosetVector (x : G ⧸ H) :
    (indTrivialToOfMulActionMap k H) (cosetVector k x) = MonoidAlgebra.single x 1 := by
  simp [cosetVector_eq_cosetVectorMk_out]

/-- tbd -/
@[simps!]
def indTrivialToOfMulActionInv :
    IntertwiningMap (ofMulAction k G (G ⧸ H)) (ind H.subtype (trivial k H k)) where
  toLinearMap := (Finsupp.lsum k fun x => LinearMap.toSpanSingleton k _ (cosetVector k x)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  isIntertwining' _ := by ext; simp

/-- tbd -/
def indTrivialOfMulActionEquiv :
    (ind H.subtype (trivial k H k)).Equiv (ofMulAction k G (G ⧸ H)) where
  toIntertwiningMap := indTrivialToOfMulActionMap k H
  invFun := (indTrivialToOfMulActionInv k H).toLinearMap
  left_inv x := IndV.induction_on x
    (by intros; rw [← smul_cosetVectorMk_eq]; simp)
    (by simp_all [map_add])
  right_inv x := MonoidAlgebra.induction_linear x (by simp) (by simp_all [map_add]) (by simp)

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
@[simps!]
def HeckeModule₁.invariantsEquiv :
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

lemma DoubleCoset.conjAct_relIndex_eq (x y : G)
    (hxy : DoubleCoset.mk H₁ H₂ x = DoubleCoset.mk H₁ H₂ y) :
    (ConjAct.toConjAct x • H₂).relIndex H₁ = (ConjAct.toConjAct y • H₂).relIndex H₁ := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := DoubleCoset.rel_iff.mp (Quotient.exact hxy)
  have hH₁ : ConjAct.toConjAct h₁ • H₁ = H₁ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh₁)
  have hH₂ : ConjAct.toConjAct h₂ • H₂ = H₂ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh₂)
  nth_rewrite 2 [← hH₁]
  simp [mul_smul, hH₂, Subgroup.relIndex_pointwise_smul]

@[simp]
lemma DoubleCoset.mk_mul_left_eq {h₁ : G} (hh₁ : h₁ ∈ H₁) (g : G) :
    DoubleCoset.mk H₁ H₂ (h₁ * g) = DoubleCoset.mk H₁ H₂ g :=
  (DoubleCoset.eq H₁ H₂ (h₁ * g) g).mpr ⟨h₁⁻¹, H₁.inv_mem hh₁, 1, H₂.one_mem, by simp⟩

@[simp]
lemma DoubleCoset.mk_mul_right_eq {h₂ : G} (hh₂ : h₂ ∈ H₂) (g : G) :
    DoubleCoset.mk H₁ H₂ (g * h₂) = DoubleCoset.mk H₁ H₂ g :=
  (DoubleCoset.eq H₁ H₂ (g * h₂) g).mpr ⟨1, H₁.one_mem, h₂⁻¹, inv_mem hh₂, by simp⟩

/-- tbd -/
abbrev DecompQuotient := H₁ ⧸ ((ConjAct.toConjAct g) • H₂).subgroupOf H₁

/-- tbd -/
def DecompQuotient.toLeftCoset :
    DecompQuotient H₁ g H₂ → G ⧸ H₂ :=
  Quotient.lift (fun x => QuotientGroup.mk (x * g)) fun _ _ h => by
    rw [Quotient.eq, QuotientGroup.leftRel_apply]
    have := (QuotientGroup.leftRel_apply.mp h)
    simpa [mul_assoc] using mem_conjAct_pointwise_smul_iff.mp this

variable {H₁ g H₂}

lemma DecompQuotient.mk_eq_iff {x x' : H₁} :
    (x : DecompQuotient H₁ g H₂) = (x' : DecompQuotient H₁ g H₂)
      ↔ (x.val * g : G ⧸ H₂) = (x'.val * g : G ⧸ H₂):= by
  simp [QuotientGroup.eq, mul_assoc, Subgroup.mem_subgroupOf, mem_conjAct_pointwise_smul_iff]

lemma DecompQuotient.eq_one_iff {x : DecompQuotient H₁ g H₂} :
    x = ((1 : H₁) : DecompQuotient H₁ g H₂) ↔ ((x.out : G) * g : G ⧸ H₂) = (g : G ⧸ H₂) := by
  constructor <;> (rw [← Quotient.out_eq' x, DecompQuotient.mk_eq_iff]; simp)

@[simp]
lemma DecompQuotient.toLeftCoset_apply (x : DecompQuotient H₁ g H₂) :
    DecompQuotient.toLeftCoset H₁ g H₂ x = (x.out.val * g : G ⧸ H₂) := by
  nth_rw 1 [← Quotient.out_eq x]
  rfl

lemma DecompQuotient.toLeftCoset.injective (H₁ H₂ : Subgroup G) (g : G) :
    Function.Injective (DecompQuotient.toLeftCoset H₁ g H₂) := by
  intro i j hij
  simp only [DecompQuotient.toLeftCoset_apply] at hij
  simpa using DecompQuotient.mk_eq_iff.mpr hij

variable {H₃} in
lemma DecompQuotient.snd_eq_of_fst_eq {g g' d : G} {i : DecompQuotient H₁ g H₂}
    {j₁ j₂ : DecompQuotient H₂ g' H₃}
    (h₁ : ((i.out : G) * g * ((j₁.out : G) * g') : G ⧸ H₃) = (d : G ⧸ H₃))
    (h₂ : ((i.out : G) * g * ((j₂.out : G) * g') : G ⧸ H₃) = (d : G ⧸ H₃)) :
    j₁ = j₂ := by
  apply DecompQuotient.toLeftCoset.injective H₂ H₃ g'
  have h := h₁.trans h₂.symm
  simp only [toLeftCoset_apply, QuotientGroup.eq] at h ⊢
  simpa [mul_assoc] using h

variable (H₁ g H₂)

/-- tbd -/
@[mk_iff] class IsHeckeTriple : Prop where
  hasFiniteDecompQuotient : (((ConjAct.toConjAct g) • H₂)).IsFiniteRelIndex H₁

lemma isHeckeTriple_iff' :
    IsHeckeTriple H₁ g H₂ ↔ (((ConjAct.toConjAct g) • H₂)).relIndex H₁ ≠ 0 := by
  simp [isHeckeTriple_iff, Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]

instance [h : IsHeckeTriple H₁ g H₂] : Fintype (DecompQuotient H₁ g H₂) := by
  have := h.hasFiniteDecompQuotient
  exact Subgroup.fintypeOfIndexNeZero Subgroup.relIndex_ne_zero

instance instIsHeckeTriple_diag_one (H : Subgroup G) : IsHeckeTriple H 1 H := ⟨⟨by simp⟩⟩

instance instIsHeckeTriple_mulLeft [IsHeckeTriple H₁ g H₂] (h₁ : H₁) :
    IsHeckeTriple H₁ (h₁ * g) H₂ := by
  rw [isHeckeTriple_iff']
  simpa only [← DoubleCoset.conjAct_relIndex_eq H₁ H₂ g (h₁ * g) (by simp)] using
    (isHeckeTriple_iff' H₁ g H₂).mp inferInstance

instance instIsHeckeTriple_mulRight [IsHeckeTriple H₁ g H₂] (h₂ : H₂) :
    IsHeckeTriple H₁ (g * h₂) H₂ := by
  rw [isHeckeTriple_iff']
  simpa only [← DoubleCoset.conjAct_relIndex_eq H₁ H₂ g (g * h₂) (by simp)] using
    (isHeckeTriple_iff' H₁ g H₂).mp inferInstance

lemma isHeckeTriple_trans [IsHeckeTriple H₁ g H₂] [IsHeckeTriple H₂ g' H₃] :
    IsHeckeTriple H₁ (g * g') H₃ := ⟨⟨by
  have h₁₂ : ((ConjAct.toConjAct g) • H₂).relIndex H₁ ≠ 0 :=
    (isHeckeTriple_iff' H₁ g H₂).mp inferInstance
  have h₂₃ : ((ConjAct.toConjAct g) • ((ConjAct.toConjAct g') • H₃)).relIndex
      ((ConjAct.toConjAct g) • H₂) ≠ 0 := by
    simpa [Subgroup.relIndex_pointwise_smul] using (isHeckeTriple_iff' H₂ g' H₃).mp inferInstance
  simpa [mul_smul] using Subgroup.relIndex_ne_zero_trans h₂₃ h₁₂⟩⟩

instance instIsHeckeTriple_trans [IsHeckeTriple H₁ g H₂]
    [IsHeckeTriple H₂ g' H₃] (h₂ : H₂) : IsHeckeTriple H₁ (g * h₂ * g') H₃ :=
  isHeckeTriple_trans H₁ (g * h₂) H₂ g' H₃

instance instIsHeckeTriple_diag_mul (H : Subgroup G) (g g' : G)
    [IsHeckeTriple H g H] [IsHeckeTriple H g' H] : IsHeckeTriple H (g * g') H := by
  simpa using isHeckeTriple_trans H g H g' H

/-- tbd -/
abbrev HeckeSet : Set G := Set.ofPred (fun g => IsHeckeTriple H₁ g H₂)

/-- tbd -/
abbrev HeckeSet.mk (g : G) [hg : IsHeckeTriple H₁ g H₂] : HeckeSet H₁ H₂ := ⟨g, hg⟩

instance (g : HeckeSet H₁ H₂) : IsHeckeTriple H₁ g.val H₂ := g.prop

/-- tbd -/
abbrev HeckeSet.setoid : Setoid (HeckeSet H₁ H₂) :=
  (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

/-- tbd -/
def HeckeCoset := Quotient (HeckeSet.setoid H₁ H₂)

variable {H₁ H₂} in
lemma HeckeCoset.rel_iff {x y : HeckeSet H₁ H₂} :
    HeckeSet.setoid H₁ H₂ x y ↔ ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, y = h₁ * x * h₂ := by
  change DoubleCoset.setoid _ _ x.val y.val ↔ _
  rw [DoubleCoset.rel_iff]

/-- tbd -/
def HeckeCoset.mk (x : HeckeSet H₁ H₂) :
    HeckeCoset H₁ H₂ := Quotient.mk (HeckeSet.setoid H₁ H₂) x

/-- tbd -/
def HeckeCoset.mk' (g : G) [IsHeckeTriple H₁ g H₂] :
    HeckeCoset H₁ H₂ := mk H₁ H₂ (HeckeSet.mk H₁ H₂ g)

lemma HeckeCoset.mk_mk (g : G) [IsHeckeTriple H₁ g H₂] :
    mk H₁ H₂ (HeckeSet.mk H₁ H₂ g) = mk' H₁ H₂ g := rfl

@[simp]
lemma HeckeCoset.quotientMk_eq_mk (x : HeckeSet H₁ H₂) :
    ⟦x⟧ = mk H₁ H₂ x := rfl

variable {H₁ H₂ H₃}

/-- tbd -/
abbrev HeckeCoset.rep (x : HeckeCoset H₁ H₂) : HeckeSet H₁ H₂ := x.out

@[simp]
lemma HeckeCoset.mk_rep (x : HeckeCoset H₁ H₂) : mk H₁ H₂ x.rep = x := Quotient.out_eq' x

lemma HeckeCoset.mk_eq_iff {x y : HeckeSet H₁ H₂} :
    mk H₁ H₂ x = mk H₁ H₂ y ↔ ∃ (h₁ : H₁) (h₂ : H₂), y.val = h₁ * x.val * h₂ := by
  have : mk H₁ H₂ x = mk H₁ H₂ y ↔ HeckeSet.setoid H₁ H₂ x y := Quotient.eq
  rw [this, HeckeCoset.rel_iff]
  simp

lemma HeckeCoset.mk_eq_iff' {x y : HeckeSet H₁ H₂} :
    mk H₁ H₂ x = mk H₁ H₂ y ↔ DoubleCoset.mk H₁ H₂ x.val = DoubleCoset.mk H₁ H₂ y.val := by
  simp [HeckeCoset.mk_eq_iff, DoubleCoset.eq]

lemma HeckeCoset.rep_leftCoset_ne_if_ne {x y : HeckeCoset H₁ H₂} (hxy : x ≠ y) (h₁ : H₁) :
    (QuotientGroup.mk (h₁ * x.rep.val) : G ⧸ H₂) ≠ (y.rep.val : G ⧸ H₂) := by
  intro h
  apply hxy
  rw [← HeckeCoset.mk_rep x, ← HeckeCoset.mk_rep y, HeckeCoset.mk_eq_iff.mpr]
  exact ⟨h₁, ⟨((h₁ : G) * x.rep)⁻¹ * y.rep, QuotientGroup.eq.mp h⟩, by simp [mul_assoc]⟩

lemma HeckeCoset.rep_mk_leftCoset.injective :
    Function.Injective (fun x : HeckeCoset H₁ H₂ => (x.rep : G ⧸ H₂)) := by
  intro x y h
  rw [← HeckeCoset.mk_rep x, ← HeckeCoset.mk_rep y]
  exact Quotient.sound <| DoubleCoset.rel_iff.mpr
    ⟨1, by simp, _, QuotientGroup.leftRel_apply.mp (Quotient.exact h), by simp⟩

/-- tbd -/
def HeckeCoset.degree (x : HeckeCoset H₁ H₂) :
    ℕ := (ConjAct.toConjAct x.rep.val • H₂).relIndex H₁

lemma HeckeCoset.degree_ne_zero (x : HeckeCoset H₁ H₂) :
    x.degree ≠ 0 := by
  simpa only [degree, ← Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero] using
    IsHeckeTriple.hasFiniteDecompQuotient

@[simp]
lemma HeckeCoset.diag_one_rep_mem : (mk' H H 1).rep.val ∈ H := by
  obtain ⟨a, b, heq⟩ := HeckeCoset.mk_eq_iff.mp (show mk' H H 1 = ⟦(mk' H H 1).rep⟧ from by simp)
  simp [heq, H.mul_mem a.prop b.prop]

@[simp]
lemma HeckeCoset.diag_one_degree_eq_one : (mk' H H 1).degree = 1 := by
  have : ConjAct.toConjAct (mk' H H 1).rep.val • H = H :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer (by simp))
  simp [degree, this]

/-- tbd -/
def HeckeCoset.mulMap (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃)
    (p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃) : HeckeCoset H₁ H₃ :=
  HeckeCoset.mk' H₁ H₃ (p.1.out * x.rep.val * p.2.out * y.rep)

/-- tbd -/
def DoubleCoset.multiplicity (Γ₁ Γ₂ Γ₃ : Subgroup G) (g h d : G) : ℕ :=
  Nat.card {p : DecompQuotient Γ₁ g Γ₂ × DecompQuotient Γ₂ h Γ₃ |
    ((p.1.out : G) * g * ((p.2.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)}

lemma HeckeCoset.mulMap_eq_of_mk_eq (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃)
    (z : HeckeCoset H₁ H₃) {p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃}
    (h : ((p.1.out * x.rep.val * ((p.2.out : G) * y.rep) : G) : G ⧸ H₃) = (z.rep : G ⧸ H₃)) :
    x.mulMap y p = z := by
  rw [← HeckeCoset.mk_rep z]
  apply HeckeCoset.mk_eq_iff.mpr
  exact ⟨1,⟨((p.1.out * x.rep.val * p.2.out * y.rep)⁻¹ * z.rep), by
    simpa [mul_assoc] using QuotientGroup.eq.mp h⟩, by simp [mul_assoc]⟩

/-- tbd -/
def HeckeCoset.multiplicity (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃) :
    HeckeCoset H₁ H₃ →₀ ℕ :=
  Finsupp.ofSupportFinite (fun z => DoubleCoset.multiplicity H₁ H₂ H₃ x.rep y.rep z.rep) <| by
    classical
    refine (Finset.univ.image (x.mulMap y)).finite_toSet.subset ?_
    intro z hz
    simp only [Function.mem_support, DoubleCoset.multiplicity, Nat.card_ne_zero] at hz
    obtain ⟨⟨p, hp⟩, _⟩ := hz
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, mulMap_eq_of_mk_eq x y z hp⟩

lemma HeckeCoset.multiplicity_apply (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃)
    (z : HeckeCoset H₁ H₃) :
    x.multiplicity y z =
      Nat.card {p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃ |
        (p.1.out * x.rep.val * (p.2.out * y.rep.val) : G ⧸ H₃) = (z.rep : G ⧸ H₃)} := rfl

/-- tbd -/
def HeckeCosetVector : HeckeCoset H₁ H₂ → IndV H₂.subtype (trivial k H₂ k) :=
  fun x => ∑ i, cosetVector k (DecompQuotient.toLeftCoset H₁ x.rep H₂ i)

lemma HeckeCosetVector_eq_sum (x : HeckeCoset H₁ H₂) :
    HeckeCosetVector k x =
      ∑ (i : DecompQuotient H₁ x.rep H₂), cosetVectorMk k (i.out * x.rep.val) H₂ := by
  simp [HeckeCosetVector]

lemma HeckeCosetVector_isInvariant (x : HeckeCoset H₁ H₂) (h₁ : H₁) :
    ind H₂.subtype (trivial k H₂ k) h₁ (HeckeCosetVector k x) = HeckeCosetVector k x := by
  simp only [HeckeCosetVector, DecompQuotient.toLeftCoset_apply, map_sum, ind_apply_cosetVector]
  exact Fintype.sum_equiv (MulAction.toPerm h₁) _ _ fun y => by
    congr 1
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc]
    simp only [← Subgroup.coe_mul, ← DecompQuotient.mk_eq_iff]
    simp [← MulAction.Quotient.mk_smul_out]

variable {k} in
/-- tbd -/
def HeckeCoset.mk₁ (x : HeckeCoset H₁ H₂) : HeckeBimodule₁ k H₁ H₂ :=
  HeckeModule₁.invariantsMk H₁ _ ⟨HeckeCosetVector k x, HeckeCosetVector_isInvariant k x⟩

@[simp]
lemma HeckeCoset.mk₁_apply (x : HeckeCoset H₁ H₂) :
    x.mk₁ (cosetVectorMk k 1 H₁) = HeckeCosetVector k x := by
  simp [mk₁]

end HeckeTriple

section bimodule₁

namespace HeckeBimodule₁

variable {H₁ H₂ k}

/-- tbd -/
@[simps]
def toLeftCosetModule : HeckeBimodule₁ k H₁ H₂ →ₗ[k] k[G ⧸ H₂] where
  toFun f := indTrivialToOfMulActionMap k H₂ (f (cosetVectorMk k 1 H₁))
  map_add' := by simp
  map_smul' := by simp

lemma toLeftCosetModule_isInvariant (f : HeckeBimodule₁ k H₁ H₂) (h₁ : H₁) :
    ofMulAction k G (G ⧸ H₂) h₁ f.toLeftCosetModule = f.toLeftCosetModule := by
  simp [← IntertwiningMap.isIntertwining]

lemma toLeftCosetModule.coeff_isInvariant (f : HeckeBimodule₁ k H₁ H₂) (h₁ : H₁) (x : G ⧸ H₂) :
    f.toLeftCosetModule.coeff ((h₁ : G) • x) = f.toLeftCosetModule.coeff x := by
  simpa using congrArg (fun w => w.coeff ((h₁ : G) • x)) (toLeftCosetModule_isInvariant f h₁).symm

lemma isHeckeTriple_of_coeff_ne_zero (f : HeckeBimodule₁ k H₁ H₂) (y : G)
    (hy : f.toLeftCosetModule.coeff (y : G ⧸ H₂) ≠ 0) : IsHeckeTriple H₁ y H₂ := by
  have : Finite (DecompQuotient H₁ y H₂) :=
    Finite.of_injective (β := f.toLeftCosetModule.coeff.support)
      (fun z => ⟨DecompQuotient.toLeftCoset H₁ y H₂ z, by
        simpa using (toLeftCosetModule.coeff_isInvariant f _ _).trans_ne hy⟩)
      fun _ _ h => DecompQuotient.toLeftCoset.injective H₁ H₂ y (congrArg Subtype.val h)
  exact ⟨Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr Subgroup.finiteIndex_of_finite_quotient⟩

variable (k H₁ H₂)

/-- tbd -/
def toHeckeCosetModuleMap :
    HeckeBimodule₁ k H₁ H₂ →ₗ[k] k[HeckeCoset H₁ H₂] where
  toFun f := comapDomain (fun x => (x.rep.val : G ⧸ H₂)) (HeckeCoset.rep_mk_leftCoset.injective)
    (f.toLeftCosetModule)
  map_add' := by simp [HeckeBimodule₁.toLeftCosetModule]
  map_smul' _ _ := by ext; simp [HeckeBimodule₁.toLeftCosetModule]

@[simp]
lemma toHeckeCosetModuleMap_apply_mk₁ (x : HeckeCoset H₁ H₂) :
    (toHeckeCosetModuleMap k H₁ H₂) x.mk₁ = single x 1
  := by classical
  ext y
  simp only [toHeckeCosetModuleMap, toLeftCosetModule_apply, LinearMap.coe_mk, AddHom.coe_mk,
    HeckeCoset.mk₁_apply, coeff_comapDomain, Finsupp.comapDomain_apply, coeff_single]
  simp only [HeckeCosetVector_eq_sum, map_sum, indTrivialToOfMulActionMap_apply_cosetVectorMk,
    coeff_sum, coeff_single, Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases hxy : x = y
  · simp [← hxy, Finsupp.single_apply, ← DecompQuotient.eq_one_iff]
  · simp [hxy, HeckeCoset.rep_leftCoset_ne_if_ne]

lemma toHeckeCosetModuleMap.coeff_eq_coeff (f : HeckeBimodule₁ k H₁ H₂)
    (x : HeckeCoset H₁ H₂) :
    (toHeckeCosetModuleMap k H₁ H₂ f).coeff x = f.toLeftCosetModule.coeff x.rep := by
  simp [toHeckeCosetModuleMap]

/-- tbd -/
def toHeckeCosetModuleInv :
    k[HeckeCoset H₁ H₂] →ₗ[k] HeckeBimodule₁ k H₁ H₂ :=
  (MonoidAlgebra.basis (HeckeCoset H₁ H₂) k).constr k fun x => x.mk₁

@[simp]
lemma toHeckeCosetModuleInv_apply_single (x : HeckeCoset H₁ H₂) :
    ((toHeckeCosetModuleInv k H₁ H₂) (single x 1)) = x.mk₁ := by
  simp [toHeckeCosetModuleInv, ← MonoidAlgebra.basis_apply]

lemma toHeckeCosetModuleInv.isRightInv (x : k[HeckeCoset H₁ H₂]) :
    toHeckeCosetModuleMap k H₁ H₂ (toHeckeCosetModuleInv k H₁ H₂ x) = x :=
  induction_linear x (by simp) (fun _ _ h h' => by nth_rw 2 [← h, ← h']; simp) <| by
    intro _ r
    rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul]
    simp

lemma toHeckeCosetModuleMap.injective :
    Function.Injective (toHeckeCosetModuleMap k H₁ H₂) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext
  apply (indTrivialOfMulActionEquiv k H₂).injective
  ext y
  change f.toLeftCosetModule.coeff y = 0
  by_contra! hy
  apply hy
  have : IsHeckeTriple H₁ y.out H₂ := isHeckeTriple_of_coeff_ne_zero f y.out (by simpa using hy)
  obtain ⟨h₁, h₂, heq⟩ := HeckeCoset.mk_eq_iff.mp
    (show HeckeCoset.mk H₁ H₂ ((HeckeCoset.mk' H₁ H₂ y.out).rep) = ⟦(HeckeSet.mk H₁ H₂ y.out)⟧
      from by simp [HeckeCoset.mk_mk])
  have : y = ((HeckeSet.mk H₁ H₂ y.out : G) : G ⧸ H₂) := by simp
  rw [this, heq, QuotientGroup.mk_mul_of_mem _ h₂.prop]
  simp only [← smul_eq_mul, ← MulAction.Quotient.smul_mk, toLeftCosetModule.coeff_isInvariant]
  simpa [toHeckeCosetModuleMap.coeff_eq_coeff] using
    congrArg (fun f => f.coeff (HeckeCoset.mk' H₁ H₂ y.out)) hf

/-- tbd -/
@[simps!]
def toHeckeCosetModuleEquiv :
    HeckeBimodule₁ k H₁ H₂ ≃ₗ[k] k[HeckeCoset H₁ H₂] where
  toLinearMap := toHeckeCosetModuleMap k H₁ H₂
  invFun := toHeckeCosetModuleInv k H₁ H₂
  left_inv f := by
    apply toHeckeCosetModuleMap.injective
    simp [toHeckeCosetModuleInv.isRightInv]
  right_inv := toHeckeCosetModuleInv.isRightInv k H₁ H₂

variable {k H₁ H₂} in
lemma induction_on (f : HeckeBimodule₁ k H₁ H₂) {p : HeckeBimodule₁ k H₁ H₂ → Prop}
    (zero : p 0)
    (mk : ∀ (g : HeckeCoset H₁ H₂), p (g.mk₁))
    (smul : ∀ (r : k) (x : HeckeBimodule₁ k H₁ H₂), p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) : p f := by
  let E := toHeckeCosetModuleEquiv k H₁ H₂
  rw [← E.symm_apply_apply f]
  refine MonoidAlgebra.induction_linear (E f) ?_ ?_ ?_
  · simp [zero]
  · intro x y hx hy
    simpa using add (E.symm x) (E.symm y) hx hy
  · intro g r
    rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul]
    simpa [E] using smul r g.mk₁ (mk g)

end HeckeBimodule₁

end bimodule₁

section HeckeAction

variable {k H₁ H₂ ρ} in
/-- tbd -/
def HeckeAction : HeckeBimodule₁ k H₁ H₂ →ₗ[k] HeckeModule₁ H₂ ρ →ₗ[k] HeckeModule₁ H₁ ρ :=
  (IntertwiningMap.llcomp (ind H₁.subtype _) (ind H₂.subtype _) ρ).flip

lemma HeckeAction_eq_comp (x : HeckeBimodule₁ k H₁ H₂) (v : HeckeModule₁ H₂ ρ) :
    HeckeAction x v = v.comp x := by
  rw [HeckeAction, LinearMap.flip_apply, IntertwiningMap.comp_def]

lemma HeckeAction_assoc (x : HeckeBimodule₁ k H₁ H₂) (y : HeckeBimodule₁ k H₂ H₃)
    (v : HeckeModule₁ H₃ ρ) :
    HeckeAction (HeckeAction x y) v = HeckeAction x (HeckeAction y v) := by
  ext
  simp [HeckeAction_eq_comp]

lemma HeckeAction_comp_eq (x : HeckeBimodule₁ k H₁ H₂) (y : HeckeBimodule₁ k H₂ H₃) :
    HeckeAction (y.comp x) (ρ := ρ) = HeckeAction (HeckeAction x y) := by
  ext
  simp [HeckeAction_eq_comp]

lemma HeckeAction.diag_mul_eq (x y : HeckeAlgebra₁Unop k H) :
    HeckeAction (y * x) (k := k) (ρ := ρ) = (HeckeAction x) * (HeckeAction y) := by
  rw [HeckeAction]
  rfl

lemma HeckeAction_mk₁_apply (x : HeckeCoset H₁ H₂) (v : HeckeModule₁ H₂ ρ) :
    HeckeAction x.mk₁ v (cosetVectorMk k 1 H₁) =
      ∑ (i : DecompQuotient H₁ x.rep H₂), ρ (i.out * x.rep) (v (cosetVectorMk k 1 H₂)) := by
  simp only [HeckeAction_eq_comp, IntertwiningMap.comp_apply, HeckeCoset.mk₁_apply, map_mul,
    Module.End.mul_apply]
  simp [HeckeCosetVector, ← IntertwiningMap.isIntertwining]

variable {H₁ H₂ H₃}

lemma HeckeAction_mk₁_mk₁_coeff (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃)
    (z : HeckeCoset H₁ H₃) :
    (HeckeBimodule₁.toLeftCosetModule (HeckeAction x.mk₁ y.mk₁)).coeff (z.rep : G ⧸ H₃)
      = (x.multiplicity y z : k) := by classical
  have : HeckeAction x.mk₁ y.mk₁ (cosetVectorMk k 1 H₁) =
      ∑ (p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃),
        cosetVectorMk k (p.1.out * x.rep.val * p.2.out * y.rep) H₃ := by
    simp only [HeckeAction_mk₁_apply, map_mul, HeckeCoset.mk₁_apply, Module.End.mul_apply,
      HeckeCosetVector_eq_sum, map_sum, ind_apply_cosetVectorMk]
    simp [← Fintype.sum_prod_type', mul_assoc]
  simp [this, Finsupp.single_apply, HeckeCoset.multiplicity_apply, mul_assoc]

theorem HeckeAction_mk₁_mk₁ (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃) :
    HeckeAction x.mk₁ y.mk₁ = (x.multiplicity y).sum fun w n => n • w.mk₁
    (k := k) := by classical
  apply HeckeBimodule₁.toHeckeCosetModuleMap.injective
  ext z
  rw [HeckeBimodule₁.toHeckeCosetModuleMap.coeff_eq_coeff, HeckeAction_mk₁_mk₁_coeff]
  simpa [map_finsuppSum, Finsupp.single_apply] using fun h => by simp [h]

end HeckeAction

variable {k H}

section HeckeAlgebra₁

variable (f : HeckeAlgebra₁ k H) (ρ : Representation k G V)

lemma HeckeAlgebra₁.smul_eq_HeckeAction (v : HeckeModule₁ H ρ) :
    f • v = HeckeAction f.unop v := rfl

lemma HeckeAlgebra₁.smul_eq_comp (v : HeckeModule₁ H ρ) :
    f • v = v.comp f.unop := rfl

lemma HeckeAlgebra₁.smul_eq_mul (g : HeckeAlgebra₁ k H) :
    f • g = f * g := rfl

lemma HeckeAlgebra₁.mul_unop_eq_comp (g : HeckeAlgebra₁ k H) :
    (f * g).unop = g.unop.comp f.unop := rfl

lemma HeckeAlgebra₁.mul_eq_HeckeAction (g : HeckeAlgebra₁ k H) :
    f * g = MulOpposite.op (HeckeAction f.unop g.unop) := by
  rw [← MulOpposite.unop_inj]
  rfl

/-- tbd -/
def HeckeCoset.diagMk₁ (x : HeckeCoset H H) :
    HeckeAlgebra₁ k H := MulOpposite.opLinearEquiv k x.mk₁

@[simp]
lemma HeckeCoset.unop_diagMk₁ (x : HeckeCoset H H) :
    MulOpposite.unop x.diagMk₁ = x.mk₁ (k := k) :=
  rfl

lemma HeckeAlgebra₁.diagMk₁_mul_diagMk₁ (x y : HeckeCoset H H) :
    x.diagMk₁ * y.diagMk₁ (k := k) = (x.multiplicity y).sum fun w n => n • w.diagMk₁ := by
  simp only [HeckeAlgebra₁.mul_eq_HeckeAction, HeckeCoset.diagMk₁, ← Nat.cast_smul_eq_nsmul k,
    ← (MulOpposite.opLinearEquiv k).map_smul, ← map_finsuppSum]
  simp [HeckeAction_mk₁_mk₁, Nat.cast_smul_eq_nsmul k]

lemma HeckeCoset.diagMk₁_one :
    (mk' H H 1).diagMk₁ (k := k) = 1 := by
  simp only [diagMk₁, MulOpposite.coe_opLinearEquiv, MulOpposite.op_eq_one_iff]
  ext
  have : Fintype.card (DecompQuotient H (mk' H H 1).rep H) = 1 := by
    simpa [degree, Subgroup.relIndex, Subgroup.index] using diag_one_degree_eq_one (H := H)
  simp [HeckeCosetVector_eq_sum, this]

/-- tbd -/
@[simps! symm_apply]
def HeckeAlgebra₁.toHeckeCosetModuleEquiv :
    HeckeAlgebra₁ k H ≃ₗ[k] k[HeckeCoset H H] :=
  (MulOpposite.opLinearEquiv k).symm.trans (HeckeBimodule₁.toHeckeCosetModuleEquiv k H H)

@[simp]
lemma HeckeAlgebra₁.toHeckeCosetModuleEquiv_apply (x : HeckeCoset H H) :
    toHeckeCosetModuleEquiv x.diagMk₁ = single x (1 : k) := by
  apply HeckeAlgebra₁.toHeckeCosetModuleEquiv.symm.injective
  simp [HeckeCoset.diagMk₁]

/-- tbd -/
def HeckeAlgebra₁.coeff :
    HeckeAlgebra₁ k H →ₗ[k] (HeckeCoset H H →₀ k) :=
  MonoidAlgebra.coeffLinearEquiv (S := k) (R := k) (M := HeckeCoset H H) ∘ₗ
    HeckeAlgebra₁.toHeckeCosetModuleEquiv.toLinearMap

@[simp]
lemma HeckeAlgebra₁.coeff_apply (x y : HeckeCoset H H) [DecidableEq (HeckeCoset H H)] :
    x.diagMk₁.coeff y = if x = y then (1 : k) else 0 := by
  simp [coeff, HeckeAlgebra₁.toHeckeCosetModuleEquiv_apply, Finsupp.single_apply]

@[ext]
lemma HeckeAlgebra₁.ext (f g : HeckeAlgebra₁ k H) (h : ∀ x, f.coeff x = g.coeff x) :
    f = g := by
  apply HeckeAlgebra₁.toHeckeCosetModuleEquiv.injective
  ext x
  exact h x

lemma HeckeAlgebra₁.induction_on {p : HeckeAlgebra₁ k H → Prop}
    (mk : ∀ x : HeckeCoset H H, p (x.diagMk₁))
    (smul : ∀ (r : k) x , p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) :
    p f := by
  change p (MulOpposite.op f.unop)
  refine HeckeBimodule₁.induction_on f.unop (p := fun x => p (MulOpposite.op x)) ?_ ?_ ?_ ?_
  · simpa using smul 0 (HeckeCoset.mk' H H 1).diagMk₁ (mk (HeckeCoset.mk' H H 1))
  · exact fun x => by simpa [HeckeCoset.diagMk₁] using mk x
  · exact fun r x hx => by simpa using smul r (MulOpposite.op x) hx
  · exact fun x y hx hy => by simpa using add (MulOpposite.op x) (MulOpposite.op y) hx hy

end HeckeAlgebra₁

section unimodular

/-- tbd -/
class IsHeckeUnimodular (H : Subgroup G) : Prop where
  relIndex_eq_inv : ∀ (g : HeckeSet H H),
    (ConjAct.toConjAct g.val • H).relIndex H = (ConjAct.toConjAct g.val⁻¹ • H).relIndex H

instance [IsHeckeUnimodular H] (g : G) [IsHeckeTriple H g H] :
    IsHeckeTriple H g⁻¹ H := by
  rw [isHeckeTriple_iff', ← IsHeckeUnimodular.relIndex_eq_inv (g := HeckeSet.mk H H g)]
  exact (isHeckeTriple_iff' H g H).mp inferInstance

/-- tbd -/
abbrev HeckeSet.inv (x : HeckeSet H H) [IsHeckeTriple H x⁻¹ H] :
    HeckeSet H H := HeckeSet.mk H H (x : G)⁻¹

variable [IsHeckeUnimodular H]

/-- tbd -/
def HeckeCoset.inv (x : HeckeCoset H H) :
    HeckeCoset H H :=
  Quotient.liftOn x (fun x ↦ (mk H H (HeckeSet.inv x))) fun x y hxy => by
    apply Quotient.sound
    simp only [HeckeCoset.rel_iff] at hxy ⊢
    obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hxy
    exact ⟨h₂⁻¹, H.inv_mem hh₂, h₁⁻¹, H.inv_mem hh₁, by simp [heq, mul_assoc]⟩

lemma HeckeCoset.mk_inv_eq (x : HeckeSet H H) :
    mk H H (HeckeSet.inv x) = (mk H H x).inv := by
  rfl

lemma HeckeCoset.inv_eq_mk_inv (x : HeckeCoset H H) :
     mk H H (HeckeSet.inv x.rep) = x.inv := by
  simp [mk_inv_eq]

@[simp]
lemma HeckeCoset.inv_inv (x : HeckeCoset H H) :
    x.inv.inv = x :=
  Quotient.inductionOn x fun x => by
    simp [← mk_inv_eq, HeckeSet.inv, _root_.inv_inv]

lemma HeckeCoset.inv_eq_iff {x y : HeckeCoset H H} :
    x.inv = y ↔ x = y.inv := by
  constructor
  · exact fun h => by rw [h.symm]; simp
  · exact fun h => by rw [h]; simp

@[simp]
lemma HeckeCoset.inv_degree_eq_degree (x : HeckeCoset H H) :
    x.inv.degree = x.degree := by
  simp only [HeckeCoset.degree, IsHeckeUnimodular.relIndex_eq_inv (g := x.rep), eq_comm]
  apply DoubleCoset.conjAct_relIndex_eq _ (y := x.inv.rep.val)
  simpa [← HeckeCoset.mk_eq_iff' (x := HeckeSet.mk H H (x.rep : G)⁻¹)] using inv_eq_mk_inv x

@[simp]
lemma HeckeCoset.diag_one_inv_eq_self :
    (mk' H H 1).inv = (mk' H H 1) := by
  simp [← mk_mk, ← mk_inv_eq, HeckeSet.inv]

lemma HeckeCoset.multiplicity_self_inv_one_eq_degree (x : HeckeCoset H H) :
    x.multiplicity x.inv (mk' H H 1) = x.degree := by classical
  simp only  [multiplicity_apply, degree]
  obtain ⟨h₁, h₂, hinv⟩ := mk_eq_iff.mp
    (show mk H H (HeckeSet.inv x.rep) = mk H H x.inv.rep by simp [mk_inv_eq])
  let j : DecompQuotient H x.inv.rep H := QuotientGroup.mk h₁⁻¹
  -- The pain is due to the absence of a "independence of representatives" lemma for `multiplicity`.
  have hj :
    ((j.out * x.inv.rep : G) : G ⧸ H) = ((x.rep⁻¹ : G) : G ⧸ H) := by
    calc
      _ = ((h₁⁻¹ * x.inv.rep : G) : G ⧸ H):= by
        rw [← DecompQuotient.mk_eq_iff]; simp [j]
      _ = _ := by
        simp [hinv, mul_assoc]
  have heq (i : DecompQuotient H x.rep H) :
      (QuotientGroup.mk (i.out * x.rep * (j.out * x.inv.rep)) : G ⧸ H)
        = (QuotientGroup.mk (mk' H H 1).rep : G ⧸ H) := by
    calc
      _ = (i.out : G ⧸ H) := by
        simpa [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc] using
          congrArg (fun q : G ⧸ H => (i.out * x.rep : G) • q) hj
      _ = _ := by
        simpa [QuotientGroup.eq (a := i.out.val)] using H.mul_mem (H.inv_mem i.out.prop) (by simp)
  let equiv :
      {p : DecompQuotient H x.rep H × DecompQuotient H x.inv.rep H |
        ((p.1.out * x.rep * (p.2.out * x.inv.rep) : G) :  G ⧸ H)= ((mk' H H 1).rep.val : G ⧸ H)}
      ≃ DecompQuotient H x.rep H :=
    { toFun p := p.1.1
      invFun i := ⟨(i, j), heq i⟩
      left_inv p := Subtype.ext (Prod.ext rfl (DecompQuotient.snd_eq_of_fst_eq (heq p.1.1) p.prop))
      right_inv _ := rfl}
  simpa [Subgroup.relIndex, Subgroup.index] using Nat.card_congr equiv

lemma HeckeCoset.multiplicity_self_ne_inv_one_eq_zero {x y : HeckeCoset H H} (h : y ≠ x.inv) :
    x.multiplicity y (mk' H H 1) = 0 := by
  simp only [multiplicity_apply]
  by_contra hne
  obtain ⟨p, hp⟩ := (Nat.card_ne_zero.mp hne).left
  simp only [Set.mem_ofPred_eq, ← mul_assoc, QuotientGroup.eq, mul_inv_rev] at hp
  have heq : y = x.inv := by
    rw [← HeckeCoset.mk_rep y, ← inv_eq_mk_inv]
    apply mk_eq_iff.mpr
    have : y.rep.val⁻¹ * p.2.out⁻¹ * x.rep.val⁻¹ ∈ H := by
      simpa [mul_assoc] using
        H.mul_mem hp (H.mul_mem (H.inv_mem (HeckeCoset.diag_one_rep_mem H)) p.1.out.prop)
    use ⟨p.2.out, p.2.out.prop⟩, ⟨(y.rep.val⁻¹ * p.2.out⁻¹ * x.rep.val⁻¹), this⟩
    simp [mul_assoc]
  exact h heq

@[simp]
lemma HeckeCoset.multiplicity_apply_one [DecidableEq (HeckeCoset H H)] {x y : HeckeCoset H H} :
    x.multiplicity y (mk' H H 1) = if y = x.inv then (x.degree : k) else 0 := by
  by_cases h : y = x.inv
  · simp [h, HeckeCoset.multiplicity_self_inv_one_eq_degree]
  · simp [h, HeckeCoset.multiplicity_self_ne_inv_one_eq_zero]

end unimodular

section coeff₁

variable {ρ : Representation k G V} (f : HeckeAlgebra₁ k H)

open MonoidAlgebra

/-- tbd -/
abbrev HeckeAlgebra₁.coeff₁ : k := f.coeff (HeckeCoset.mk' H H 1)

lemma HeckeAlgebra₁.coeff_diagMk₁_mul_diagMk₁ {x y z : HeckeCoset H H} :
    (x.diagMk₁ * y.diagMk₁).coeff z = (x.multiplicity y z : k) := by classical
  simp only [diagMk₁_mul_diagMk₁, coeff, map_finsuppSum, ← Nat.cast_smul_eq_nsmul k, map_smul]
  simpa [Finsupp.single_apply] using fun h => by simp [h]

lemma HeckeAlgebra₁.coeff₁_diagMk₁_mul_diagMk₁ {x y : HeckeCoset H H} :
    (x.diagMk₁ * y.diagMk₁).coeff₁ = (x.multiplicity y (HeckeCoset.mk' H H 1) : k) := by
  simp [coeff₁, HeckeAlgebra₁.coeff_diagMk₁_mul_diagMk₁]

lemma HeckeAlgebra₁.coeff₁_mul_diagMk₁ [IsHeckeUnimodular H] (f : HeckeAlgebra₁ k H)
    (x : HeckeCoset H H) :
    (f * x.diagMk₁).coeff₁ = x.degree • f.coeff x.inv := by classical
  apply HeckeAlgebra₁.induction_on f
  · intro y
    simp only [coeff₁_diagMk₁_mul_diagMk₁, HeckeCoset.multiplicity_apply_one, coeff_apply, smul_ite,
      nsmul_eq_mul, mul_one]
    by_cases h : y = x.inv
    · simp [h]
    · simp only [← HeckeCoset.inv_eq_iff, h, ↓reduceIte, mul_zero, ite_eq_right_iff]
      exact fun h' => by simpa using h h'.symm
  · exact fun _ _ hx => by simp [coeff₁, hx, ← mul_assoc, mul_comm]
  · exact fun _ _ hx hy => by simp [coeff₁, add_mul, hx, hy]

theorem HeckeAlgebra₁.coeff₁_isSymmetric {x y : HeckeAlgebra₁ k H} [IsHeckeUnimodular H] :
    (x * y).coeff₁ = (y * x).coeff₁ := by classical
  apply HeckeAlgebra₁.induction_on x
  · intro x
    apply HeckeAlgebra₁.induction_on y
    · intro y
      simp only [coeff₁, diagMk₁_mul_diagMk₁, ← Nat.cast_smul_eq_nsmul k, map_finsuppSum, map_smul,
        Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply, coeff_apply, _root_.smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq,
        HeckeCoset.multiplicity_apply_one, ite_not]
      by_cases h : y = x.inv
      · have : x = y.inv := by simp [h]
        rw [h, HeckeCoset.multiplicity_self_inv_one_eq_degree]
        simp [this, HeckeCoset.multiplicity_self_inv_one_eq_degree, HeckeCoset.degree_ne_zero]
      · have : x ≠ y.inv := by
          by_contra heq
          exact h (HeckeCoset.inv_eq_iff.mpr heq).symm
        simp [h, this]
    · exact fun _ _ hx => by simp [coeff₁, hx]
    · exact fun _ _ hx hy => by simp [coeff₁, mul_add, add_mul, hx, hy]
  · exact fun _ _ hx => by simp [coeff₁, hx]
  · exact fun _ _ hx hy => by simp [coeff₁, mul_add, add_mul, hx, hy]

end coeff₁

section invertible

variable (k) in
/-- tbd -/
class IsHeckeInvertible (H : Subgroup G) where
  degreeInv : HeckeCoset H H → k
  degreeInv_mul_cancel : ∀ x, degreeInv x * x.degree = 1

variable (k) in
/-- tbd -/
def HeckeCoset.degreeInv [IsHeckeInvertible k H] (x : HeckeCoset H H) :
    k := (IsHeckeInvertible.degreeInv x)

@[simp]
lemma HeckeCoset.degreeInv_mul_cancel [IsHeckeInvertible k H] (x : HeckeCoset H H) :
    x.degreeInv k * x.degree = 1 :=
  IsHeckeInvertible.degreeInv_mul_cancel x

@[simp]
lemma HeckeCoset.mul_degreeInv_cancel [IsHeckeInvertible k H] (x : HeckeCoset H H) :
    x.degree * x.degreeInv k = 1 := by
  simpa [mul_comm] using degreeInv_mul_cancel x (k := k)

@[simp]
lemma HeckeCoset.inv_degreeInv [IsHeckeInvertible k H] [IsHeckeUnimodular H] (x : HeckeCoset H H) :
    x.inv.degreeInv k = x.degreeInv k := by
  calc
    _ = x.inv.degreeInv k * x.inv.degree * x.degreeInv k := by
      simp [mul_assoc]
    _ = x.degreeInv k := by
      rw [HeckeCoset.degreeInv_mul_cancel, one_mul]

instance {k : Type*} [Field k] [CharZero k] : IsHeckeInvertible k H where
  degreeInv x := (x.degree : k)⁻¹
  degreeInv_mul_cancel _ := by simp [HeckeCoset.degree_ne_zero]

theorem HeckeAlgebra₁.coeff₁_isNondegenerate [IsHeckeUnimodular H] [IsHeckeInvertible k H]
    {x y : HeckeAlgebra₁ k H}
    (hxy : ∀ z : HeckeCoset H H, (x * z.diagMk₁).coeff₁ = (y * z.diagMk₁).coeff₁) :
    x = y := by
  apply sub_eq_zero.mp
  ext z
  simpa [sub_eq_zero, coeff₁_mul_diagMk₁, ← mul_assoc]
    using congrArg (fun x => z.degreeInv k • x) (hxy z.inv)

end invertible

section trace

/-- tbd -/
def HeckeAlgebra₁.trace (ρ : Representation k G V)
    : HeckeAlgebra₁ k H →ₗ[k] k :=
  LinearMap.trace k (HeckeModule₁ H ρ) ∘ₗ HeckeAction ∘ₗ
    (MulOpposite.opLinearEquiv _).symm.toLinearMap

lemma HeckeAlgebra.trace_apply (ρ : Representation k G V) (f : HeckeAlgebra₁ k H) :
    f.trace ρ = LinearMap.trace k (HeckeModule₁ H ρ) (HeckeAction f.unop) := rfl

lemma HeckeAlgebra₁.trace_comm (x y : HeckeAlgebra₁ k H) (ρ : Representation k G V) :
    (x * y).trace ρ = (y * x).trace ρ := by
  simp only [trace, LinearMap.coe_comp, LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv_symm,
    Function.comp_apply, MulOpposite.unop_mul, HeckeAction.diag_mul_eq]
  rw [LinearMap.trace_mul_comm]

variable {k : Type*} [CommRing k] [IsHeckeInvertible k H]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (f : HeckeAlgebra₁ k H) (ρ : Representation k G V)

variable (H) in
/-- tbd -/
abbrev HeckeCoset.trace_average :
    HeckeCoset H H → k := fun x => x.degreeInv k * x.diagMk₁.trace ρ

variable (H) in
/-- tbd -/
class IsRelCompact [Module.Finite k (HeckeModule₁ H ρ)] : Prop where
  hasFiniteSupport : (HeckeCoset.trace_average H ρ (k := k)).HasFiniteSupport

variable [Module.Finite k (HeckeModule₁ H ρ)] [ρ.IsRelCompact H]

/-- tbd -/
def HeckeAlgebra₁.traceFinsupp :
    HeckeCoset H H →₀ k :=
  Finsupp.ofSupportFinite (HeckeCoset.trace_average H ρ) (IsRelCompact.hasFiniteSupport)

@[simp]
lemma HeckeAlgebra₁.traceFinsupp_apply (x : HeckeCoset H H) :
    traceFinsupp ρ x = x.degreeInv k * x.diagMk₁.trace ρ := rfl

variable [IsHeckeUnimodular H]

/-- tbd -/
def HeckeAlgebra₁.traceMk : HeckeAlgebra₁ k H :=
    (traceFinsupp ρ).sum fun x r => r • x.inv.diagMk₁

lemma HeckeAlgebra₁.traceMk_coeff (x : HeckeCoset H H) :
    (traceMk ρ).coeff x = x.degreeInv k * x.inv.diagMk₁.trace ρ := by classical
  rw [HeckeAlgebra₁.traceMk, coeff, map_finsuppSum, eq_comm]
  simp [Finsupp.single_apply, HeckeCoset.inv_eq_iff]

lemma HeckeAlgebra₁.coeff₁_traceMk_mul (f : HeckeAlgebra₁ k H) :
    (traceMk ρ * f).coeff₁ = f.trace ρ := by
  apply HeckeAlgebra₁.induction_on f
  · intro x
    simp [coeff₁_mul_diagMk₁, traceMk_coeff, ← mul_assoc]
  · exact fun _ _ hx => by simp [coeff₁, hx]
  · exact fun _ _ hx hy => by simp [coeff₁, mul_add, hx, hy]

lemma HeckeAlgebra₁.traceMk_isCentral (f : HeckeAlgebra₁ k H) :
    traceMk ρ * f = f * traceMk ρ := by
  apply HeckeAlgebra₁.coeff₁_isNondegenerate
  intro z
  nth_rw 2 [mul_assoc, coeff₁_isSymmetric]
  simp [mul_assoc, coeff₁_traceMk_mul, trace_comm f z.diagMk₁]

end trace

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
abbrev toHeckeModule (A : Rep k G) : ModuleCat (HeckeAlgebra H σ) :=
  ModuleCat.of (HeckeAlgebra H σ) (HeckeModule H σ A.ρ)

/-- The module over the opposite standard Hecke algebra associated a representation `ρ` of `G`. -/
abbrev toHecke₁Module (A : Rep k G) : ModuleCat (HeckeAlgebra₁ k H) :=
  ModuleCat.of (HeckeAlgebra₁ k H) (HeckeModule₁ H A.ρ)

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
abbrev toHeckeModuleFunctor : Rep k G ⥤ ModuleCat (HeckeAlgebra H σ) where
  obj := toHeckeModule H σ
  map := toHeckeModuleMap H σ

/-- The functor sending represenations to Hecke modules over the opposite standard Hecke algbera. -/
abbrev toHecke₁ModuleFunctor : Rep k G ⥤ ModuleCat (HeckeAlgebra₁ k H) where
  obj := toHecke₁Module H
  map := toHecke₁ModuleMap H

end Rep

end

end Representation
