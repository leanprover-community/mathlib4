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
    cosetVector k ⟦g⟧ = cosetVectorMk k g H :=
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
    (fun g => LinearMap.toSpanSingleton k _ (MonoidAlgebra.single ⟦g⁻¹⟧ 1))
    (by intros; congr 3; exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by simp)))
  isIntertwining' _ := by ext; simp

@[simp]
lemma indTrivialToOfMulActionMap_apply_cosetVectorMk (g : G) :
    (indTrivialToOfMulActionMap k H) (cosetVectorMk k g H) = MonoidAlgebra.single ⟦g⟧ 1 := by
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

/-- tbd -/
abbrev DecompQuotient := H₁ ⧸ ((ConjAct.toConjAct g) • H₂).subgroupOf H₁

/-- tbd -/
def DecompQuotient.toLeftCoset :
    DecompQuotient H₁ g H₂ → G ⧸ H₂ :=
  Quotient.lift (fun x => ⟦x * g⟧) fun _ _ h => by
    rw [Quotient.eq, QuotientGroup.leftRel_apply]
    have := (QuotientGroup.leftRel_apply.mp h)
    simpa [mul_assoc] using mem_conjAct_pointwise_smul_iff.mp this

variable {H₁ g H₂}

lemma DecompQuotient.mk_eq_iff {x x' : H₁} :
    ⟦x⟧ = (⟦x'⟧ : DecompQuotient H₁ g H₂) ↔ (⟦x.val * g⟧ : G ⧸ H₂) = ⟦x'.val * g⟧ := by
  simp [Quotient.eq, QuotientGroup.leftRel_apply, mul_assoc, Subgroup.mem_subgroupOf,
    mem_conjAct_pointwise_smul_iff]

lemma DecompQuotient.eq_one_iff (x : DecompQuotient H₁ g H₂) :
    x = ⟦1⟧ ↔ (⟦(x.out : G) * g⟧ : G ⧸ H₂) = ⟦g⟧ := by
  constructor <;> (rw [← Quotient.out_eq' x, DecompQuotient.mk_eq_iff]; simp)

@[simp]
lemma DecompQuotient.toLeftCoset_apply (x : DecompQuotient H₁ g H₂) :
    DecompQuotient.toLeftCoset H₁ g H₂ x = ⟦x.out * g⟧ := by
  nth_rw 1 [← Quotient.out_eq x]
  rfl

lemma DecompQuotient.toLeftCoset.injective (H₁ H₂ : Subgroup G) (g : G) :
    Function.Injective (DecompQuotient.toLeftCoset H₁ g H₂) := by
  intro i j hij
  simp only [DecompQuotient.toLeftCoset_apply] at hij
  simpa using DecompQuotient.mk_eq_iff.mpr hij

variable (H₁ g H₂)

/-- tbd -/
class IsHeckeTriple : Prop where
  hasFiniteDecompQuotient : (((ConjAct.toConjAct g) • H₂)).IsFiniteRelIndex H₁

instance [h : IsHeckeTriple H₁ g H₂] : Fintype (DecompQuotient H₁ g H₂) := by
  have := h.hasFiniteDecompQuotient
  exact Subgroup.fintypeOfIndexNeZero Subgroup.relIndex_ne_zero

instance instIsHeckeTriple_diag_one (H : Subgroup G) : IsHeckeTriple H 1 H := ⟨⟨by simp⟩⟩

instance instIsHeckeTriple_mulLeft [IsHeckeTriple H₁ g H₂] (h₁ : H₁) :
    IsHeckeTriple H₁ (h₁ * g) H₂ := ⟨by
  have hh : (ConjAct.toConjAct (h₁ : G)) • H₁ = H₁ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer h₁.prop)
  nth_rewrite 2 [← hh]
  simpa [mul_smul, Subgroup.relIndex_pointwise_smul, Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    using IsHeckeTriple.hasFiniteDecompQuotient⟩

instance instIsHeckeTriple_mulRight [IsHeckeTriple H₁ g H₂] (h₂ : H₂) :
    IsHeckeTriple H₁ (g * h₂) H₂ := ⟨by
  have hh : (ConjAct.toConjAct (h₂ : G)) • H₂ = H₂ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer h₂.prop)
  simpa [mul_smul, hh] using IsHeckeTriple.hasFiniteDecompQuotient⟩

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

/-- tbd -/
abbrev HeckeSet : Set G := Set.ofPred (fun g => IsHeckeTriple H₁ g H₂)

instance (g : HeckeSet H₁ H₂) : IsHeckeTriple H₁ g.val H₂ := g.prop

/-- tbd -/
abbrev HeckeSet.Setoid : Setoid (HeckeSet H₁ H₂) :=
  (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

/-- tbd -/
def HeckeCoset := Quotient (HeckeSet.Setoid H₁ H₂)

/-- tbd -/
def HeckeCoset.mk (g : G) [hg : IsHeckeTriple H₁ g H₂] : HeckeCoset H₁ H₂ := ⟦⟨g, hg⟩⟧

variable {H₁ H₂ H₃}

/-- tbd -/
abbrev HeckeCoset.rep (x : HeckeCoset H₁ H₂) : HeckeSet H₁ H₂ := x.out

lemma HeckeCoset.mk_rep (x : HeckeCoset H₁ H₂) : ⟦x.rep⟧ = x := Quotient.out_eq' x

lemma HeckeCoset.mk_eq_iff {x y : HeckeSet H₁ H₂} :
    (⟦x⟧ : HeckeCoset H₁ H₂) = ⟦y⟧ ↔ ∃ (h₁ : H₁) (h₂ : H₂), y.val = h₁ * x.val * h₂ := by
  simpa [Quotient.eq] using DoubleCoset.rel_iff

lemma HeckeCoset.rep_leftCoset_ne_if_ne {x y : HeckeCoset H₁ H₂} (hxy : x ≠ y) (h₁ : H₁) :
    (⟦h₁ * x.rep⟧ : G ⧸ H₂) ≠ ⟦(y.rep : G)⟧ := by
  intro h
  apply hxy
  rw [← HeckeCoset.mk_rep x, ← HeckeCoset.mk_rep y, HeckeCoset.mk_eq_iff.mpr]
  exact ⟨h₁, ⟨((h₁ : G) * x.rep)⁻¹ * y.rep, QuotientGroup.eq.mp h⟩, by simp [mul_assoc]⟩

lemma HeckeCoset.rep_mk_leftCoset.injective :
    Function.Injective (fun x : HeckeCoset H₁ H₂ => (⟦x.rep⟧ : G ⧸ H₂)) := by
  intro x y h
  rw [← HeckeCoset.mk_rep x, ← HeckeCoset.mk_rep y]
  exact Quotient.sound <| DoubleCoset.rel_iff.mpr
    ⟨1, by simp, _, QuotientGroup.leftRel_apply.mp (Quotient.exact h), by simp⟩

/-- tbd -/
def HeckeCoset.mulMap (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃)
    (p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃) : HeckeCoset H₁ H₃ :=
  HeckeCoset.mk H₁ H₃ (p.1.out * x.rep.val * p.2.out * y.rep)

/-- tbd -/
def HeckeCoset.multiplicity (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃) (z : HeckeCoset H₁ H₃) :
    Nat :=
    Nat.card {p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃ |
    ((p.1.out : G) * x.rep * ((p.2.out : G) * y.rep ) : G ⧸ H₃) = (z.rep  : G ⧸ H₃)}

lemma HeckeCoset.mulMap_eq_of_mk_eq (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃)
    (z : HeckeCoset H₁ H₃) {p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃}
    (h : ⟦p.1.out * x.rep.val * ((p.2.out : G) * y.rep)⟧ = (z.rep : G ⧸ H₃)) :
    x.mulMap y p = z := by
  rw [← HeckeCoset.mk_rep z]
  apply HeckeCoset.mk_eq_iff.mpr
  exact ⟨1,⟨((p.1.out * x.rep.val * p.2.out * y.rep)⁻¹ * z.rep), by
    simpa [mul_assoc] using QuotientGroup.eq.mp h⟩, by simp [mul_assoc]⟩

instance (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃) :
    Fintype (x.multiplicity y).support := by
  classical
  apply Set.Finite.fintype
  refine (Finset.univ.image (x.mulMap y)).finite_toSet.subset ?_
  intro z hz
  change x.multiplicity y z ≠ 0 at hz
  rw [HeckeCoset.multiplicity, Nat.card_ne_zero] at hz
  obtain ⟨⟨p, hp⟩, _⟩ := hz
  change z ∈ Finset.univ.image (x.mulMap y)
  exact Finset.mem_image.mpr
    ⟨p, Finset.mem_univ p, HeckeCoset.mulMap_eq_of_mk_eq x y z hp⟩

/-- tbd -/
def HeckeCosetVector : HeckeCoset H₁ H₂ → IndV H₂.subtype (trivial k H₂ k) :=
  fun x => ∑ i, cosetVector k (DecompQuotient.toLeftCoset H₁ x.rep H₂ i)

lemma HeckeCosetVector_isInvariant (x : HeckeCoset H₁ H₂) (h₁ : H₁) :
    ind H₂.subtype (trivial k H₂ k) h₁ (HeckeCosetVector k x) = HeckeCosetVector k x := by
  simp only [HeckeCosetVector, DecompQuotient.toLeftCoset_apply, map_sum, ind_apply_cosetVector]
  exact Fintype.sum_equiv (MulAction.toPerm h₁) _ _ fun y => by
    congr 1
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc]
    change ⟦(h₁ * y.out : H₁) * (x.out : G)⟧ = _
    rw [← DecompQuotient.mk_eq_iff]
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
    (hy : f.toLeftCosetModule.coeff ⟦y⟧ ≠ 0) : IsHeckeTriple H₁ y H₂ := by
  have : Finite (DecompQuotient H₁ y H₂) :=
    Finite.of_injective (β := f.toLeftCosetModule.coeff.support)
      (fun z => ⟨DecompQuotient.toLeftCoset H₁ y H₂ z, by
        simpa using (toLeftCosetModule.coeff_isInvariant f _ _).trans_ne hy⟩)
      fun _ _ h => DecompQuotient.toLeftCoset.injective H₁ H₂ y (congrArg Subtype.val h)
  exact ⟨Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr Subgroup.finiteIndex_of_finite_quotient⟩

variable (k H₁ H₂)

/-- tbd -/
def toHeckeCosetModuleLinearMap :
    HeckeBimodule₁ k H₁ H₂ →ₗ[k] k[HeckeCoset H₁ H₂] where
  toFun f := comapDomain (fun x => ⟦x.rep.val⟧) (HeckeCoset.rep_mk_leftCoset.injective)
    (f.toLeftCosetModule)
  map_add' := by simp [HeckeBimodule₁.toLeftCosetModule]
  map_smul' _ _ := by ext; simp [HeckeBimodule₁.toLeftCosetModule]

@[simp]
lemma toHeckeCosetModuleLinearMap_apply_mk₁ (x : HeckeCoset H₁ H₂) :
    (toHeckeCosetModuleLinearMap k H₁ H₂) x.mk₁ = single x 1
  := by classical
  ext y
  simp only [toHeckeCosetModuleLinearMap, toLeftCosetModule_apply, LinearMap.coe_mk, AddHom.coe_mk,
    HeckeCoset.mk₁_apply, coeff_comapDomain, Finsupp.comapDomain_apply, coeff_single]
  simp only [HeckeCosetVector, DecompQuotient.toLeftCoset_apply, cosetVector_mk_eq_cosetVectorMk,
    map_sum, indTrivialToOfMulActionMap_apply_cosetVectorMk, coeff_sum, coeff_single,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases hxy : x = y
  · simp [← hxy, Finsupp.single_apply, ← DecompQuotient.eq_one_iff]
  · simp [hxy, HeckeCoset.rep_leftCoset_ne_if_ne]

lemma toHeckeCosetModuleLinearMap.coeff_eq_coeff (f : HeckeBimodule₁ k H₁ H₂)
    (x : HeckeCoset H₁ H₂) :
    (toHeckeCosetModuleLinearMap k H₁ H₂ f).coeff x = f.toLeftCosetModule.coeff ⟦x.out⟧ := by
  simp [toHeckeCosetModuleLinearMap]

/-- tbd -/
def toHeckeCosetModuleLinearInv :
    k[HeckeCoset H₁ H₂] →ₗ[k] HeckeBimodule₁ k H₁ H₂ :=
  (MonoidAlgebra.basis (HeckeCoset H₁ H₂) k).constr k fun x => x.mk₁

@[simp]
lemma toHeckeCosetModuleLinearInv_apply_single (x : HeckeCoset H₁ H₂) :
    ((toHeckeCosetModuleLinearInv k H₁ H₂) (single x 1)) = x.mk₁ := by
  simp [toHeckeCosetModuleLinearInv, ← MonoidAlgebra.basis_apply]

lemma toHeckeCosetModuleLinearInv.isRightInv (x : k[HeckeCoset H₁ H₂]) :
    toHeckeCosetModuleLinearMap k H₁ H₂ (toHeckeCosetModuleLinearInv k H₁ H₂ x) = x :=
  induction_linear x (by simp) (fun _ _ h h' => by nth_rw 2 [← h, ← h']; simp) <| by
    intro _ r
    rw [← mul_one r, ← MonoidAlgebra.smul_single', map_smul]
    simp

lemma toHeckeCosetModuleLinearMap.injective :
    Function.Injective (toHeckeCosetModuleLinearMap k H₁ H₂) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext
  apply (indTrivialOfMulActionEquiv k H₂).injective
  ext y
  change f.toLeftCosetModule.coeff y = 0
  by_contra! hy; apply hy
  have : IsHeckeTriple H₁ y.out H₂ := isHeckeTriple_of_coeff_ne_zero f y.out (by simpa using hy)
  let g : HeckeSet H₁ H₂ := ⟨y.out, this⟩
  let x : HeckeCoset H₁ H₂ := ⟦g⟧
  obtain ⟨h₁, h₂, heq⟩ := (HeckeCoset.mk_eq_iff (x := x.rep) (y := g)).mp <| by simp [x]
  have : ⟦g.val⟧ = y := by simp [g]
  simp only [← this, heq, QuotientGroup.mk_mul_of_mem _ h₂.prop]
  rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, toLeftCosetModule.coeff_isInvariant]
  simpa [toHeckeCosetModuleLinearMap.coeff_eq_coeff] using congrArg (fun f => f.coeff x) hf

/-- tbd -/
@[simps!]
def toHeckeCosetModuleLinearEquiv :
    HeckeBimodule₁ k H₁ H₂ ≃ₗ[k] k[HeckeCoset H₁ H₂] where
  toLinearMap := toHeckeCosetModuleLinearMap k H₁ H₂
  invFun := toHeckeCosetModuleLinearInv k H₁ H₂
  left_inv f := by
    apply toHeckeCosetModuleLinearMap.injective
    simp [toHeckeCosetModuleLinearInv.isRightInv]
  right_inv := toHeckeCosetModuleLinearInv.isRightInv k H₁ H₂

variable {k H₁ H₂} in
lemma induction_on (f : HeckeBimodule₁ k H₁ H₂) {p : HeckeBimodule₁ k H₁ H₂ → Prop}
    (zero : p 0)
    (mk : ∀ (g : HeckeCoset H₁ H₂), p (g.mk₁))
    (smul : ∀ (r : k) (x : HeckeBimodule₁ k H₁ H₂), p x → p (r • x))
    (add : ∀ x y, p x → p y → p (x + y)) : p f := by
  let E := toHeckeCosetModuleLinearEquiv k H₁ H₂
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

lemma HeckeAction_mk₁_apply (x : HeckeCoset H₁ H₂) (v : HeckeModule₁ H₂ ρ) :
    HeckeAction x.mk₁ v (cosetVectorMk k 1 H₁) =
      ∑ (i : DecompQuotient H₁ x.rep H₂), ρ (i.out * x.rep) (v (cosetVectorMk k 1 H₂)) := by
  simp only [HeckeAction_eq_comp, IntertwiningMap.comp_apply, HeckeCoset.mk₁_apply, map_mul,
    Module.End.mul_apply]
  simp [HeckeCosetVector, ← IntertwiningMap.isIntertwining]

variable {H₁ H₂ H₃}

lemma HeckeAction_mk₁_mk₁_apply_eq (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃) :
    HeckeAction x.mk₁ y.mk₁ (cosetVectorMk k 1 H₁) =
      ∑ (p : DecompQuotient H₁ x.rep H₂ × DecompQuotient H₂ y.rep H₃),
        cosetVectorMk k (p.1.out * x.rep.val * p.2.out * y.rep) H₃ := by
  simp only [HeckeAction_mk₁_apply, map_mul, HeckeCoset.mk₁_apply, Module.End.mul_apply]
  simp only [HeckeCosetVector, DecompQuotient.toLeftCoset_apply, cosetVector_mk_eq_cosetVectorMk,
    map_sum, ind_apply_cosetVectorMk]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_congr _ _ (by simp [mul_assoc])

lemma HeckeAction_mk₁_mk₁_coeff_eq (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃)
    (z : HeckeCoset H₁ H₃) :
    (HeckeBimodule₁.toLeftCosetModule (HeckeAction x.mk₁ y.mk₁)).coeff z.out
      = (x.multiplicity y z : k) := by classical
  simp only [HeckeBimodule₁.toLeftCosetModule_apply, HeckeAction_mk₁_mk₁_apply_eq, map_sum,
    indTrivialToOfMulActionMap_apply_cosetVectorMk, coeff_sum, coeff_single, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  simp [Finsupp.single_apply, HeckeCoset.multiplicity, mul_assoc]

theorem HeckeAction_mk₁_mk₁_eq (x : HeckeCoset H₁ H₂) (y : HeckeCoset H₂ H₃) :
    HeckeAction x.mk₁ y.mk₁ = ∑ w : (x.multiplicity y).support, (x.multiplicity y w) • w.1.mk₁
    (k := k) := by classical
  apply HeckeBimodule₁.toHeckeCosetModuleLinearMap.injective
  ext z
  rw [HeckeBimodule₁.toHeckeCosetModuleLinearMap.coeff_eq_coeff, HeckeAction_mk₁_mk₁_coeff_eq]
  simp only [map_sum, LinearMap.map_smul_of_tower,
    HeckeBimodule₁.toHeckeCosetModuleLinearMap_apply_mk₁, smul_single, nsmul_eq_mul,
    mul_one, coeff_sum, coeff_single, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  by_cases hz : z ∈ (x.multiplicity y).support
  · simp [← Subtype.ext_iff (a2 := ⟨z, hz⟩)]
  · have hz' (w : (x.multiplicity y).support) : w ≠ z := fun h => hz (h ▸ w.property)
    simp [Function.notMem_support.mp hz, hz']

end HeckeAction

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
