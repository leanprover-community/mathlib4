/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Hecke.LeftFiniteDoubleCoset
public import Mathlib.RepresentationTheory.Hecke.StructureConst

/-!
# Unimodular condition for subgroups

This file introduces the unimodular condition for a subgroup and calculate the structure constant of
the involultion under such condition.
-/

@[expose] public section

open DoubleCoset

variable {G : Type*} [Group G] {H H₁ H₂ H₃ : Subgroup G}

namespace DoubleCoset

/-- The map sending `H₁gH₂` to `H₂g⁻¹H₁`. -/
def Quotient.inv (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) :=
  Quotient.liftOn x (fun x => DoubleCoset.mk H₂ H₁ x⁻¹) fun a b hab => by
    obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := DoubleCoset.rel_iff.mp hab
    rw [DoubleCoset.eq]
    exact ⟨h₂⁻¹, H₂.inv_mem hh₂, h₁⁻¹, H₁.inv_mem hh₁, by simp [heq, mul_assoc]⟩

@[simp]
lemma inv_mk (g : G) :
    (mk H₁ H₂ g).inv = mk H₂ H₁ g⁻¹ := by
  rfl

@[simp]
lemma mk_inv_out (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    mk H₂ H₁ x.out⁻¹ = x.inv := by
  rw [← inv_mk, DoubleCoset.out_eq']

@[simp]
lemma inv_inv (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    x.inv.inv = x :=
  Quotient.inductionOn x fun x => by simp

lemma inv_eq_iff (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G))
    (y : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G)) :
    x.inv = y ↔ x = y.inv :=
  ⟨by intro rfl; simp, by intro rfl; simp⟩

end DoubleCoset

/-- A subgroup `H` is called Hecke unimodular if `Nat.card HgH = Nat.card Hg⁻¹H` for any `g`. -/
class Subgroup.IsHeckeUnimodular (H : Subgroup G) : Prop where
  degree_eq_inv_degree : ∀ (x : DoubleCoset.Quotient (H : Set G) (H : Set G)),
    x.degree = (x.inv).degree

instance [H.IsHeckeUnimodular] (g : G) [IsLeftFinite H H g] :
    IsLeftFinite H H g⁻¹ := by
  rw [isLeftFinite_iff, ←inv_mk g, ← Subgroup.IsHeckeUnimodular.degree_eq_inv_degree]
  simp [mk_degree]

@[simp]
lemma DoubleCoset.inv_degree [H.IsHeckeUnimodular]
    (x : DoubleCoset.Quotient (H : Set G) (H : Set G)) :
    x.inv.degree = x.degree :=
  (Subgroup.IsHeckeUnimodular.degree_eq_inv_degree x).symm

namespace DoubleCoset₀

variable [H.IsHeckeUnimodular]

/-- The map sending `HgH` to `Hg⁻¹H`. -/
def inv (x : DoubleCoset₀ H H) :
    DoubleCoset₀ H H := ⟨x.val.inv, by simp⟩

@[simp]
lemma coe_inv (x : DoubleCoset₀ H H) :
    x.inv = x.val.inv := rfl

@[simp]
lemma inv_mk (g : G) [IsLeftFinite H H g] :
    (mk H H g).inv = mk H H g⁻¹ := rfl

lemma mk_rep_inv (x : DoubleCoset₀ H H) :
    mk H H x.rep⁻¹ = x.inv  := by
  rw [← inv_mk, mk_rep]

@[simp]
lemma inv_inv (x : DoubleCoset₀ H H) :
    x.inv.inv = x := by
  simp [inv]

lemma inv_eq_iff {x y : DoubleCoset₀ H H} :
    x.inv = y ↔ x = y.inv :=
  ⟨by intro rfl; simp, by intro rfl; simp⟩

@[simp]
lemma inv_degree (x : DoubleCoset₀ H H) :
    x.inv.degree = x.degree := by
  simp [inv, degree]

omit [H.IsHeckeUnimodular] in
lemma relPosition_mem_one_eq_inv {x : DoubleCoset₀ H H} {c : G ⧸ H} :
    c ∈ x.leftDecomposition → relPosition c (1 : G) = x.val.inv :=
  QuotientGroup.induction_on c (fun g h => by simp; simpa using congrArg (fun y => y.inv) h)

@[simp]
lemma structureConst_apply_one {x y : DoubleCoset₀ H H} [Decidable (y = x.inv)] :
    x.structureConst y (mk H H 1) = if y = x.inv then x.degree else 0 := by
  rw [structureConst_coe, structureConst_mk, degree, degree_def]
  by_cases h : y = x.inv
  · simp only [↓reduceIte, h]
    congr 2
    simpa using fun _ => relPosition_mem_one_eq_inv
  · simp only [↓reduceIte, h, Nat.card_eq_zero, isEmpty_iff]
    exact .inl (fun ⟨a, ha⟩ => by
      simp only [ne_eq, Set.mem_ofPred_eq] at ha
      apply h
      simpa [← coe_inv, ha.2, Subtype.ext_iff (a1 := y)] using relPosition_mem_one_eq_inv ha.1)

end DoubleCoset₀
