/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.HeckeCoset.Multiplicity

/-!
# Multiplicity

-/

@[expose] public section

open DoubleCoset

variable {G : Type*} [Group G] {H H₁ H₂ : Subgroup G}

namespace DoubleCoset

/-- tbd -/
def inv (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) :=
  Quotient.liftOn x (fun x => DoubleCoset.mk H₂ H₁ x⁻¹) fun a b hab => by
    obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := DoubleCoset.rel_iff.mp hab
    rw [DoubleCoset.eq]
    exact ⟨h₂⁻¹, H₂.inv_mem hh₂, h₁⁻¹, H₁.inv_mem hh₁, by simp [heq, mul_assoc]⟩

@[simp]
lemma inv_mk (g : G) :
    inv (mk H₁ H₂ g) = mk H₂ H₁ g⁻¹ := by
  rfl

lemma mk_inv_out (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    mk H₂ H₁ x.out⁻¹ = inv x := by
  simp [← inv_mk, DoubleCoset.out_eq']

@[simp]
lemma inv_inv (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    inv (inv x) = x :=
  Quotient.inductionOn x fun x => by simp

end DoubleCoset

/-- tbd -/
class IsHeckeUnimodular (H : Subgroup G) : Prop where
  degree_eq_inv_degree : ∀ (x : DoubleCoset.Quotient (H : Set G) (H : Set G)),
    x.degree = (inv x).degree

instance [IsHeckeUnimodular H] (g : G) [IsHeckeTriple H H g] :
    IsHeckeTriple H H g⁻¹ := by
  rw [isHeckeTriple_iff, ←inv_mk g, ← IsHeckeUnimodular.degree_eq_inv_degree]
  simp [mk_degree]
namespace HeckeCoset

variable [IsHeckeUnimodular H]

/-- tbd -/
def inv (x : HeckeCoset H H) :
    HeckeCoset H H := ⟨DoubleCoset.inv x, by simp [← IsHeckeUnimodular.degree_eq_inv_degree]⟩

lemma coe_inv (x : HeckeCoset H H) :
    x.inv = DoubleCoset.inv x.val := rfl

@[simp]
lemma inv_mk (g : G) [IsHeckeTriple H H g] :
    (mk H H g).inv = mk H H g⁻¹ := rfl

lemma mk_inv_rep (x : HeckeCoset H H) :
    mk H H x.rep⁻¹ = x.inv  := by
  simp [inv, ← DoubleCoset.mk_inv_out, rep_eq_out]

@[simp]
lemma inv_inv (x : HeckeCoset H H) :
    x.inv.inv = x :=
  induction_on x (p := fun x => x.inv.inv = x) fun g => by simp

lemma inv_eq_iff {x y : HeckeCoset H H} :
    x.inv = y ↔ x = y.inv :=
  ⟨by intro rfl; simp, by intro rfl; simp⟩

@[simp]
lemma inv_degree_eq_degree (x : HeckeCoset H H) :
    x.inv.degree = x.degree := by
  rw [← mk_rep x, mk_degree, ← DoubleCoset.mk_degree, IsHeckeUnimodular.degree_eq_inv_degree]
  simp [inv, mk_degree, DoubleCoset.mk_degree]

lemma diag_one_inv_eq_self :
    (mk H H 1).inv = (mk H H 1) := by
  simp

private lemma multiplicity_self_inv_mk_one_eq_degree (x : HeckeCoset H H) :
    x.multiplicity x.inv (mk H H 1) = x.degree := by classical
  simp only  [multiplicity_apply]
  obtain ⟨h₁, hh₁, h₂, hh₂, hinv⟩ := mk_eq_iff.mp
    (show mk H H x.rep⁻¹ = mk H H x.inv.rep by simp [mk_inv_rep])
  let j : DecompQuotient H H x.inv.rep := QuotientGroup.mk ⟨h₁⁻¹, H.inv_mem hh₁⟩
  have hrep : DoubleCoset.mk H H x.inv.rep = DoubleCoset.mk H H x.rep⁻¹ := by
    rw [← coe_mk, ← coe_mk, mk_inv_rep, mk_rep]
  obtain ⟨j, hj⟩ := DoubleCoset.DecompQuotient.exists_toLeftCoset_of_mk_eq hrep
  simp only [DoubleCoset.DecompQuotient.toLeftCoset_apply] at hj
  have heq (i : DecompQuotient H H x.rep) :
      (i.out * x.rep * (j.out * x.inv.rep) : G ⧸ H)
        = ((mk H H 1).rep : G ⧸ H) := by
    calc
      _ = (i.out : G ⧸ H) := by
        simpa [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc] using
          congrArg (fun q : G ⧸ H => (i.out * x.rep : G) • q) hj
      _ = _ := by
        simpa [QuotientGroup.eq (a := i.out.val)] using H.mul_mem (H.inv_mem i.out.prop) (by simp)
  let equiv :
      {p : DecompQuotient H H x.rep × DecompQuotient H H x.inv.rep |
        ((p.1.out * x.rep * (p.2.out * x.inv.rep) : G) :  G ⧸ H) = ((mk H H 1).rep : G ⧸ H)}
      ≃ DecompQuotient H H x.rep :=
    { toFun p := p.1.1
      invFun i := ⟨(i, j), heq i⟩
      left_inv p := Subtype.ext
        (Prod.ext rfl (DoubleCoset.DecompQuotient.snd_eq_of_fst_eq (heq p.1.1) p.prop))
      right_inv _ := rfl}
  simpa [degree_eq_rep] using Nat.card_congr equiv

private lemma multiplicity_ne_self_inv_mk_one_eq_zero {x y : HeckeCoset H H} (h : y ≠ x.inv) :
    x.multiplicity y (mk H H 1) = 0 := by
  simp only [multiplicity_apply]
  by_contra hne
  obtain ⟨p, hp⟩ := (Nat.card_ne_zero.mp hne).left
  simp only [Set.mem_ofPred_eq, ← mul_assoc, QuotientGroup.eq, mul_inv_rev] at hp
  have heq : y = x.inv := by
    rw [← HeckeCoset.mk_rep y, ← mk_inv_rep]
    apply mk_eq_iff.mpr
    have : y.rep⁻¹ * p.2.out⁻¹ * x.rep⁻¹ ∈ H := by
      simpa [mul_assoc] using
        H.mul_mem hp (H.mul_mem (H.inv_mem (HeckeCoset.diag_mk_one_rep_mem H)) p.1.out.prop)
    exact ⟨p.2.out, p.2.out.prop, (y.rep⁻¹ * p.2.out⁻¹ * x.rep⁻¹), this, by simp [mul_assoc]⟩
  exact h heq

@[simp]
lemma multiplicity_apply_one {x y : HeckeCoset H H} [Decidable (y = x.inv)] :
    x.multiplicity y (mk H H 1) = if y = x.inv then x.degree else 0 := by
  by_cases h : y = x.inv
  · simp [h, HeckeCoset.multiplicity_self_inv_mk_one_eq_degree]
  · simp [h, HeckeCoset.multiplicity_ne_self_inv_mk_one_eq_zero]

end HeckeCoset
