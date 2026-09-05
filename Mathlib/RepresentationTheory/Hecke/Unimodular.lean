/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Hecke.LeftFiniteDoubleCoset
public import Mathlib.RepresentationTheory.Hecke.Multiplicity

/-!
# Unimodular condition for subgroups

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

lemma coe_inv (x : DoubleCoset₀ H H) :
    x.inv = x.val.inv := rfl

@[simp]
lemma inv_mk (g : G) [IsLeftFinite H H g] :
    (mk H H g).inv = mk H H g⁻¹ := rfl

lemma mk_inv_rep (x : DoubleCoset₀ H H) :
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

private lemma multiplicity_self_inv_mk_one_eq_degree (x : DoubleCoset₀ H H) :
    x.multiplicity x.inv (mk H H 1) = x.degree := by
  rw [multiplicity_apply, ← mk_rep x, mk_degree, mk_rep]
  have hrep : DoubleCoset.mk H H x.inv.rep = DoubleCoset.mk H H x.rep⁻¹ := by
    rw [← coe_mk, ← coe_mk, mk_inv_rep, mk_rep]
  obtain ⟨j, hj⟩ := DoubleCoset.LeftDecompQuotient.mem_range_toLeftCoset_iff.mpr hrep
  simp only [DoubleCoset.LeftDecompQuotient.toLeftCoset_apply] at hj
  have heq (i : LeftDecompQuotient H H x.rep) :
      (i.out * x.rep * (j.out * x.inv.rep) : G ⧸ H)
        = ((mk H H 1).rep : G ⧸ H) := by
    calc
      _ = (i.out : G ⧸ H) := by
        simpa [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc] using
          congrArg (fun q : G ⧸ H => (i.out * x.rep : G) • q) hj
      _ = _ := by
        simpa [QuotientGroup.eq (a := i.out.val)] using H.mul_mem (H.inv_mem i.out.prop) (by simp)
  exact Nat.card_congr
    { toFun p := p.1.1
      invFun i := ⟨(i, j), heq i⟩
      left_inv p := Subtype.ext
        (Prod.ext rfl (DoubleCoset.LeftDecompQuotient.snd_eq_of_fst_eq (heq p.1.1) p.prop))
      right_inv _ := rfl}

private lemma multiplicity_ne_self_inv_mk_one_eq_zero {x y : DoubleCoset₀ H H} (h : y ≠ x.inv) :
    x.multiplicity y (mk H H 1) = 0 := by
  simp only [multiplicity_apply]
  by_contra hne
  apply h
  obtain ⟨p, hp⟩ := (Nat.card_ne_zero.mp hne).left
  simp only [Set.mem_ofPred_eq, ← mul_assoc, QuotientGroup.eq, mul_inv_rev] at hp
  rw [← mk_rep y, ← mk_inv_rep]
  refine mk_eq_iff.mpr ⟨_, p.2.out.prop, y.rep⁻¹ * p.2.out⁻¹ * x.rep⁻¹, ?_, by simp [mul_assoc]⟩
  simpa [mul_assoc] using H.mul_mem hp (H.mul_mem (H.inv_mem (diag_mk_one_rep_mem H)) p.1.out.prop)

@[simp]
lemma multiplicity_apply_one {x y : DoubleCoset₀ H H} [Decidable (y = x.inv)] :
    x.multiplicity y (mk H H 1) = if y = x.inv then x.degree else 0 := by
  by_cases h : y = x.inv
  · simp [h, DoubleCoset₀.multiplicity_self_inv_mk_one_eq_degree]
  · simp [h, DoubleCoset₀.multiplicity_ne_self_inv_mk_one_eq_zero]

end DoubleCoset₀
