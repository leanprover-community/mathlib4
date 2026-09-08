/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.Data.Finsupp.Defs
public import Mathlib.RepresentationTheory.Hecke.LeftFiniteDoubleCoset

/-!
# Structure constants of the convolution product

This file defines the structureConst for a triple of double cosets: the coefficient with which the
third occurs in the convolution product of the first two. We also provide a flexible computation
lemma `structureConst_mk_mk_mk` that allows arbitrary representatives to be chosen.
-/

@[expose] public section

variable {G : Type*} [Group G] {H₁ H₂ H₃ : Subgroup G}
open DoubleCoset

namespace DoubleCoset

/-- The map sending `(gH₁, g'H₂)` to `H₁g⁻¹g'H₂`. -/
def relPosition : G ⧸ H₁ → G ⧸ H₂ → DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G) :=
  Quotient.lift₂ (fun g g' : G => mk H₁ H₂ (g⁻¹ * g')) fun _ _ _ _ ha hb => by
    rw [eq]
    exact ⟨_, H₁.inv_mem (QuotientGroup.leftRel_apply.mp ha), _,
      QuotientGroup.leftRel_apply.mp hb, by simp [mul_assoc]⟩

@[simp]
lemma relPosition_mk_mk (g g' : G) :
    relPosition (g : G ⧸ H₁) (g' : G ⧸ H₂) = mk H₁ H₂ (g⁻¹ * g') := rfl

@[simp]
lemma relPosition_smul (g : G) (c : G ⧸ H₁) (d : G ⧸ H₂) :
    relPosition (g • c) d = relPosition c (g⁻¹ • d) := by
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, MulAction.Quotient.smul_mk,
    MulAction.Quotient.smul_mk, relPosition_mk_mk, relPosition_mk_mk]
  simp [mul_assoc]

lemma relPosition_one_eq_iff {x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)} {c : G ⧸ H₂} :
    relPosition ((1 : G) : G ⧸ H₁) c = x ↔ c ∈ x.leftDecomposition := by
  rw [← QuotientGroup.out_eq' c, relPosition_mk_mk, mem_leftDecomposition_mk]
  simp

/-- The number of left cosets `aH₂ ⊆ x` such that `H₂a⁻¹bH₃ = y` for any fixed left coset `bH₃ ⊆ z`,
or `0` if there are infinitely many. See `structureConst_mk_mk_mk` for a computation lemma. -/
noncomputable def Quotient.structureConst (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G))
    (y : DoubleCoset.Quotient (H₂ : Set G) (H₃ : Set G))
    (z : DoubleCoset.Quotient (H₁ : Set G) (H₃ : Set G)) :
    ℕ :=
  Quotient.liftOn z (fun g => Nat.card {d ∈ x.leftDecomposition | relPosition d g = y})
    fun g g' h => by
      obtain ⟨h₁ ,hh₁, h₃, hh₃, rfl⟩ := rel_iff.mp h
      exact Nat.card_congr <| Equiv.subtypeEquiv (MulAction.toPerm h₁) fun c =>
        QuotientGroup.induction_on c (by simp [hh₃, mk_mem_mul ⟨_, hh₁⟩])

lemma structureConst_mk (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G))
    (y : DoubleCoset.Quotient (H₂ : Set G) (H₃ : Set G)) (g : G) :
    x.structureConst y (mk H₁ H₃ g) =  Nat.card {d ∈ x.leftDecomposition | relPosition d g = y} :=
  rfl

lemma structureConst_of_mem (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G))
    (y : DoubleCoset.Quotient (H₂ : Set G) (H₃ : Set G))
    (z : DoubleCoset.Quotient (H₁ : Set G) (H₃ : Set G))
    {c : G ⧸ H₃} (hc : c ∈ z.leftDecomposition) :
    x.structureConst y z = Nat.card {d ∈ x.leftDecomposition | relPosition d c = y} := by
  rw [← QuotientGroup.out_eq' c] at hc ⊢
  rw [← mem_leftDecomposition_mk.mp hc, structureConst_mk]

open leftDecompQuotient in
/-- The computation formula for structureConst with given representatives of doublecosets and
left-coset decompositions. -/
lemma structureConst_mk_mk_mk (u v w : G) {ι κ : Type*}
    {σ : ι → H₁} (hσ : Function.Bijective fun i => (σ i : leftDecompQuotient H₁ H₂ u))
    {τ : κ → H₂} (hτ : Function.Bijective fun j => (τ j : leftDecompQuotient H₂ H₃ v)) :
    (mk H₁ H₂ u).structureConst (mk H₂ H₃ v) (mk H₁ H₃ w) =
      Nat.card {p : ι × κ | (σ p.1 * u * (τ p.2 * v) : G ⧸ H₃) = (w : G ⧸ H₃)} := by
  rw [structureConst_mk, eq_comm]
  refine Nat.card_eq_of_bijective ⟨?_, ?_⟩
    (f := fun ⟨p, hp⟩ => ⟨(σ p.1).val * u, ⟨by simp, by simp [← Set.mem_ofPred.mp hp, mul_assoc]⟩⟩)
  · intro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    -- We obtain injectivity from  `H₁/(gH₂g⁻¹ ∩ H₁) ↪ G ⧸ H₂` and `axH₃ = ayH₃ ↔ xH₃ = yH₃`
    obtain rfl : x1 = y1 := hσ.injective <| toLeftCoset_injective (by simp [heq])
    obtain rfl : x2 = y2 := hτ.injective <| toLeftCoset_injective (by
      simpa [mul_assoc] using congrArg ((σ x1 * u)⁻¹ • ·) (hx.trans hy.symm))
    rfl
  · intro ⟨d, hd, hrel⟩
    -- We construct inverse `⟨i, j⟩` s.t. `(σ i * u)H₂ = d` `(τ j * v)H₃ = (σ i * u)⁻¹wH₃`
    simp only [Set.mem_ofPred_eq, Subtype.mk.injEq, Subtype.exists, exists_prop, Prod.exists]
    obtain ⟨i, hi⟩ := toLeftDecompositionEquiv.surjective.comp hσ.surjective ⟨d, hd⟩
    simp only [Function.comp_apply, toLeftDecompositionEquiv_apply_coe, toLeftCoset_mk,
      Subtype.ext_iff] at hi
    obtain ⟨j, hj⟩ := toLeftDecompositionEquiv.surjective.comp hτ.surjective
      ⟨((σ i * u)⁻¹ * w : G ⧸ H₃), by rw [mem_leftDecomposition_mk, ← relPosition_mk_mk, hi, hrel]⟩
    exact ⟨i, j, by simpa [mul_assoc] using congrArg ((σ i * u) • ·) (Subtype.ext_iff.mp hj), hi⟩

end DoubleCoset

namespace DoubleCoset₀

noncomputable def structureConst (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃) :
    DoubleCoset₀ H₁ H₃ →₀ ℕ :=
  Finsupp.ofSupportFinite (fun z => x.val.structureConst y.val z.val) <| by
    apply Set.Finite.of_finite_image (f := Subtype.val) _ fun _ _ _ _ h => Subtype.ext h
    refine (Set.finite_range fun p : x.leftDecomposition × y.leftDecomposition =>
      relPosition (p.1.val.out⁻¹ : G) p.2.val).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [Function.mem_support, ← out_eq' z.val, structureConst_mk, Nat.card_ne_zero] at hz
    obtain ⟨⟨⟨d, hd, hrel⟩⟩, -⟩ := hz
    refine ⟨(⟨d, hd⟩, ⟨(d.out : G)⁻¹ • ((z.val.out : G) : G ⧸ H₃), ?_⟩), ?_⟩
    · rw [← relPosition_one_eq_iff, ← relPosition_smul]
      simpa using hrel
    · simpa [relPosition_one_eq_iff, mem_leftDecomposition_mk] using out_eq' z.val

@[simp]
lemma structureConst_coe (x : DoubleCoset₀ H₁ H₂) (y : DoubleCoset₀ H₂ H₃)
    (z : DoubleCoset₀ H₁ H₃) :
    x.structureConst y z = x.val.structureConst y.val z.val := rfl

end DoubleCoset₀
