/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# Double cosets admitting finite left-coset decomposition

This file introduces two indexing types for the left-coset decomposition: the intrinsic
`LeftDecomposition` and the computational `LeftDecompQuotient`. They are equivalent via
`toLeftDecompositionEquiv`. The first `LeftDecomposition` is useful for coordinate-free definitions
and proofs, while the second `LeftDecompQuotient` carries a base point `gH₂` and remains useful for
concrete convolution product computation.
-/

@[expose] public section

variable {G : Type*} [Group G] {H₁ H₂ : Subgroup G} {g g' : G}

open DoubleCoset Pointwise

namespace DoubleCoset

/-- Given a double coset `x`, the set of left cosets `{gH₂ | H₁gH₂ = x}`. -/
def Quotient.LeftDecomposition (x : Quotient (H₁ : Set G) (H₂ : Set G)) :
    Set (G ⧸ H₂) :=
  (Quotient.lift (fun g : G => mk H₁ H₂ g) (fun a b hab => by
    obtain h := QuotientGroup.leftRel_apply.mp hab
    rw [DoubleCoset.eq]
    exact ⟨1, H₁.one_mem, a⁻¹ * b, h, by simp⟩)) ⁻¹' {x}

@[simp]
lemma mem_LeftDecomposition_mk (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    (g : G ⧸ H₂) ∈ x.LeftDecomposition ↔ DoubleCoset.mk H₁ H₂ g = x := by
  simp [Quotient.LeftDecomposition]

instance (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :
    MulAction H₁ x.LeftDecomposition where
  smul h q := ⟨h • (q : G ⧸ H₂), by
    rw [← QuotientGroup.out_eq' q.1, MulAction.subgroup_smul_def, MulAction.Quotient.smul_mk,
      mem_LeftDecomposition_mk, smul_eq_mul, mk_mem_mul]
    simp [← mem_LeftDecomposition_mk]⟩
  one_smul q := Subtype.ext <| one_smul H₁ (q : G ⧸ H₂)
  mul_smul h h' q := Subtype.ext <| mul_smul h h' (q : G ⧸ H₂)

@[simp]
lemma coe_smul_LeftDecomposition {x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)} (h : H₁)
    (y : x.LeftDecomposition) :
    ((h • y : x.LeftDecomposition) : G ⧸ H₂) = (h : G) • (y : G ⧸ H₂) :=
  rfl

@[simp]
lemma stabilizer_leftCoset :
    MulAction.stabilizer H₁ (g : G ⧸ H₂) = (ConjAct.toConjAct g • H₂).subgroupOf H₁ := by
  ext h
  have (x : G) : x ∈ ConjAct.toConjAct g • H₂ ↔ g⁻¹ * x * g ∈ H₂ := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct, inv_inv]
  simp [Subgroup.mem_subgroupOf, this, eq_comm, QuotientGroup.eq, MulAction.subgroup_smul_def,
    mul_assoc]

variable (H₁ H₂ g) in
/-- The quotient `H₁ ⧸ (H₁ ∩ gH₂g⁻¹)` indexing the left cosets `h₁gH₂` inside the double coset
`H₁gH₂`. -/
abbrev LeftDecompQuotient := H₁ ⧸ MulAction.stabilizer H₁ (g : G ⧸ H₂)

namespace LeftDecompQuotient

/-- The map sending `⟦h₁⟧` to `h₁gH₂`. -/
def toLeftCoset :
    LeftDecompQuotient H₁ H₂ g → G ⧸ H₂ :=
  MulAction.ofQuotientStabilizer H₁ (g : G ⧸ H₂)

@[simp]
lemma toLeftCoset_mk (h : H₁) :
    toLeftCoset (h : LeftDecompQuotient H₁ H₂ g) = ((h : G) * g : G ⧸ H₂) := by
  simp [toLeftCoset, MulAction.subgroup_smul_def]

lemma toLeftCoset_apply (x : LeftDecompQuotient H₁ H₂ g) :
    toLeftCoset x = ((x.out : G) * g : G ⧸ H₂) := by
  rw [← QuotientGroup.out_eq' x, toLeftCoset_mk, QuotientGroup.out_eq']

lemma toLeftCoset_injective :
    Function.Injective (toLeftCoset (H₁ := H₁) (H₂ := H₂) (g := g)) :=
  MulAction.injective_ofQuotientStabilizer H₁ (g : G ⧸ H₂)

lemma mem_range_toLeftCoset_iff :
    (∃ i, toLeftCoset (H₁ := H₁) (g := g) i = (g' : G ⧸ H₂)) ↔ mk H₁ H₂ g = mk H₁ H₂ g' := by
  constructor
  · intro ⟨h, heq⟩
    rw [toLeftCoset_apply, QuotientGroup.eq] at heq
    exact (DoubleCoset.eq H₁ H₂ g g').mpr ⟨_, h.out.prop, _, heq, by simp [mul_assoc]⟩
  · intro h
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := (DoubleCoset.eq H₁ H₂ g g').mp h
    exact ⟨QuotientGroup.mk ⟨h₁, hh₁⟩, by simp [hh₂]⟩

/-- The equivalence between `H₁ ⧸ (H₁ ∩ gH₂g⁻¹)` and `{xH₂ | H₁xH₂ = H₁gH₂}`. -/
@[simps! apply]
noncomputable def toLeftDecompositionEquiv :
    LeftDecompQuotient H₁ H₂ g ≃ (mk H₁ H₂ g).LeftDecomposition :=
  (Equiv.ofInjective toLeftCoset toLeftCoset_injective).trans
    (Set.equivOfEq (by
      ext x
      rw [← QuotientGroup.out_eq' x, Set.mem_range, mem_range_toLeftCoset_iff,
        mem_LeftDecomposition_mk, eq_comm]))

end LeftDecompQuotient

end DoubleCoset
