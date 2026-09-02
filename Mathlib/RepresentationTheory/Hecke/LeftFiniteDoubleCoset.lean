/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index

/-!
# Double cosets admitting finite left-coset decomposition

This file introduces a finiteness condition `DoubleCoset.IsLeftFinite` on double cosets and its
bundled version `DoubleCoset₀`.

We begin by introducing two indexing types for the left-coset decomposition: the intrinsic
`LeftDecomposition` and the computational `LeftDecompQuotient`. They are equivalent via
`toLeftDecompositionEquiv`. The first `LeftDecomposition` is useful for coordinate-free definitions
and proofs, while the second `LeftDecompQuotient` carries a base point `gH₂` and remains useful for
concrete convolution product computation.

For a triple `(H₁, H₂, g)`, the property `DoubleCoset.IsLeftFinite H₁ H₂ g` says that the double
coset H₁gH₂ admits finite decomposition into left cosets, i.e. the set `{xH₂ | H₁xH₂ = H₁gH₂}` is
finite. The collection of all such double cosets is bundled into a type `DoubleCoset₀`, which allows
us to describe the intertwining space `Hom_G(k[G ⧸ H₁], k[G ⧸ H₂])` as the free module
`k[DoubleCoset₀ H₁ H₂]`.
-/

@[expose] public section

variable {G : Type*} [Group G] {H₁ H₂ H₃ : Subgroup G} {g g' : G}

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

section degree

variable (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G))

/-- The number of left cosets in `H₁gH₂`, which is set to `0` if there are infinitely many.
Alternatively, this is equal to `Nat.card H₁ ⧸ (H₁ ∩ gH₂g⁻¹)` where `g` is any representative of the
underlying double coset. -/
noncomputable def Quotient.degree : ℕ := Nat.card (LeftDecomposition x)

lemma degree_def :
    x.degree = Nat.card x.LeftDecomposition := rfl

lemma mk_degree (g : G) :
    (mk H₁ H₂ g).degree = Nat.card (LeftDecompQuotient H₁ H₂ g) := by
  rw [degree_def, Nat.card_eq_of_bijective _ LeftDecompQuotient.toLeftDecompositionEquiv.bijective]

end degree

section finite

variable (H₁ H₂ g) in
/-- A triple `(H₁, H₂, g)` is called `IsLeftFinite` if the double coset `H₁gH₂` has finite
decomposition into left cosets. -/
@[mk_iff] class IsLeftFinite : Prop where
  degreeNeZero : (DoubleCoset.mk H₁ H₂ g).degree ≠ 0

lemma isLeftFinite_iff_relIndexNeZero :
    IsLeftFinite H₁ H₂ g ↔ (ConjAct.toConjAct g • H₂).relIndex H₁ ≠ 0 := by
  rw [isLeftFinite_iff, mk_degree, LeftDecompQuotient, stabilizer_leftCoset, Subgroup.relIndex,
    Subgroup.index]

instance [IsLeftFinite H₁ H₂ g] : Finite (mk H₁ H₂ g).LeftDecomposition := by
  apply Nat.finite_of_card_ne_zero
  simpa [degree_def] using IsLeftFinite.degreeNeZero

noncomputable instance [IsLeftFinite H₁ H₂ g] : Fintype (LeftDecompQuotient H₁ H₂ g) := by
  simpa [LeftDecompQuotient] using
    Subgroup.fintypeOfIndexNeZero (isLeftFinite_iff_relIndexNeZero.mp (inferInstance))

instance instIsLeftFinite_diag_one (H : Subgroup G) : IsLeftFinite H H 1 := by
  simp [isLeftFinite_iff, mk_degree, LeftDecompQuotient]

instance instIsLeftFinite_mulLeft [IsLeftFinite H₁ H₂ g] (h₁ : H₁) :
    IsLeftFinite H₁ H₂ (h₁ * g) := by
  simp [isLeftFinite_iff, IsLeftFinite.degreeNeZero]

instance instIsLeftFinite_mulRight [IsLeftFinite H₁ H₂ g] (h₂ : H₂) :
    IsLeftFinite H₁ H₂ (g * h₂) := by
  simp [isLeftFinite_iff, IsLeftFinite.degreeNeZero]

variable (H₁ H₂ H₃ g g') in
lemma isLeftFinite_trans [IsLeftFinite H₁ H₂ g] [IsLeftFinite H₂ H₃ g'] :
    IsLeftFinite H₁ H₃ (g * g') := by
  have h₁₂ : ((ConjAct.toConjAct g) • H₂).relIndex H₁ ≠ 0 :=
    (isLeftFinite_iff_relIndexNeZero.mp inferInstance)
  have h₂₃ : ((ConjAct.toConjAct g) • ((ConjAct.toConjAct g') • H₃)).relIndex
      ((ConjAct.toConjAct g) • H₂) ≠ 0 := by
    simp [Subgroup.relIndex_pointwise_smul, isLeftFinite_iff_relIndexNeZero.mp]
  simpa [isLeftFinite_iff_relIndexNeZero, mul_smul] using Subgroup.relIndex_ne_zero_trans h₂₃ h₁₂

instance instIsLeftFinite_trans [IsLeftFinite H₁ H₂ g]
    [IsLeftFinite H₂ H₃ g'] (h₂ : H₂) : IsLeftFinite H₁ H₃ (g * h₂ * g') :=
  isLeftFinite_trans H₁ H₂ H₃ (g * h₂) g'

end finite

end DoubleCoset

variable (H₁ H₂) in
/-- The collection of double cosets admitting finite decomposition into left cosets. -/
@[implicit_reducible]
def DoubleCoset₀ := {x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G) // x.degree ≠ 0}

instance : Coe (DoubleCoset₀ H₁ H₂) (DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :=
  ⟨Subtype.val⟩

namespace DoubleCoset₀

/-- The Hecke double coset represented by `g`. -/
abbrev mk (H₁ H₂ : Subgroup G) (g : G) [IsLeftFinite H₁ H₂ g] :
    DoubleCoset₀ H₁ H₂ := ⟨DoubleCoset.mk H₁ H₂ g, IsLeftFinite.degreeNeZero⟩

/-- A representative of the underlying double coset in the ambient group. -/
noncomputable def rep (x : DoubleCoset₀ H₁ H₂) : G := x.val.out

/-- The cardinality of left cosets in `H₁gH₂`. This is equal to `Nat.card H₁ ⧸ (H₁ ∩ gH₂g⁻¹)` where
`g` is some representative of the underlying double coset. -/
noncomputable abbrev degree (x : DoubleCoset₀ H₁ H₂) : ℕ := x.val.degree

/-- Given `x : DoubleCoset₀ H₁ H₂`, the finite set of left cosets `{gH₂ | H₁gH₂ = x}`. -/
abbrev LeftDecomposition (x : DoubleCoset₀ H₁ H₂) : Set (G ⧸ H₂) := x.val.LeftDecomposition

@[simp]
lemma degree_ne_zero (x : DoubleCoset₀ H₁ H₂) :
    x.degree ≠ 0 := x.prop

instance (x : DoubleCoset₀ H₁ H₂) : Finite x.LeftDecomposition := by
  apply Nat.finite_of_card_ne_zero
  simpa [degree_def] using x.2

instance (x : DoubleCoset₀ H₁ H₂) : IsLeftFinite H₁ H₂ x.rep := by
  simp [isLeftFinite_iff, rep, DoubleCoset.out_eq']

lemma coe_mk (g : G) [IsLeftFinite H₁ H₂ g] :
    (mk H₁ H₂ g : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) = DoubleCoset.mk H₁ H₂ g := rfl

@[simp]
lemma mk_rep (x : DoubleCoset₀ H₁ H₂) :
    mk H₁ H₂ x.rep = x := by
  simp [mk, DoubleCoset.out_eq', rep]

@[simp]
lemma mk_rep_eq_val (x : DoubleCoset₀ H₁ H₂) :
    DoubleCoset.mk H₁ H₂ x.rep = x.val := by
  simp [DoubleCoset.out_eq', rep]

lemma mk_degree [IsLeftFinite H₁ H₂ g] :
    (mk H₁ H₂ g).degree = Nat.card (LeftDecompQuotient H₁ H₂ g) := by
  simpa using DoubleCoset.mk_degree g (H₁ := H₁) (H₂ := H₂)

lemma mk_eq_iff {g g' : G} [IsLeftFinite H₁ H₂ g] [IsLeftFinite H₁ H₂ g'] :
    mk H₁ H₂ g = mk H₁ H₂ g' ↔ ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g' = h₁ * g * h₂ := by
  rw [Subtype.ext_iff, DoubleCoset.eq]

@[simp]
lemma mk_mul_mem [IsLeftFinite H₁ H₂ g] (h₁ : H₁) :
    mk H₁ H₂ (h₁ * g) = mk H₁ H₂ g := by
  simp [mk]

@[simp]
lemma mk_mem_mul [IsLeftFinite H₁ H₂ g] (h₂ : H₂) :
    mk H₁ H₂ (g * h₂) = mk H₁ H₂ g := by
  simp [mk]

@[simp]
lemma diag_mk_one_rep_mem (H : Subgroup G) : (mk H H 1).rep ∈ H := by
  obtain ⟨_, h₁, _, h₂, heq⟩ := mk_eq_iff.mp (show mk H H 1 = mk H H (mk H H 1).rep from by simp)
  simp [heq, H.mul_mem h₁ h₂]

@[simp]
lemma diag_mk_one_degree_eq_one (H : Subgroup G) : (mk H H 1).degree = 1 := by
  simp [mk_degree, LeftDecompQuotient]

end DoubleCoset₀
