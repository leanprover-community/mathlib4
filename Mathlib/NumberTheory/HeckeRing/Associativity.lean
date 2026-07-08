/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.NumberTheory.HeckeRing.One

/-!
# Hecke rings: associativity

Associativity of the convolution product of Hecke coset modules, in the mixed-level generality
`HeckeCosetModule Δ H₁ H₂ R × HeckeCosetModule Δ H₂ H₃ R × HeckeCosetModule Δ H₃ H₄ R`, following
Proposition 3.2 of [Shimura][shimura1971]. The combinatorial input is the invariance of Shimura's
multiplicity
`m(g, h; d)` in `d` under the double coset of `d`: both associations of a triple product then
count the triples of representatives `(σᵢ, τⱼ, υₖ)` with `σᵢ g₁ τⱼ g₂ υₖ g₃ Γ₄ = d Γ₄`, and the
two bookkeepings are matched through the one-sided description of the multiplicity
(`multiplicity_eq_card_filter`).

## Main results

* `DoubleCoset.multiplicity_eq_card_filter`: `m(g, h; d)` counts the `σᵢ` with
  `(σᵢg)⁻¹d ∈ Γ₂hΓ₃`.
* `DoubleCoset.multiplicity_doubleCoset_congr`: `m(g, h; d)` depends on `d` only through the
  double coset `Γ₁dΓ₃`.
* `HeckeCosetModule.mul_assoc'`: associativity of the convolution product at mixed levels.
* the `Semiring (𝕋 Δ H R)` instance.
-/

@[expose] public section

open Subgroup DoubleCoset Finsupp
open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ₁ Γ₂ Γ₃ : Subgroup G}

/-- Splitting the count of a set of pairs along the first coordinate. -/
private lemma nat_card_prod_setOf {A B : Type*} [Fintype A] [Finite B] (P : A × B → Prop) :
    Nat.card {p : A × B | P p} = ∑ a : A, Nat.card {b : B | P (a, b)} :=
  calc Nat.card {p : A × B | P p}
      = Nat.card (Σ a : A, {b : B | P (a, b)}) :=
        Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b ↦ P (a, b))
    _ = ∑ a : A, Nat.card {b : B | P (a, b)} := Nat.card_sigma

open Classical in
/-- Counting a set as a sum of indicators. -/
private lemma nat_card_setOf_eq_sum {A : Type*} [Fintype A] (P : A → Prop) :
    Nat.card {a : A | P a} = ∑ a : A, if P a then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp [Set.mem_setOf_eq]

/-- Membership in a double coset is invariant under left multiplication by the left
subgroup. -/
private lemma mul_mem_doubleCoset_iff {β : G} (hβ : β ∈ Γ₂) {a z : G} :
    β * z ∈ doubleCoset a Γ₂ Γ₃ ↔ z ∈ doubleCoset a Γ₂ Γ₃ := by
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp hz
    refine mem_doubleCoset.mpr ⟨β⁻¹ * x, Γ₂.mul_mem (Γ₂.inv_mem hβ) hx, y, hy, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc x, ← hxy, inv_mul_cancel_left]
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.mp hz
    exact mem_doubleCoset.mpr ⟨β * x, Γ₂.mul_mem hβ hx, y, hy, by
      simp only [mul_assoc]⟩

open Classical in
/-- The fibre of the multiplicity over a fixed first representative: for fixed `w`, there is
exactly one representative `τⱼ` with `w τⱼ h Γ₃ = d Γ₃` if `w⁻¹d ∈ Γ₂hΓ₃`, and none
otherwise. -/
lemma nat_card_fiber (Γ₂ Γ₃ : Subgroup G) (h w d : G) :
    Nat.card {j : DecompQuotient Γ₂ Γ₃ h | (w * ((j.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)} =
      if w⁻¹ * d ∈ doubleCoset h Γ₂ Γ₃ then 1 else 0 := by
  have hcond : ∀ j : DecompQuotient Γ₂ Γ₃ h,
      ((w * ((j.out : G) * h) : G) : G ⧸ Γ₃) = (d : G ⧸ Γ₃) ↔
        (((j.out : G) * h : G) : G ⧸ Γ₃) = ((w⁻¹ * d : G) : G ⧸ Γ₃) := by
    intro j
    simp only [QuotientGroup.eq, mul_inv_rev, mul_assoc]
  split_ifs with hd
  · rw [Nat.card_eq_one_iff_unique]
    constructor
    · exact ⟨fun j₁ j₂ ↦ Subtype.ext (mk_out_mul_injective Γ₂ Γ₃ h
        (((hcond _).mp j₁.2).trans ((hcond _).mp j₂.2).symm))⟩
    · rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hd
      obtain ⟨j, hj⟩ := hd
      rw [mem_leftCoset_iff] at hj
      exact ⟨⟨j, (hcond j).mpr (QuotientGroup.eq.mpr hj)⟩⟩
  · have : IsEmpty {j : DecompQuotient Γ₂ Γ₃ h |
        (w * ((j.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)} := by
      rw [Set.isEmpty_coe_sort, Set.eq_empty_iff_forall_notMem]
      intro j hj
      have hj' := QuotientGroup.eq.mp ((hcond j).mp hj)
      exact hd (mem_doubleCoset.mpr ⟨j.out, j.out.2, _, hj', by
        rw [mul_inv_cancel_left]⟩)
    rw [Nat.card_of_isEmpty]

/-- Shimura's multiplicity as a one-sided count: the second component of a pair in the fibre
is determined by the first, so `m(g, h; d)` counts the representatives `σᵢ` with
`(σᵢg)⁻¹d ∈ Γ₂hΓ₃`. -/
theorem multiplicity_eq_card_filter (g h d : G) [Finite (DecompQuotient Γ₁ Γ₂ g)]
    [Finite (DecompQuotient Γ₂ Γ₃ h)] :
    multiplicity Γ₁ Γ₂ Γ₃ g h d =
      Nat.card {i : DecompQuotient Γ₁ Γ₂ g | ((i.out : G) * g)⁻¹ * d ∈ doubleCoset h Γ₂ Γ₃} := by
  classical
  have : Fintype (DecompQuotient Γ₁ Γ₂ g) := Fintype.ofFinite _
  have step1 : Nat.card {p : DecompQuotient Γ₁ Γ₂ g × DecompQuotient Γ₂ Γ₃ h |
      ((p.1.out : G) * g * ((p.2.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)} =
      ∑ i : DecompQuotient Γ₁ Γ₂ g, Nat.card {j : DecompQuotient Γ₂ Γ₃ h |
        ((i.out : G) * g * ((j.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)} := by
    exact nat_card_prod_setOf _
  rw [multiplicity, step1, nat_card_setOf_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [nat_card_fiber Γ₂ Γ₃ h ((i.out : G) * g) d]

/-- Shimura's multiplicity is invariant under left translation of the target by `Γ₁`. -/
theorem multiplicity_mul_left {γ : G} (hγ : γ ∈ Γ₁) (g h d : G)
    [Finite (DecompQuotient Γ₁ Γ₂ g)] [Finite (DecompQuotient Γ₂ Γ₃ h)] :
    multiplicity Γ₁ Γ₂ Γ₃ g h (γ * d) = multiplicity Γ₁ Γ₂ Γ₃ g h d := by
  rw [multiplicity_eq_card_filter, multiplicity_eq_card_filter]
  set γ' : Γ₁ := ⟨γ, hγ⟩ with hγ'def
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm γ'⁻¹) fun i ↦ ?_)
  simp only [Set.mem_setOf_eq, MulAction.toPerm_apply]
  have h1 : QuotientGroup.mk (γ'⁻¹ * i.out) = γ'⁻¹ • i := by
    rw [← smul_eq_mul]
    exact MulAction.Quotient.mk_smul_out _ γ'⁻¹ i
  have hk : (γ'⁻¹ * i.out)⁻¹ * (γ'⁻¹ • i).out ∈
      (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁ :=
    QuotientGroup.eq.mp (h1.trans (QuotientGroup.out_eq' _).symm)
  have hβ : g⁻¹ * ((((γ'⁻¹ * i.out)⁻¹ * (γ'⁻¹ • i).out : Γ₁) : G)) * g ∈ Γ₂ :=
    Subgroup.mem_conjAct_pointwise_smul_iff.mp (Subgroup.mem_subgroupOf.mp hk)
  have hy : ((γ'⁻¹ • i).out : G) =
      γ⁻¹ * (i.out : G) * (((γ'⁻¹ * i.out)⁻¹ * (γ'⁻¹ • i).out : Γ₁) : G) := by
    rw [show γ⁻¹ * (i.out : G) = ((γ'⁻¹ * i.out : Γ₁) : G) from rfl, ← Subgroup.coe_mul,
      mul_inv_cancel_left]
  have hcalc : (((γ'⁻¹ • i).out : G) * g)⁻¹ * d =
      (g⁻¹ * ((((γ'⁻¹ * i.out)⁻¹ * (γ'⁻¹ • i).out : Γ₁) : G)) * g)⁻¹ *
        (((i.out : G) * g)⁻¹ * (γ * d)) := by
    rw [hy]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [hcalc, mul_mem_doubleCoset_iff (Γ₂.inv_mem hβ)]

/-- Shimura's multiplicity is invariant under right translation of the target by `Γ₃`. -/
theorem multiplicity_mul_right {γ : G} (hγ : γ ∈ Γ₃) (g h d : G) :
    multiplicity Γ₁ Γ₂ Γ₃ g h (d * γ) = multiplicity Γ₁ Γ₂ Γ₃ g h d := by
  simp only [multiplicity, QuotientGroup.mk_mul_of_mem d hγ]

/-- Shimura's multiplicity depends on the target only through its double coset. -/
theorem multiplicity_doubleCoset_congr (g h : G) {d d' : G}
    (hd : d' ∈ doubleCoset d Γ₁ Γ₃) [Finite (DecompQuotient Γ₁ Γ₂ g)]
    [Finite (DecompQuotient Γ₂ Γ₃ h)] :
    multiplicity Γ₁ Γ₂ Γ₃ g h d' = multiplicity Γ₁ Γ₂ Γ₃ g h d := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.mp hd
  rw [mul_assoc, multiplicity_mul_left hx, multiplicity_mul_right hy]

end DoubleCoset

namespace HeckeCoset

open DoubleCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ H₃ H₄ : Subgroup G}

open Classical in
/-- Summing the multiplicities of the double cosets in the support of a product against the
indicator of containing a fixed element recovers the multiplicity of that element: the double
cosets in the support are pairwise disjoint, each contributing its (constant) multiplicity, and
elements outside every double coset of the support have multiplicity zero. -/
private lemma sum_ite_mem_multiplicity [IsHeckeTriple Δ H₂ H₃] [IsHeckeTriple Δ H₃ H₄]
    [DecidableEq (HeckeCoset Δ H₂ H₄)] (g₂ g₃ : Δ) (x : G) :
    ∑ F ∈ Finset.univ.image (mulMap H₂ H₃ H₄ g₂ g₃),
        (if x ∈ doubleCoset (F.rep : G) H₂ H₄ then
          multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) (F.rep : G) else 0) =
      multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) x := by
  by_cases hx : ∃ F₀ ∈ Finset.univ.image (mulMap H₂ H₃ H₄ g₂ g₃),
      x ∈ doubleCoset (F₀.rep : G) H₂ H₄
  · obtain ⟨F₀, hF₀, hxF₀⟩ := hx
    rw [Finset.sum_eq_single_of_mem F₀ hF₀ fun F hF hne ↦ if_neg fun hxF ↦
      hne (HeckeCoset.toSet_injective (by
        rw [HeckeCoset.toSet_eq_doubleCoset_rep, HeckeCoset.toSet_eq_doubleCoset_rep,
          ← doubleCoset_eq_of_mem hxF, ← doubleCoset_eq_of_mem hxF₀])),
      if_pos hxF₀]
    exact (multiplicity_doubleCoset_congr _ _ hxF₀).symm
  · simp only [not_exists, not_and] at hx
    rw [Finset.sum_eq_zero fun F hF ↦ if_neg (hx F hF)]
    by_contra h0
    have hne : multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) x ≠ 0 := fun hh ↦ h0 hh.symm
    obtain ⟨w, hw, y, hy, rfl⟩ := mem_doubleCoset.mp (multiplicity_ne_zero_iff.mp hne)
    obtain ⟨β, hβ, c, hc, rfl⟩ := mem_doubleCoset.mp hw
    have hxΔ : β * (g₂ : G) * c * (g₃ : G) * y ∈ Δ :=
      Δ.mul_mem (Δ.mul_mem (Δ.mul_mem (Δ.mul_mem (IsHeckeTriple.mem_of_mem_left H₃ hβ) g₂.2)
        (IsHeckeTriple.mem_of_mem_left H₄ hc)) g₃.2) (IsHeckeTriple.mem_of_mem_right H₃ hy)
    set xΔ : Δ := ⟨β * (g₂ : G) * c * (g₃ : G) * y, hxΔ⟩
    have hrep : ((HeckeCoset.mk H₂ H₄ xΔ).rep : G) ∈ doubleCoset (xΔ : G) H₂ H₄ := by
      have h1 := HeckeCoset.rep_mem (HeckeCoset.mk H₂ H₄ xΔ)
      rwa [HeckeCoset.toSet_mk] at h1
    refine hx (HeckeCoset.mk H₂ H₄ xΔ) ?_ ?_
    · rw [HeckeCoset.mem_image_mulMap_iff, multiplicity_doubleCoset_congr _ _ hrep]
      exact hne
    · rw [doubleCoset_eq_of_mem hrep]
      exact mem_doubleCoset_self H₂ H₄ _

open Classical in
/-- The right-handed Fubini step: summing the structure constants against a further
multiplicity over the double cosets of the product `H₂g₂H₃g₃H₄` counts, for each representative
`σᵢ` of `H₁g₁H₂`, the multiplicity of `(σᵢg₁)⁻¹d`. -/
lemma sum_image_mulMap_multiplicity_right [IsHeckeTriple Δ H₁ H₂]
    [IsHeckeTriple Δ H₂ H₃] [IsHeckeTriple Δ H₃ H₄]
    [DecidableEq (HeckeCoset Δ H₂ H₄)] (g₁ g₂ g₃ d : Δ) :
    ∑ F ∈ Finset.univ.image (mulMap H₂ H₃ H₄ g₂ g₃),
        multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) (F.rep : G) *
          multiplicity H₁ H₂ H₄ (g₁ : G) (F.rep : G) (d : G) =
      ∑ i : DecompQuotient H₁ H₂ (g₁ : G),
        multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) (((i.out : G) * g₁)⁻¹ * d) := by
  haveI : IsHeckeTriple Δ H₂ H₄ := IsHeckeTriple.trans (H₂ := H₃)
  have hstep : ∀ F ∈ Finset.univ.image (mulMap H₂ H₃ H₄ g₂ g₃),
      multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) (F.rep : G) *
        multiplicity H₁ H₂ H₄ (g₁ : G) (F.rep : G) (d : G) =
      ∑ i : DecompQuotient H₁ H₂ (g₁ : G),
        (if ((i.out : G) * g₁)⁻¹ * d ∈ doubleCoset (F.rep : G) H₂ H₄ then
          multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) (F.rep : G) else 0) := by
    intro F _
    rw [multiplicity_eq_card_filter (Γ₁ := H₁) (g₁ : G) (F.rep : G) (d : G),
      nat_card_setOf_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ sum_ite_mem_multiplicity g₂ g₃ _

/-- Joining the right-handed Fubini step with the one-sided count: the right association counts
pairs of representatives whose product moves `d` into `H₃g₃H₄`. -/
lemma sum_multiplicity_eq_card [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    [IsHeckeTriple Δ H₃ H₄] (g₁ g₂ g₃ d : Δ) :
    ∑ i : DecompQuotient H₁ H₂ (g₁ : G),
        multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) (((i.out : G) * g₁)⁻¹ * d) =
      Nat.card {p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G) |
        ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂))⁻¹ * d ∈ doubleCoset (g₃ : G) H₃ H₄} := by
  classical
  have step : Nat.card {p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G) |
      ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂))⁻¹ * d ∈ doubleCoset (g₃ : G) H₃ H₄} =
      ∑ i : DecompQuotient H₁ H₂ (g₁ : G), Nat.card {j : DecompQuotient H₂ H₃ (g₂ : G) |
        ((i.out : G) * g₁ * ((j.out : G) * g₂))⁻¹ * d ∈ doubleCoset (g₃ : G) H₃ H₄} := by
    exact nat_card_prod_setOf _
  rw [step]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [multiplicity_eq_card_filter (Γ₁ := H₂) (g₂ : G) (g₃ : G) (((i.out : G) * g₁)⁻¹ * d)]
  exact Nat.card_congr (Equiv.setCongr (by
    ext j
    simp only [Set.mem_setOf_eq, mul_inv_rev, mul_assoc]))

open Classical in
/-- The left-handed Fubini step: the left association also counts pairs of representatives
whose product moves `d` into `H₃g₃H₄`, using the invariance of the multiplicity across the
left cosets of a double coset. -/
lemma sum_image_mulMap_multiplicity_left [IsHeckeTriple Δ H₁ H₂]
    [IsHeckeTriple Δ H₂ H₃] [IsHeckeTriple Δ H₃ H₄]
    [DecidableEq (HeckeCoset Δ H₁ H₃)] (g₁ g₂ g₃ d : Δ) :
    ∑ E ∈ Finset.univ.image (mulMap H₁ H₂ H₃ g₁ g₂),
        multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (E.rep : G) *
          multiplicity H₁ H₃ H₄ (E.rep : G) (g₃ : G) (d : G) =
      Nat.card {p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G) |
        ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂))⁻¹ * d ∈ doubleCoset (g₃ : G) H₃ H₄} := by
  haveI h13 : IsHeckeTriple Δ H₁ H₃ := IsHeckeTriple.trans (H₂ := H₂)
  have hA : ∀ E ∈ Finset.univ.image (mulMap H₁ H₂ H₃ g₁ g₂),
      multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (E.rep : G) *
        multiplicity H₁ H₃ H₄ (E.rep : G) (g₃ : G) (d : G) =
      ∑ l : DecompQuotient H₁ H₃ (E.rep : G),
        ∑ p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G),
          if (((l.out : G) * E.rep)⁻¹ * d ∈ doubleCoset (g₃ : G) H₃ H₄) ∧
              ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂) : G ⧸ H₃) =
                (((l.out : G) * E.rep : G) : G ⧸ H₃) then 1 else 0 := by
    intro E _
    rw [multiplicity_eq_card_filter (Γ₁ := H₁) (E.rep : G) (g₃ : G) (d : G),
      nat_card_setOf_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [mul_ite, mul_one, mul_zero]
    split_ifs with hcond
    · rw [show multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (E.rep : G) =
          multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) ((l.out : G) * E.rep) from
          (multiplicity_mul_left l.out.2 _ _ _).symm,
        multiplicity, nat_card_setOf_eq_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      by_cases hm : ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂) : G ⧸ H₃) =
          (((l.out : G) * E.rep : G) : G ⧸ H₃)
      · rw [if_pos hm, if_pos ⟨hcond, hm⟩]
      · rw [if_neg hm, if_neg fun hh ↦ hm hh.2]
    · exact (Finset.sum_eq_zero fun p _ ↦ if_neg fun hh ↦ hcond hh.1).symm
  rw [Finset.sum_congr rfl hA,
    Finset.sum_congr rfl fun (E : HeckeCoset Δ H₁ H₃) _ ↦ Finset.sum_comm, Finset.sum_comm,
    nat_card_setOf_eq_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  -- Step E: for each pair `p` there is exactly one pair `(E, l)` matching the coset of the
  -- product of the representatives of `p`.
  set wG : G := (p.1.out : G) * g₁ * ((p.2.out : G) * g₂) with hwG
  have hwΔ : wG ∈ Δ :=
    Δ.mul_mem (Δ.mul_mem (IsHeckeTriple.mem_of_mem_left H₂ p.1.out.2) g₁.2)
      (Δ.mul_mem (IsHeckeTriple.mem_of_mem_left H₃ p.2.out.2) g₂.2)
  set E₀ : HeckeCoset Δ H₁ H₃ := HeckeCoset.mk H₁ H₃ ⟨wG, hwΔ⟩ with hE₀def
  have hE₀mem : E₀ ∈ Finset.univ.image (mulMap H₁ H₂ H₃ g₁ g₂) :=
    Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  have hw_rep : wG ∈ doubleCoset ((E₀.rep : Δ) : G) H₁ H₃ := by
    have h1 := HeckeCoset.rep_mem E₀
    rw [hE₀def, HeckeCoset.toSet_mk] at h1
    rw [doubleCoset_eq_of_mem h1]
    exact mem_doubleCoset_self H₁ H₃ _
  have hdec := hw_rep
  rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hdec
  obtain ⟨l₀, hl₀⟩ := hdec
  rw [mem_leftCoset_iff] at hl₀
  have hmk : ((wG : G) : G ⧸ H₃) = (((l₀.out : G) * (E₀.rep : G) : G) : G ⧸ H₃) :=
    (QuotientGroup.eq.mpr hl₀).symm
  rw [Finset.sum_eq_single_of_mem E₀ hE₀mem ?hEne]
  case hEne =>
    intro E hE hne
    refine Finset.sum_eq_zero fun l _ ↦ if_neg ?_
    rintro ⟨-, hmatch⟩
    have hwE : wG ∈ doubleCoset ((E.rep : Δ) : G) H₁ H₃ := by
      have h2 := QuotientGroup.eq.mp hmatch
      refine mem_doubleCoset.mpr ⟨(l.out : G), l.out.2, ((l.out : G) * E.rep)⁻¹ * wG,
        by simpa [mul_inv_rev, mul_assoc] using H₃.inv_mem h2, (mul_inv_cancel_left _ _).symm⟩
    refine hne (HeckeCoset.toSet_injective ?_)
    rw [HeckeCoset.toSet_eq_doubleCoset_rep, hE₀def, HeckeCoset.toSet_mk]
    exact (doubleCoset_eq_of_mem hwE).symm
  rw [Finset.sum_eq_single_of_mem l₀ (Finset.mem_univ _) ?hlne]
  case hlne =>
    intro l _ hlne
    refine if_neg ?_
    rintro ⟨-, hmatch⟩
    exact hlne (mk_out_mul_injective H₁ H₃ ((E₀.rep : Δ) : G) (hmatch.symm.trans hmk))
  have hiff : ((((l₀.out : G) * (E₀.rep : G))⁻¹ * d ∈ doubleCoset (g₃ : G) H₃ H₄) ∧
      ((wG : G) : G ⧸ H₃) = (((l₀.out : G) * (E₀.rep : G) : G) : G ⧸ H₃)) ↔
      (wG⁻¹ * (d : G) ∈ doubleCoset (g₃ : G) H₃ H₄) := by
    have hw2 : wG⁻¹ * (d : G) =
        (((l₀.out : G) * (E₀.rep : G))⁻¹ * wG)⁻¹ *
          ((((l₀.out : G) * (E₀.rep : G)))⁻¹ * d) := by
      simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    constructor
    · intro hh
      rw [hw2, mul_mem_doubleCoset_iff (H₃.inv_mem hl₀)]
      exact hh.1
    · intro hh
      refine ⟨?_, hmk⟩
      rw [hw2, mul_mem_doubleCoset_iff (H₃.inv_mem hl₀)] at hh
      exact hh
  by_cases hd4 : wG⁻¹ * (d : G) ∈ doubleCoset (g₃ : G) H₃ H₄
  · rw [if_pos (hiff.mpr hd4), if_pos hd4]
  · rw [if_neg fun hh ↦ hd4 (hiff.mp hh), if_neg hd4]

/-- Associativity of the structure constants of the Hecke product (Proposition 3.2 of
[Shimura][shimura1971]): both associations of a triple product of double cosets have the same
structure constants. -/
theorem sum_multiplicity_assoc [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    [IsHeckeTriple Δ H₃ H₄] [DecidableEq (HeckeCoset Δ H₁ H₃)]
    [DecidableEq (HeckeCoset Δ H₂ H₄)] (g₁ g₂ g₃ d : Δ) :
    ∑ E ∈ Finset.univ.image (mulMap H₁ H₂ H₃ g₁ g₂),
        multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (E.rep : G) *
          multiplicity H₁ H₃ H₄ (E.rep : G) (g₃ : G) (d : G) =
      ∑ F ∈ Finset.univ.image (mulMap H₂ H₃ H₄ g₂ g₃),
        multiplicity H₂ H₃ H₄ (g₂ : G) (g₃ : G) (F.rep : G) *
          multiplicity H₁ H₂ H₄ (g₁ : G) (F.rep : G) (d : G) := by
  rw [sum_image_mulMap_multiplicity_left g₁ g₂ g₃ d,
    sum_image_mulMap_multiplicity_right g₁ g₂ g₃ d, sum_multiplicity_eq_card g₁ g₂ g₃ d]

end HeckeCoset

namespace HeckeCosetModule

open DoubleCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ H₃ H₄ : Subgroup G}
  (R : Type*) [Semiring R]

open Classical in
/-- The support of the structure constants is contained in the image of `mulMap`. -/
private lemma support_structureConstants_subset [IsHeckeTriple Δ H₁ H₂]
    [IsHeckeTriple Δ H₂ H₃] (g₁ g₂ : Δ) :
    (structureConstants R H₁ H₂ H₃ g₁ g₂).support ⊆
      Finset.univ.image (HeckeCoset.mulMap H₁ H₂ H₃ g₁ g₂) :=
  Finsupp.support_onFinset_subset

/-- `Finsupp.sum_smul_index`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R`. -/
private lemma sum_smul_index_T {N : Type*} [AddCommMonoid N] (a : R)
    (f : HeckeCosetModule Δ H₁ H₂ R) (F : HeckeCoset Δ H₁ H₂ → R → N) (h0 : ∀ D, F D 0 = 0) :
    (a • f).sum F = f.sum fun D c ↦ F D (a * c) :=
  Finsupp.sum_smul_index h0

/-- `Finsupp.smul_apply`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R`. -/
private lemma smul_apply_T (a : R) (f : HeckeCosetModule Δ H₁ H₂ R) (D : HeckeCoset Δ H₁ H₂) :
    (a • f) D = a * f D :=
  rfl

/-- Unfolding `Finsupp.sum` with the wrapper-type coercion. -/
private lemma sum_eq_sum_T {N : Type*} [AddCommMonoid N] (f : HeckeCosetModule Δ H₁ H₂ R)
    (F : HeckeCoset Δ H₁ H₂ → R → N) : f.sum F = ∑ D ∈ f.support, F D (f D) :=
  rfl

/-- `Finsupp.notMem_support_iff`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R`. -/
private lemma apply_eq_zero_of_notMem_support_T (f : HeckeCosetModule Δ H₁ H₂ R)
    (D : HeckeCoset Δ H₁ H₂) (h : D ∉ f.support) : f D = 0 :=
  Finsupp.notMem_support_iff.mp h

/-- `Finsupp.zero_apply`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R`. -/
private lemma zero_apply_T (D : HeckeCoset Δ H₁ H₂) : (0 : HeckeCosetModule Δ H₁ H₂ R) D = 0 :=
  rfl

/-- `Finsupp.sum_apply`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R`. -/
private lemma sum_apply_T {H₁ H₂ H₃ H₄ : Subgroup G} (f : HeckeCosetModule Δ H₁ H₂ R)
    (F : HeckeCoset Δ H₁ H₂ → R → HeckeCosetModule Δ H₃ H₄ R) (D : HeckeCoset Δ H₃ H₄) :
    (f.sum F) D = f.sum fun E c ↦ F E c D :=
  Finsupp.sum_apply

/-- The convolution product commutes with scalar multiplication on the left factor. (Note
that the corresponding statement for the right factor fails over a noncommutative `R`.) -/
lemma smul_mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃] (a : R)
    (f : HeckeCosetModule Δ H₁ H₂ R) (g : HeckeCosetModule Δ H₂ H₃ R) :
    mul R (a • f) g = a • mul R f g := by
  rw [mul_eq_sum, mul_eq_sum, sum_smul_index_T R a f _ fun D₁ ↦ by simp,
    Finsupp.sum, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun D₁ _ ↦ ?_
  rw [Finsupp.sum, Finsupp.sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun D₂ _ ↦ by rw [mul_smul]

/-- Evaluation of the convolution product against a basis element on the left. -/
lemma single_mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (D₁ : HeckeCoset Δ H₁ H₂) (b₁ : R) (g : HeckeCosetModule Δ H₂ H₃ R) :
    mul R (single R D₁ b₁) g =
      g.sum fun D₂ b₂ ↦ b₁ • b₂ • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep := by
  rw [mul_eq_sum, single]
  exact Finsupp.sum_single_index (by simp)

/-- Evaluation of the convolution product against a basis element on the right. -/
lemma mul_single [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (D₂ : HeckeCoset Δ H₂ H₃) (b₂ : R) :
    mul R f (single R D₂ b₂) =
      f.sum fun D₁ b₁ ↦ b₁ • b₂ • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep := by
  rw [mul_eq_sum]
  exact Finsupp.sum_congr fun D₁ _ ↦ Finsupp.sum_single_index (by simp)

/-- `Finsupp.induction_linear`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R` so
that the hypotheses match the `HeckeCosetModule` vocabulary. -/
private lemma induction_linear {p : HeckeCosetModule Δ H₁ H₂ R → Prop}
    (f : HeckeCosetModule Δ H₁ H₂ R) (h0 : p 0)
    (hadd : ∀ f g : HeckeCosetModule Δ H₁ H₂ R, p f → p g → p (f + g))
    (hsingle : ∀ (D : HeckeCoset Δ H₁ H₂) (b : R), p (single R D b)) : p f :=
  Finsupp.induction_linear f h0 hadd hsingle

/-- Associativity of the convolution product of Hecke coset modules, at mixed levels
(Proposition 3.2 of [Shimura][shimura1971]). -/
theorem mul_assoc' [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    [IsHeckeTriple Δ H₃ H₄] [IsHeckeTriple Δ H₁ H₃] [IsHeckeTriple Δ H₂ H₄]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g : HeckeCosetModule Δ H₂ H₃ R)
    (h : HeckeCosetModule Δ H₃ H₄ R) :
    mul R (mul R f g) h = mul R f (mul R g h) := by
  classical
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp only [HeckeCosetModule.zero_mul]
  | hadd f₁ f₂ h₁ h₂ => simp only [HeckeCosetModule.add_mul, h₁, h₂]
  | hsingle D₁ b₁ =>
    induction g using HeckeCosetModule.induction_linear with
    | h0 => simp only [HeckeCosetModule.zero_mul, HeckeCosetModule.mul_zero]
    | hadd g₁ g₂ h₁ h₂ =>
      simp only [HeckeCosetModule.mul_add, HeckeCosetModule.add_mul, h₁, h₂]
    | hsingle D₂ b₂ =>
      induction h using HeckeCosetModule.induction_linear with
      | h0 => simp only [HeckeCosetModule.mul_zero]
      | hadd h₁ h₂ hh₁ hh₂ => simp only [HeckeCosetModule.mul_add, hh₁, hh₂]
      | hsingle D₃ b₃ =>
        rw [mul_single_single R D₁ D₂ b₁ b₂, smul_mul, smul_mul, mul_single,
          mul_single_single R D₂ D₃ b₂ b₃, single_mul,
          sum_smul_index_T R b₂ _ _ fun F ↦ by simp,
          sum_smul_index_T R b₃ _ _ fun F ↦ by simp]
        ext D
        rw [smul_apply_T, smul_apply_T, sum_apply_T, sum_apply_T, sum_eq_sum_T, sum_eq_sum_T,
          Finset.sum_subset (support_structureConstants_subset R D₁.rep D₂.rep)
            (fun E _ hE ↦ by
              simp [apply_eq_zero_of_notMem_support_T _ _ _ hE, zero_apply_T]),
          Finset.sum_subset (support_structureConstants_subset R D₂.rep D₃.rep)
            (fun F _ hF ↦ by
              simp [apply_eq_zero_of_notMem_support_T _ _ _ hF, zero_apply_T])]
        simp only [smul_apply_T, structureConstants_apply]
        have hL : ∀ E : HeckeCoset Δ H₁ H₃,
            ((multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (E.rep : G) : R) *
              (b₃ * (multiplicity H₁ H₃ H₄ (E.rep : G) (D₃.rep : G) (D.rep : G) : R))) =
            b₃ * ((multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (E.rep : G) *
              multiplicity H₁ H₃ H₄ (E.rep : G) (D₃.rep : G) (D.rep : G) : ℕ) : R) := by
          intro E
          rw [(Nat.cast_commute (multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (E.rep : G))
            b₃).left_comm, Nat.cast_mul]
        have hR : ∀ F : HeckeCoset Δ H₂ H₄,
            (b₁ * ((b₂ * (b₃ * (multiplicity H₂ H₃ H₄ (D₂.rep : G) (D₃.rep : G) (F.rep : G) :
              R))) * (multiplicity H₁ H₂ H₄ (D₁.rep : G) (F.rep : G) (D.rep : G) : R))) =
            b₁ * (b₂ * (b₃ * ((multiplicity H₂ H₃ H₄ (D₂.rep : G) (D₃.rep : G) (F.rep : G) *
              multiplicity H₁ H₂ H₄ (D₁.rep : G) (F.rep : G) (D.rep : G) : ℕ) : R))) := by
          intro F
          rw [Nat.cast_mul, mul_assoc, mul_assoc]
        rw [Finset.sum_congr rfl fun E _ ↦ hL E, Finset.sum_congr rfl fun F _ ↦ hR F,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Nat.cast_sum, ← Nat.cast_sum]
        exact congrArg (fun n : ℕ ↦ b₁ * (b₂ * (b₃ * (n : R))))
          (HeckeCoset.sum_multiplicity_assoc D₁.rep D₂.rep D₃.rep D.rep)

/-- The Hecke ring is a semiring: the convolution product is associative. -/
noncomputable instance {H : Subgroup G} [IsHeckeTriple Δ H H] : Semiring (𝕋 Δ H R) :=
  { (inferInstance : NonAssocSemiring (𝕋 Δ H R)) with
    mul_assoc := fun f g h ↦ mul_assoc' R f g h }

end HeckeCosetModule
