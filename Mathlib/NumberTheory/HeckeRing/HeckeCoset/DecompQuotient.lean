/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index

/-!
# Decompsition Quotient

-/

@[expose] public section

variable {G : Type*} [Group G] (H₁ H₂ : Subgroup G) (g g' : G)

open Pointwise

namespace DoubleCoset

section decomp

/-- The decomposition quotient `H₁ ⧸ (H₁ ∩ gH₂g⁻¹)`, indexing the left cosets of `Γ₂` inside
the double coset `H₁gH₂`; see `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`. -/
abbrev DecompQuotient := H₁ ⧸ ((ConjAct.toConjAct g) • H₂).subgroupOf H₁

namespace DecompQuotient

lemma nat_card_eq_relIndex :
    Nat.card (DecompQuotient H₁ H₂ g) = (ConjAct.toConjAct g • H₂).relIndex H₁ := rfl

/-- The canonical map from the decomposition quotient `H₁ ⧸ (H₁ ∩ gH₂g⁻¹)` to left coset space
`G ⧸ H₂`. -/
def toLeftCoset :
    DecompQuotient H₁ H₂ g → G ⧸ H₂ :=
  Quotient.lift (fun x => (x * g : G)) fun _ _ h => by
    rw [Quotient.eq, QuotientGroup.leftRel_apply]
    have := (QuotientGroup.leftRel_apply.mp h)
    simpa [mul_assoc] using Subgroup.mem_conjAct_pointwise_smul_iff.mp this

variable {H₁ H₂ H₃ g g'}

@[simp]
lemma toLeftCoset_mk (x : H₁) :
    toLeftCoset H₁ H₂ g (x : DecompQuotient H₁ H₂ g) = (x.val * g : G ⧸ H₂) :=
  rfl

lemma toLeftCoset_apply (x : DecompQuotient H₁ H₂ g) :
    toLeftCoset H₁ H₂ g x = (x.out.val * g : G ⧸ H₂) := by
  nth_rw 1 [← Quotient.out_eq x]
  rfl

lemma toLeftCoset_injective :
    Function.Injective (toLeftCoset H₁ H₂ g) := by
  intro i j hij
  rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq]
  simpa [toLeftCoset_apply, QuotientGroup.eq, mul_assoc, Subgroup.mem_subgroupOf,
    Subgroup.mem_conjAct_pointwise_smul_iff] using hij

lemma exists_toLeftCoset_of_mk_eq
    {g d : G}
    (hgd : DoubleCoset.mk H₁ H₂ g = DoubleCoset.mk H₁ H₂ d) :
    ∃ i : DecompQuotient H₁ H₂ g, toLeftCoset H₁ H₂ g i = (d : G ⧸ H₂) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := (DoubleCoset.eq H₁ H₂ g d).mp hgd
  refine ⟨QuotientGroup.mk ⟨h₁, hh₁⟩, ?_⟩
  simp [hh₂]

end DecompQuotient

end decomp

section degree

variable {H₁ H₂} (x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G))

/-- The cardinality of `H₁ ⧸ (H₁ ∩ gH₂g⁻¹)`, which depends only the correponding double coset
`H₁gH₂`. -/
noncomputable def Quotient.degree :
    ℕ := Quotient.liftOn x (fun x => (ConjAct.toConjAct x • H₂).relIndex H₁) fun a b hab => by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := DoubleCoset.rel_iff.mp hab
  have hH₁ : ConjAct.toConjAct h₁ • H₁ = H₁ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh₁)
  have hH₂ : ConjAct.toConjAct h₂ • H₂ = H₂ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh₂)
  nth_rewrite 2 [← hH₁]
  simp [mul_smul, hH₂, Subgroup.relIndex_pointwise_smul]

lemma mk_degree (g : G) :
    (mk H₁ H₂ g).degree = Nat.card (DecompQuotient H₁ H₂ g)  := rfl

lemma degree_eq_out :
    x.degree = Nat.card (DecompQuotient H₁ H₂ x.out)  := by
  simp [← mk_degree, out_eq']

@[simp]
lemma diag_mk_one_degree_eq_one (H : Subgroup G) : (mk H H 1).degree = 1 := by
  simp [mk_degree]

end degree

end DoubleCoset
