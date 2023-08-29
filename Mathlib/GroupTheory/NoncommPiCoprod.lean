/-
Copyright (c) 2022 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.SupIndep

#align_import group_theory.noncomm_pi_coprod from "leanprover-community/mathlib"@"6f9f36364eae3f42368b04858fd66d6d9ae730d8"

/-!
# Canonical homomorphism from a finite family of monoids

This file defines the construction of the canonical homomorphism from a family of monoids.

Given a family of morphisms `ϕ i : N i →* M` for each `i : ι` where elements in the
images of different morphisms commute, we obtain a canonical morphism
`MonoidHom.noncommPiCoprod : (Π i, N i) →* M` that coincides with `ϕ`

## Main definitions

* `MonoidHom.noncommPiCoprod : (Π i, N i) →* M` is the main homomorphism
* `Subgroup.noncommPiCoprod : (Π i, H i) →* G` is the specialization to `H i : Subgroup G`
   and the subgroup embedding.

## Main theorems

* `MonoidHom.noncommPiCoprod` coincides with `ϕ i` when restricted to `N i`
* `MonoidHom.noncommPiCoprod_mrange`: The range of `MonoidHom.noncommPiCoprod` is
  `⨆ (i : ι), (ϕ i).mrange`
* `MonoidHom.noncommPiCoprod_range`: The range of `MonoidHom.noncommPiCoprod` is
  `⨆ (i : ι), (ϕ i).range`
* `Subgroup.noncommPiCoprod_range`: The range of `Subgroup.noncommPiCoprod` is `⨆ (i : ι), H i`.
* `MonoidHom.injective_noncommPiCoprod_of_independent`: in the case of groups, `pi_hom.hom` is
   injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `MonoidHom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
   of the `ϕ` are independent.
* `Subgroup.independent_of_coprime_order`: If commuting normal subgroups `H i` have coprime orders,
   they are independent.

-/


open BigOperators

namespace Subgroup

variable {G : Type*} [Group G]

/-- `Finset.noncommProd` is “injective” in `f` if `f` maps into independent subgroups.  This
generalizes (one direction of) `Subgroup.disjoint_iff_mul_eq_one`. -/
@[to_additive "`Finset.noncommSum` is “injective” in `f` if `f` maps into independent subgroups.
This generalizes (one direction of) `AddSubgroup.disjoint_iff_add_eq_zero`. "]
theorem eq_one_of_noncommProd_eq_one_of_independent {ι : Type*} (s : Finset ι) (f : ι → G) (comm)
    (K : ι → Subgroup G) (hind : CompleteLattice.Independent K) (hmem : ∀ x ∈ s, f x ∈ K x)
    (heq1 : s.noncommProd f comm = 1) : ∀ i ∈ s, f i = 1 := by
  classical
    revert heq1
    induction' s using Finset.induction_on with i s hnmem ih
    · simp
    · have hcomm := comm.mono (Finset.coe_subset.2 <| Finset.subset_insert _ _)
      simp only [Finset.forall_mem_insert] at hmem
      have hmem_bsupr : s.noncommProd f hcomm ∈ ⨆ i ∈ (s : Set ι), K i := by
        refine' Subgroup.noncommProd_mem _ _ _
        intro x hx
        have : K x ≤ ⨆ i ∈ (s : Set ι), K i := le_iSup₂ (f := fun i _ => K i) x hx
        exact this (hmem.2 x hx)
      intro heq1
      rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ hnmem] at heq1
      have hnmem' : i ∉ (s : Set ι) := by simpa
      obtain ⟨heq1i : f i = 1, heq1S : s.noncommProd f _ = 1⟩ :=
        Subgroup.disjoint_iff_mul_eq_one.mp (hind.disjoint_biSup hnmem') hmem.1 hmem_bsupr heq1
      intro i h
      simp only [Finset.mem_insert] at h
      rcases h with (rfl | h)
      · exact heq1i
      · refine' ih hcomm hmem.2 heq1S _ h
#align subgroup.eq_one_of_noncomm_prod_eq_one_of_independent Subgroup.eq_one_of_noncommProd_eq_one_of_independent
#align add_subgroup.eq_zero_of_noncomm_sum_eq_zero_of_independent AddSubgroup.eq_zero_of_noncommSum_eq_zero_of_independent

end Subgroup

section FamilyOfMonoids

variable {M : Type*} [Monoid M]

-- We have a family of monoids
-- The fintype assumption is not always used, but declared here, to keep things in order
variable {ι : Type*} [hdec : DecidableEq ι] [Fintype ι]

variable {N : ι → Type*} [∀ i, Monoid (N i)]

-- And morphisms ϕ into G
variable (ϕ : ∀ i : ι, N i →* M)

-- We assume that the elements of different morphism commute
variable (hcomm : Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y))

-- We use `f` and `g` to denote elements of `Π (i : ι), N i`
variable (f g : ∀ i : ι, N i)

namespace MonoidHom

/-- The canonical homomorphism from a family of monoids. -/
@[to_additive "The canonical homomorphism from a family of additive monoids. See also
`LinearMap.lsum` for a linear version without the commutativity assumption."]
def noncommPiCoprod : (∀ i : ι, N i) →* M
    where
  toFun f := Finset.univ.noncommProd (fun i => ϕ i (f i)) fun i _ j _ h => hcomm h _ _
  map_one' := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ _ _).trans (one_pow _)
    -- ⊢ ∀ (x : ι), x ∈ Finset.univ → ↑(ϕ x) (OfNat.ofNat 1 x) = 1
    simp
    -- 🎉 no goals
  map_mul' f g := by
    classical
    simp only
    convert @Finset.noncommProd_mul_distrib _ _ _ _ (fun i => ϕ i (f i)) (fun i => ϕ i (g i)) _ _ _
    · exact map_mul _ _ _
    · rintro i - j - h
      exact hcomm h _ _
#align monoid_hom.noncomm_pi_coprod MonoidHom.noncommPiCoprod
#align add_monoid_hom.noncomm_pi_coprod AddMonoidHom.noncommPiCoprod

variable {hcomm}

@[to_additive (attr := simp)]
theorem noncommPiCoprod_mulSingle (i : ι) (y : N i) :
    noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y := by
  change Finset.univ.noncommProd (fun j => ϕ j (Pi.mulSingle i y j)) (fun _ _ _ _ h => hcomm h _ _)
    = ϕ i y
  simp (config := { singlePass := true }) only [← Finset.insert_erase (Finset.mem_univ i)]
  -- ⊢ Finset.noncommProd (insert i (Finset.erase Finset.univ i)) (fun x => ↑(ϕ x)  …
  rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ (Finset.not_mem_erase i _)]
  -- ⊢ ↑(ϕ i) (Pi.mulSingle i y i) * Finset.noncommProd (Finset.erase Finset.univ i …
  rw [Pi.mulSingle_eq_same]
  -- ⊢ ↑(ϕ i) y * Finset.noncommProd (Finset.erase Finset.univ i) (fun x => ↑(ϕ x)  …
  rw [Finset.noncommProd_eq_pow_card]
  · rw [one_pow]
    -- ⊢ ↑(ϕ i) y * 1 = ↑(ϕ i) y
    exact mul_one _
    -- 🎉 no goals
  · intro j hj
    -- ⊢ ↑(ϕ j) (Pi.mulSingle i y j) = 1
    simp only [Finset.mem_erase] at hj
    -- ⊢ ↑(ϕ j) (Pi.mulSingle i y j) = 1
    simp [hj]
    -- 🎉 no goals
#align monoid_hom.noncomm_pi_coprod_mul_single MonoidHom.noncommPiCoprod_mulSingle
#align add_monoid_hom.noncomm_pi_coprod_single AddMonoidHom.noncommPiCoprod_single

/-- The universal property of `MonoidHom.noncommPiCoprod` -/
@[to_additive "The universal property of `AddMonoidHom.noncommPiCoprod`"]
def noncommPiCoprodEquiv :
    { ϕ : ∀ i, N i →* M // Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y) } ≃ ((∀ i, N i) →* M)
    where
  toFun ϕ := noncommPiCoprod ϕ.1 ϕ.2
  invFun f :=
    ⟨fun i => f.comp (MonoidHom.single N i), fun i j hij x y =>
      Commute.map (Pi.mulSingle_commute hij x y) f⟩
  left_inv ϕ := by
    ext
    -- ⊢ ↑(↑((fun f => { val := fun i => comp f (single N i), property := (_ : ∀ (i j …
    simp
    -- 🎉 no goals
  right_inv f := pi_ext fun i x => by simp
                                      -- 🎉 no goals
#align monoid_hom.noncomm_pi_coprod_equiv MonoidHom.noncommPiCoprodEquiv
#align add_monoid_hom.noncomm_pi_coprod_equiv AddMonoidHom.noncommPiCoprodEquiv

@[to_additive]
theorem noncommPiCoprod_mrange :
    MonoidHom.mrange (noncommPiCoprod ϕ hcomm) = ⨆ i : ι, MonoidHom.mrange (ϕ i) := by
  classical
    apply le_antisymm
    · rintro x ⟨f, rfl⟩
      refine Submonoid.noncommProd_mem _ _ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => ?_)
      apply Submonoid.mem_sSup_of_mem
      · use i
      simp
    · refine' iSup_le _
      rintro i x ⟨y, rfl⟩
      refine' ⟨Pi.mulSingle i y, noncommPiCoprod_mulSingle _ _ _⟩
#align monoid_hom.noncomm_pi_coprod_mrange MonoidHom.noncommPiCoprod_mrange
#align add_monoid_hom.noncomm_pi_coprod_mrange AddMonoidHom.noncommPiCoprod_mrange

end MonoidHom

end FamilyOfMonoids

section FamilyOfGroups

variable {G : Type*} [Group G]

variable {ι : Type*} [hdec : DecidableEq ι] [hfin : Fintype ι]

variable {H : ι → Type*} [∀ i, Group (H i)]

variable (ϕ : ∀ i : ι, H i →* G)

variable {hcomm : ∀ i j : ι, i ≠ j → ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)}

-- We use `f` and `g` to denote elements of `Π (i : ι), H i`
variable (f g : ∀ i : ι, H i)

namespace MonoidHom

-- The subgroup version of `MonoidHom.noncommPiCoprod_mrange`
@[to_additive]
theorem noncommPiCoprod_range : (noncommPiCoprod ϕ hcomm).range = ⨆ i : ι, (ϕ i).range := by
  classical
    apply le_antisymm
    · rintro x ⟨f, rfl⟩
      refine Subgroup.noncommProd_mem _ (fun _ _ _ _ h => hcomm _ _ h _ _) ?_
      intro i _hi
      apply Subgroup.mem_sSup_of_mem
      · use i
      simp
    · refine' iSup_le _
      rintro i x ⟨y, rfl⟩
      refine' ⟨Pi.mulSingle i y, noncommPiCoprod_mulSingle _ _ _⟩
#align monoid_hom.noncomm_pi_coprod_range MonoidHom.noncommPiCoprod_range
#align add_monoid_hom.noncomm_pi_coprod_range AddMonoidHom.noncommPiCoprod_range

@[to_additive]
theorem injective_noncommPiCoprod_of_independent
    (hind : CompleteLattice.Independent fun i => (ϕ i).range)
    (hinj : ∀ i, Function.Injective (ϕ i)) : Function.Injective (noncommPiCoprod ϕ hcomm) := by
  classical
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro f heq1
    have : ∀ i, i ∈ Finset.univ → ϕ i (f i) = 1 :=
      Subgroup.eq_one_of_noncommProd_eq_one_of_independent _ _ (fun _ _ _ _ h => hcomm _ _ h _ _)
        _ hind (by simp) heq1
    ext i
    apply hinj
    simp [this i (Finset.mem_univ i)]
#align monoid_hom.injective_noncomm_pi_coprod_of_independent MonoidHom.injective_noncommPiCoprod_of_independent
#align add_monoid_hom.injective_noncomm_pi_coprod_of_independent AddMonoidHom.injective_noncommPiCoprod_of_independent

variable (hcomm)

@[to_additive]
theorem independent_range_of_coprime_order [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : ∀ i j, i ≠ j → Nat.coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    CompleteLattice.Independent fun i => (ϕ i).range := by
  cases nonempty_fintype ι
  -- ⊢ CompleteLattice.Independent fun i => range (ϕ i)
  classical
    rintro i
    rw [disjoint_iff_inf_le]
    rintro f ⟨hxi, hxp⟩
    dsimp at hxi hxp
    rw [iSup_subtype', ← noncommPiCoprod_range] at hxp
    rotate_left
    · intro _ _ hj
      apply hcomm
      exact hj ∘ Subtype.ext
    cases' hxp with g hgf
    cases' hxi with g' hg'f
    have hxi : orderOf f ∣ Fintype.card (H i) := by
      rw [← hg'f]
      exact (orderOf_map_dvd _ _).trans orderOf_dvd_card_univ
    have hxp : orderOf f ∣ ∏ j : { j // j ≠ i }, Fintype.card (H j) := by
      rw [← hgf, ← Fintype.card_pi]
      exact (orderOf_map_dvd _ _).trans orderOf_dvd_card_univ
    change f = 1
    rw [← pow_one f, ← orderOf_dvd_iff_pow_eq_one]
    -- porting note: ouch, had to replace an ugly `convert`
    obtain ⟨c, hc⟩ := Nat.dvd_gcd hxp hxi
    use c
    rw [← hc]
    symm
    rw [← Nat.coprime_iff_gcd_eq_one]
    apply Nat.coprime_prod_left
    intro j _
    apply hcoprime
    exact j.2
#align monoid_hom.independent_range_of_coprime_order MonoidHom.independent_range_of_coprime_order
#align add_monoid_hom.independent_range_of_coprime_order AddMonoidHom.independent_range_of_coprime_order

end MonoidHom

end FamilyOfGroups

namespace Subgroup

-- We have a family of subgroups
variable {G : Type*} [Group G]

variable {ι : Type*} [hdec : DecidableEq ι] [hfin : Fintype ι] {H : ι → Subgroup G}

-- Elements of `Π (i : ι), H i` are called `f` and `g` here
variable (f g : ∀ i : ι, H i)

section CommutingSubgroups

-- We assume that the elements of different subgroups commute
variable (hcomm : ∀ i j : ι, i ≠ j → ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)

@[to_additive]
theorem commute_subtype_of_commute (i j : ι) (hne : i ≠ j) :
    ∀ (x : H i) (y : H j), Commute ((H i).subtype x) ((H j).subtype y) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  -- ⊢ Commute (↑(Subgroup.subtype (H i)) { val := x, property := hx }) (↑(Subgroup …
  exact hcomm i j hne x y hx hy
  -- 🎉 no goals
#align subgroup.commute_subtype_of_commute Subgroup.commute_subtype_of_commute
#align add_subgroup.commute_subtype_of_commute AddSubgroup.commute_subtype_of_commute

/-- The canonical homomorphism from a family of subgroups where elements from different subgroups
commute -/
@[to_additive "The canonical homomorphism from a family of additive subgroups where elements from
different subgroups commute"]
def noncommPiCoprod : (∀ i : ι, H i) →* G :=
  MonoidHom.noncommPiCoprod (fun i => (H i).subtype) (commute_subtype_of_commute hcomm)
#align subgroup.noncomm_pi_coprod Subgroup.noncommPiCoprod
#align add_subgroup.noncomm_pi_coprod AddSubgroup.noncommPiCoprod

variable {hcomm}

@[to_additive (attr := simp)]
theorem noncommPiCoprod_mulSingle (i : ι) (y : H i) :
    noncommPiCoprod hcomm (Pi.mulSingle i y) = y := by apply MonoidHom.noncommPiCoprod_mulSingle
                                                       -- 🎉 no goals
#align subgroup.noncomm_pi_coprod_mul_single Subgroup.noncommPiCoprod_mulSingle
#align add_subgroup.noncomm_pi_coprod_single AddSubgroup.noncommPiCoprod_single

@[to_additive]
theorem noncommPiCoprod_range : (noncommPiCoprod hcomm).range = ⨆ i : ι, H i := by
  simp [noncommPiCoprod, MonoidHom.noncommPiCoprod_range]
  -- 🎉 no goals
#align subgroup.noncomm_pi_coprod_range Subgroup.noncommPiCoprod_range
#align add_subgroup.noncomm_pi_coprod_range AddSubgroup.noncommPiCoprod_range

@[to_additive]
theorem injective_noncommPiCoprod_of_independent (hind : CompleteLattice.Independent H) :
    Function.Injective (noncommPiCoprod hcomm) := by
  apply MonoidHom.injective_noncommPiCoprod_of_independent
  -- ⊢ CompleteLattice.Independent fun i => MonoidHom.range (Subgroup.subtype ((fun …
  · simpa using hind
    -- 🎉 no goals
  · intro i
    -- ⊢ Function.Injective ↑(Subgroup.subtype ((fun i => H i) i))
    exact Subtype.coe_injective
    -- 🎉 no goals
#align subgroup.injective_noncomm_pi_coprod_of_independent Subgroup.injective_noncommPiCoprod_of_independent
#align add_subgroup.injective_noncomm_pi_coprod_of_independent AddSubgroup.injective_noncommPiCoprod_of_independent

variable (hcomm)

@[to_additive]
theorem independent_of_coprime_order [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : ∀ i j, i ≠ j → Nat.coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    CompleteLattice.Independent H := by
  simpa using
    MonoidHom.independent_range_of_coprime_order (fun i => (H i).subtype)
      (commute_subtype_of_commute hcomm) hcoprime
#align subgroup.independent_of_coprime_order Subgroup.independent_of_coprime_order
#align add_subgroup.independent_of_coprime_order AddSubgroup.independent_of_coprime_order

end CommutingSubgroups

end Subgroup
