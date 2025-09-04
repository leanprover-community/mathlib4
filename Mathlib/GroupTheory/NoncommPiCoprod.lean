/-
Copyright (c) 2022 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.SupIndep

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
* `MonoidHom.injective_noncommPiCoprod_of_iSupIndep`: in the case of groups, `pi_hom.hom` is
  injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `MonoidHom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
  of the `ϕ` are independent.
* `Subgroup.independent_of_coprime_order`: If commuting normal subgroups `H i` have coprime orders,
  they are independent.

-/

assert_not_exists Field

namespace Subgroup

variable {G : Type*} [Group G]

/-- `Finset.noncommProd` is “injective” in `f` if `f` maps into independent subgroups.  This
generalizes (one direction of) `Subgroup.disjoint_iff_mul_eq_one`. -/
@[to_additive /-- `Finset.noncommSum` is “injective” in `f` if `f` maps into independent subgroups.
This generalizes (one direction of) `AddSubgroup.disjoint_iff_add_eq_zero`. -/]
theorem eq_one_of_noncommProd_eq_one_of_iSupIndep {ι : Type*} (s : Finset ι) (f : ι → G) (comm)
    (K : ι → Subgroup G) (hind : iSupIndep K) (hmem : ∀ x ∈ s, f x ∈ K x)
    (heq1 : s.noncommProd f comm = 1) : ∀ i ∈ s, f i = 1 := by
  classical
    revert heq1
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hnotMem ih =>
      have hcomm := comm.mono (Finset.coe_subset.2 <| Finset.subset_insert _ _)
      simp only [Finset.forall_mem_insert] at hmem
      have hmem_bsupr : s.noncommProd f hcomm ∈ ⨆ i ∈ (s : Set ι), K i := by
        refine Subgroup.noncommProd_mem _ _ ?_
        intro x hx
        have : K x ≤ ⨆ i ∈ (s : Set ι), K i := le_iSup₂ (f := fun i _ => K i) x hx
        exact this (hmem.2 x hx)
      intro heq1
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hnotMem] at heq1
      have hnotMem' : i ∉ (s : Set ι) := by simpa
      obtain ⟨heq1i : f i = 1, heq1S : s.noncommProd f _ = 1⟩ :=
        Subgroup.disjoint_iff_mul_eq_one.mp (hind.disjoint_biSup hnotMem') hmem.1 hmem_bsupr heq1
      intro i h
      simp only [Finset.mem_insert] at h
      rcases h with (rfl | h)
      · exact heq1i
      · refine ih hcomm hmem.2 heq1S _ h

end Subgroup

section FamilyOfMonoids

variable {M : Type*} [Monoid M]

-- We have a family of monoids
-- The fintype assumption is not always used, but declared here, to keep things in order
variable {ι : Type*} [Fintype ι]
variable {N : ι → Type*} [∀ i, Monoid (N i)]

-- And morphisms ϕ into G
variable (ϕ : ∀ i : ι, N i →* M)

-- We assume that the elements of different morphism commute
variable (hcomm : Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y))

namespace MonoidHom

/-- The canonical homomorphism from a family of monoids. -/
@[to_additive /-- The canonical homomorphism from a family of additive monoids. See also
`LinearMap.lsum` for a linear version without the commutativity assumption. -/]
def noncommPiCoprod : (∀ i : ι, N i) →* M where
  toFun f := Finset.univ.noncommProd (fun i => ϕ i (f i)) fun _ _ _ _ h => hcomm h _ _
  map_one' := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ _ _).trans (one_pow _)
    simp
  map_mul' f g := by
    classical
    convert @Finset.noncommProd_mul_distrib _ _ _ _ (fun i => ϕ i (f i)) (fun i => ϕ i (g i)) _ _ _
    · exact map_mul _ _ _
    · rintro i - j - h
      exact hcomm h _ _

variable {hcomm}

@[to_additive (attr := simp)]
theorem noncommPiCoprod_mulSingle [DecidableEq ι] (i : ι) (y : N i) :
    noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y := by
  change Finset.univ.noncommProd (fun j => ϕ j (Pi.mulSingle i y j)) (fun _ _ _ _ h => hcomm h _ _)
    = ϕ i y
  rw [← Finset.insert_erase (Finset.mem_univ i)]
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ (Finset.notMem_erase i _)]
  rw [Pi.mulSingle_eq_same]
  rw [Finset.noncommProd_eq_pow_card]
  · rw [one_pow]
    exact mul_one _
  · intro j hj
    simp only [Finset.mem_erase] at hj
    simp [hj]

/--
The universal property of `MonoidHom.noncommPiCoprod`

Given monoid morphisms `φᵢ : Nᵢ → M` whose images pairwise commute,
there exists a unique monoid morphism `φ : Πᵢ Nᵢ → M` that induces the `φᵢ`,
and it is given by `MonoidHom.noncommPiCoprod`. -/
@[to_additive /-- The universal property of `MonoidHom.noncommPiCoprod`

Given monoid morphisms `φᵢ : Nᵢ → M` whose images pairwise commute,
there exists a unique monoid morphism `φ : Πᵢ Nᵢ → M` that induces the `φᵢ`,
and it is given by `AddMonoidHom.noncommPiCoprod`. -/]
def noncommPiCoprodEquiv [DecidableEq ι] :
    { ϕ : ∀ i, N i →* M // Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y) } ≃
      ((∀ i, N i) →* M) where
  toFun ϕ := noncommPiCoprod ϕ.1 ϕ.2
  invFun f :=
    ⟨fun i => f.comp (MonoidHom.mulSingle N i), fun _ _ hij x y =>
      Commute.map (Pi.mulSingle_commute hij x y) f⟩
  left_inv ϕ := by
    ext
    simp only [coe_comp, Function.comp_apply, mulSingle_apply, noncommPiCoprod_mulSingle]
  right_inv f := pi_ext fun i x => by
    simp only [noncommPiCoprod_mulSingle, coe_comp, Function.comp_apply, mulSingle_apply]

@[to_additive]
theorem noncommPiCoprod_mrange :
    MonoidHom.mrange (noncommPiCoprod ϕ hcomm) = ⨆ i : ι, MonoidHom.mrange (ϕ i) := by
  letI := Classical.decEq ι
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    refine Submonoid.noncommProd_mem _ _ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => ?_)
    apply Submonoid.mem_sSup_of_mem
    · use i
    simp
  · refine iSup_le ?_
    rintro i x ⟨y, rfl⟩
    exact ⟨Pi.mulSingle i y, noncommPiCoprod_mulSingle _ _ _⟩

@[to_additive]
lemma commute_noncommPiCoprod {m : M}
    (comm : ∀ i (x : N i), Commute m ((ϕ i x))) (h : (i : ι) → N i) :
    Commute m (MonoidHom.noncommPiCoprod ϕ hcomm h) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
  apply Finset.noncommProd_induction
  · exact fun x y ↦ Commute.mul_right
  · exact Commute.one_right _
  · exact fun x _ ↦ comm x (h x)

@[to_additive]
lemma noncommPiCoprod_apply (h : (i : ι) → N i) :
    MonoidHom.noncommPiCoprod ϕ hcomm h = Finset.noncommProd Finset.univ (fun i ↦ ϕ i (h i))
      (Pairwise.set_pairwise (fun ⦃i j⦄ a ↦ hcomm a (h i) (h j)) _) := by
  dsimp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]

/--
Given monoid morphisms `φᵢ : Nᵢ → M` and `f : M → P`, if we have sufficient commutativity, then
`f ∘ (∐ᵢ φᵢ) = ∐ᵢ (f ∘ φᵢ)` -/
@[to_additive]
theorem comp_noncommPiCoprod {P : Type*} [Monoid P] {f : M →* P}
    (hcomm' : Pairwise fun i j => ∀ x y, Commute (f.comp (ϕ i) x) (f.comp (ϕ j) y) :=
      Pairwise.mono hcomm (fun i j ↦ forall_imp (fun x h y ↦ by
        simp only [MonoidHom.coe_comp, Function.comp_apply, Commute.map (h y) f]))) :
    f.comp (MonoidHom.noncommPiCoprod ϕ hcomm) =
      MonoidHom.noncommPiCoprod (fun i ↦ f.comp (ϕ i)) hcomm' :=
  MonoidHom.ext fun _ ↦ by
    simp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply, Finset.map_noncommProd]

end MonoidHom

end FamilyOfMonoids

section FamilyOfGroups

variable {G : Type*} [Group G]
variable {ι : Type*}
variable {H : ι → Type*} [∀ i, Group (H i)]
variable (ϕ : ∀ i : ι, H i →* G)

namespace MonoidHom
-- The subgroup version of `MonoidHom.noncommPiCoprod_mrange`
@[to_additive]
theorem noncommPiCoprod_range [Fintype ι]
    {hcomm : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)} :
    (noncommPiCoprod ϕ hcomm).range = ⨆ i : ι, (ϕ i).range := by
  letI := Classical.decEq ι
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    refine Subgroup.noncommProd_mem _ (fun _ _ _ _ h => hcomm h _ _) ?_
    intro i _hi
    apply Subgroup.mem_sSup_of_mem
    · use i
    simp
  · refine iSup_le ?_
    rintro i x ⟨y, rfl⟩
    exact ⟨Pi.mulSingle i y, noncommPiCoprod_mulSingle _ _ _⟩

@[to_additive]
theorem injective_noncommPiCoprod_of_iSupIndep [Fintype ι]
    {hcomm : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)}
    (hind : iSupIndep fun i => (ϕ i).range)
    (hinj : ∀ i, Function.Injective (ϕ i)) : Function.Injective (noncommPiCoprod ϕ hcomm) := by
  classical
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [eq_bot_iff]
    intro f heq1
    have : ∀ i, i ∈ Finset.univ → ϕ i (f i) = 1 :=
      Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep _ _ (fun _ _ _ _ h => hcomm h _ _)
        _ hind (by simp) heq1
    ext i
    apply hinj
    simp [this i (Finset.mem_univ i)]

@[to_additive]
theorem independent_range_of_coprime_order
    (hcomm : Pairwise fun i j : ι => ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y))
    [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    iSupIndep fun i => (ϕ i).range := by
  cases nonempty_fintype ι
  letI := Classical.decEq ι
  rintro i
  rw [disjoint_iff_inf_le]
  rintro f ⟨hxi, hxp⟩
  dsimp at hxi hxp
  rw [iSup_subtype', ← noncommPiCoprod_range] at hxp
  rotate_left
  · intro _ _ hj
    apply hcomm
    exact hj ∘ Subtype.ext
  obtain ⟨g, hgf⟩ := hxp
  obtain ⟨g', hg'f⟩ := hxi
  have hxi : orderOf f ∣ Fintype.card (H i) := by
    rw [← hg'f]
    exact (orderOf_map_dvd _ _).trans orderOf_dvd_card
  have hxp : orderOf f ∣ ∏ j : { j // j ≠ i }, Fintype.card (H j) := by
    rw [← hgf, ← Fintype.card_pi]
    exact (orderOf_map_dvd _ _).trans orderOf_dvd_card
  change f = 1
  rw [← pow_one f, ← orderOf_dvd_iff_pow_eq_one]
  obtain ⟨c, hc⟩ := Nat.dvd_gcd hxp hxi
  use c
  rw [← hc]
  symm
  rw [← Nat.coprime_iff_gcd_eq_one, Nat.coprime_fintype_prod_left_iff, Subtype.forall]
  intro j h
  exact hcoprime h

end MonoidHom

end FamilyOfGroups

namespace Subgroup

-- We have a family of subgroups
variable {G : Type*} [Group G]
variable {ι : Type*} {H : ι → Subgroup G}

section CommutingSubgroups

-- We assume that the elements of different subgroups commute
-- with `hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y`

@[to_additive]
theorem commute_subtype_of_commute
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) (i j : ι)
    (hne : i ≠ j) :
    ∀ (x : H i) (y : H j), Commute ((H i).subtype x) ((H j).subtype y) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  exact hcomm hne x y hx hy

@[to_additive]
theorem independent_of_coprime_order
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    iSupIndep H := by
  simpa using
    MonoidHom.independent_range_of_coprime_order (fun i => (H i).subtype)
      (commute_subtype_of_commute hcomm) hcoprime

variable [Fintype ι]

/-- The canonical homomorphism from a family of subgroups where elements from different subgroups
commute -/
@[to_additive /-- The canonical homomorphism from a family of additive subgroups where elements from
different subgroups commute -/]
def noncommPiCoprod (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) :
    (∀ i : ι, H i) →* G :=
  MonoidHom.noncommPiCoprod (fun i => (H i).subtype) (commute_subtype_of_commute hcomm)

@[to_additive (attr := simp)]
theorem noncommPiCoprod_mulSingle [DecidableEq ι]
    {hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y}(i : ι) (y : H i) :
    noncommPiCoprod hcomm (Pi.mulSingle i y) = y := by apply MonoidHom.noncommPiCoprod_mulSingle

@[to_additive]
theorem noncommPiCoprod_range
    {hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y} :
    (noncommPiCoprod hcomm).range = ⨆ i : ι, H i := by
  simp [noncommPiCoprod, MonoidHom.noncommPiCoprod_range]

@[to_additive]
theorem injective_noncommPiCoprod_of_iSupIndep
    {hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y}
    (hind : iSupIndep H) :
    Function.Injective (noncommPiCoprod hcomm) := by
  apply MonoidHom.injective_noncommPiCoprod_of_iSupIndep
  · simpa using hind
  · intro i
    exact Subtype.coe_injective

@[to_additive]
theorem noncommPiCoprod_apply (comm) (u : (i : ι) → H i) :
    Subgroup.noncommPiCoprod comm u = Finset.noncommProd Finset.univ (fun i ↦ u i)
      (fun i _ j _ h ↦ comm h _ _ (u i).prop (u j).prop) := by
  simp only [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod,
    coe_subtype, MonoidHom.coe_mk, OneHom.coe_mk]

end CommutingSubgroups

end Subgroup
