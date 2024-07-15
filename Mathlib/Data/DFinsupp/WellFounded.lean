/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Data.DFinsupp.Lex
import Mathlib.Order.GameAdd
import Mathlib.Order.Antisymmetrization
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic.AdaptationNote

#align_import data.dfinsupp.well_founded from "leanprover-community/mathlib"@"e9b8651eb1ad354f4de6be35a38ef31efcd2cfaa"

/-!
# Well-foundedness of the lexicographic and product orders on `DFinsupp` and `Pi`

The primary results are `DFinsupp.Lex.wellFounded` and the two variants that follow it,
which essentially say that if `(· > ·)` is a well order on `ι`, `(· < ·)` is well-founded on each
`α i`, and `0` is a bottom element in `α i`, then the lexicographic `(· < ·)` is well-founded
on `Π₀ i, α i`. The proof is modelled on the proof of `WellFounded.cutExpand`.

The results are used to prove `Pi.Lex.wellFounded` and two variants, which say that if
`ι` is finite and equipped with a linear order and `(· < ·)` is well-founded on each `α i`,
then the lexicographic `(· < ·)` is well-founded on `Π i, α i`, and the same is true for
`Π₀ i, α i` (`DFinsupp.Lex.wellFounded_of_finite`), because `DFinsupp` is order-isomorphic
to `pi` when `ι` is finite.

Finally, we deduce `DFinsupp.wellFoundedLT`, `Pi.wellFoundedLT`,
`DFinsupp.wellFoundedLT_of_finite` and variants, which concern the product order
rather than the lexicographic one. An order on `ι` is not required in these results,
but we deduce them from the well-foundedness of the lexicographic order by choosing
a well order on `ι` so that the product order `(· < ·)` becomes a subrelation
of the lexicographic `(· < ·)`.

All results are provided in two forms whenever possible: a general form where the relations
can be arbitrary (not the `(· < ·)` of a preorder, or not even transitive, etc.) and a specialized
form provided as `WellFoundedLT` instances where the `(d)Finsupp/pi` type (or their `Lex`
type synonyms) carries a natural `(· < ·)`.

Notice that the definition of `DFinsupp.Lex` says that `x < y` according to `DFinsupp.Lex r s`
iff there exists a coordinate `i : ι` such that `x i < y i` according to `s i`, and at all
`r`-smaller coordinates `j` (i.e. satisfying `r j i`), `x` remains unchanged relative to `y`;
in other words, coordinates `j` such that `¬ r j i` and `j ≠ i` are exactly where changes
can happen arbitrarily. This explains the appearance of `rᶜ ⊓ (≠)` in
`dfinsupp.acc_single` and `dfinsupp.well_founded`. When `r` is trichotomous (e.g. the `(· < ·)`
of a linear order), `¬ r j i ∧ j ≠ i` implies `r i j`, so it suffices to require `r.swap`
to be well-founded.
-/


variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

open Relation Prod

section Zero

variable [∀ i, Zero (α i)] (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop)

/-- This key lemma says that if a finitely supported dependent function `x₀` is obtained by merging
  two such functions `x₁` and `x₂`, and if we evolve `x₀` down the `DFinsupp.Lex` relation one
  step and get `x`, we can always evolve one of `x₁` and `x₂` down the `DFinsupp.Lex` relation
  one step while keeping the other unchanged, and merge them back (possibly in a different way)
  to get back `x`. In other words, the two parts evolve essentially independently under
  `DFinsupp.Lex`. This is used to show that a function `x` is accessible if
  `DFinsupp.single i (x i)` is accessible for each `i` in the (finite) support of `x`
  (`DFinsupp.Lex.acc_of_single`). -/
theorem lex_fibration [∀ (i) (s : Set ι), Decidable (i ∈ s)] :
    Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s)
      fun x => piecewise x.2.1 x.2.2 x.1 := by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs with hp
  · refine ⟨⟨{ j | r j i → j ∈ p }, piecewise x₁ x { j | r j i }, x₂⟩,
      .fst ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_setOf_eq]
    · simp only [if_pos hj]
    · split_ifs with hi
      · rwa [hr i hi, if_pos hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_setOf_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₂, if_pos (h₁ h₂)]
      · rw [Classical.not_imp] at h₁
        rw [hr j h₁.1, if_neg h₁.2]
  · refine ⟨⟨{ j | r j i ∧ j ∈ p }, x₁, piecewise x₂ x { j | r j i }⟩,
      .snd ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_setOf_eq]
    · exact if_pos hj
    · split_ifs with hi
      · rwa [hr i hi, if_neg hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_setOf_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₁.1, if_pos h₁.2]
      · rw [hr j h₂, if_neg]
        simpa [h₂] using h₁
#align dfinsupp.lex_fibration DFinsupp.lex_fibration

variable {r s}

theorem Lex.acc_of_single_erase [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
    (hs : Acc (DFinsupp.Lex r s) <| single i (x i)) (hu : Acc (DFinsupp.Lex r s) <| x.erase i) :
    Acc (DFinsupp.Lex r s) x := by
  classical
    convert ← @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{i}, _⟩
      (InvImage.accessible snd <| hs.prod_gameAdd hu)
    convert piecewise_single_erase x i
#align dfinsupp.lex.acc_of_single_erase DFinsupp.Lex.acc_of_single_erase

variable (hbot : ∀ ⦃i a⦄, ¬s i a 0)

theorem Lex.acc_zero : Acc (DFinsupp.Lex r s) 0 :=
  Acc.intro 0 fun _ ⟨_, _, h⟩ => (hbot h).elim
#align dfinsupp.lex.acc_zero DFinsupp.Lex.acc_zero

theorem Lex.acc_of_single [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i) :
    (∀ i ∈ x.support, Acc (DFinsupp.Lex r s) <| single i (x i)) → Acc (DFinsupp.Lex r s) x := by
  generalize ht : x.support = t; revert x
  classical
    induction' t using Finset.induction with b t hb ih
    · intro x ht
      rw [support_eq_empty.1 ht]
      exact fun _ => Lex.acc_zero hbot
    refine fun x ht h => Lex.acc_of_single_erase b (h b <| t.mem_insert_self b) ?_
    refine ih _ (by rw [support_erase, ht, Finset.erase_insert hb]) fun a ha => ?_
    rw [erase_ne (ha.ne_of_not_mem hb)]
    exact h a (Finset.mem_insert_of_mem ha)
#align dfinsupp.lex.acc_of_single DFinsupp.Lex.acc_of_single

variable (hs : ∀ i, WellFounded (s i))

theorem Lex.acc_single [DecidableEq ι] {i : ι} (hi : Acc (rᶜ ⊓ (· ≠ ·)) i) :
    ∀ a, Acc (DFinsupp.Lex r s) (single i a) := by
  induction' hi with i _ ih
  refine fun a => WellFounded.induction (hs i)
    (C := fun x ↦ Acc (DFinsupp.Lex r s) (single i x)) a fun a ha ↦ ?_
  refine Acc.intro _ fun x ↦ ?_
  rintro ⟨k, hr, hs⟩
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  classical
    refine Lex.acc_of_single hbot x fun j hj ↦ ?_
    obtain rfl | hij := eq_or_ne i j
    · exact ha _ hs
    by_cases h : r j i
    · rw [hr j h, single_eq_of_ne hij, single_zero]
      exact Lex.acc_zero hbot
    · exact ih _ ⟨h, hij.symm⟩ _
#align dfinsupp.lex.acc_single DFinsupp.Lex.acc_single

theorem Lex.acc [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i)
    (h : ∀ i ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) i) : Acc (DFinsupp.Lex r s) x :=
  Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _
#align dfinsupp.lex.acc DFinsupp.Lex.acc

theorem Lex.wellFounded (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (DFinsupp.Lex r s) :=
  ⟨fun x => by classical exact Lex.acc hbot hs x fun i _ => hr.apply i⟩
#align dfinsupp.lex.well_founded DFinsupp.Lex.wellFounded

theorem Lex.wellFounded' [IsTrichotomous ι r] (hr : WellFounded (Function.swap r)) :
    WellFounded (DFinsupp.Lex r s) :=
  Lex.wellFounded hbot hs <| Subrelation.wf
   (fun {i j} h => ((@IsTrichotomous.trichotomous ι r _ i j).resolve_left h.1).resolve_left h.2) hr
#align dfinsupp.lex.well_founded' DFinsupp.Lex.wellFounded'

end Zero

instance Lex.wellFoundedLT [LT ι] [IsTrichotomous ι (· < ·)] [hι : WellFoundedGT ι]
    [∀ i, CanonicallyOrderedAddCommMonoid (α i)] [hα : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨Lex.wellFounded' (fun _ a => (zero_le a).not_lt) (fun i => (hα i).wf) hι.wf⟩
#align dfinsupp.lex.well_founded_lt DFinsupp.Lex.wellFoundedLT

end DFinsupp

open DFinsupp

variable (r : ι → ι → Prop) {s : ∀ i, α i → α i → Prop}

theorem Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs : ∀ i, WellFounded (s i)) :
    WellFounded (Pi.Lex r (fun {i} ↦ s i)) := by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
  · convert emptyWf.wf
  letI : ∀ i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  haveI := IsTrans.swap r; haveI := IsIrrefl.swap r; haveI := Fintype.ofFinite ι
  refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
  exacts [(hs i).not_lt_min ⊤ _ trivial, Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]
#align pi.lex.well_founded Pi.Lex.wellFounded

instance Pi.Lex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i, LT (α i)]
    [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (∀ i, α i)) :=
  ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩
#align pi.lex.well_founded_lt Pi.Lex.wellFoundedLT

instance Function.Lex.wellFoundedLT {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoundedLT α] :
    WellFoundedLT (Lex (ι → α)) :=
  Pi.Lex.wellFoundedLT
#align function.lex.well_founded_lt Function.Lex.wellFoundedLT

theorem DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [∀ i, Zero (α i)]
    (hs : ∀ i, WellFounded (s i)) : WellFounded (DFinsupp.Lex r s) :=
  have := Fintype.ofFinite ι
  InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)
#align dfinsupp.lex.well_founded_of_finite DFinsupp.Lex.wellFounded_of_finite

instance DFinsupp.Lex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i, Zero (α i)]
    [∀ i, LT (α i)] [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩
#align dfinsupp.lex.well_founded_lt_of_finite DFinsupp.Lex.wellFoundedLT_of_finite

protected theorem DFinsupp.wellFoundedLT [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] (hbot : ∀ ⦃i⦄ ⦃a : α i⦄, ¬a < 0) : WellFoundedLT (Π₀ i, α i) :=
  ⟨by
    set β := fun i ↦ Antisymmetrization (α i) (· ≤ ·)
    set e : (i : ι) → α i → β i := fun i ↦ toAntisymmetrization (· ≤ ·)
    let _ : ∀ i, Zero (β i) := fun i ↦ ⟨e i 0⟩
    have : WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
        (fun _ ↦ (· < ·) : (i : ι) → β i → β i → Prop)) := by
      have := IsTrichotomous.swap (@WellOrderingRel ι)
      refine Lex.wellFounded' ?_ (fun i ↦ IsWellFounded.wf) ?_
      · rintro i ⟨a⟩
        apply hbot
      · #adaptation_note /-- nightly-2024-03-16: simp was
        simp (config := { unfoldPartialApp := true }) only [Function.swap] -/
        simp only [Function.swap_def]
        exact IsWellFounded.wf
    refine Subrelation.wf (fun h => ?_) <| InvImage.wf (mapRange (fun i ↦ e i) fun _ ↦ rfl) this
    have := IsStrictOrder.swap (@WellOrderingRel ι)
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
    exact ⟨i, fun j hj ↦ Quot.sound (he j hj), hl⟩⟩
#align dfinsupp.well_founded_lt DFinsupp.wellFoundedLT

instance DFinsupp.wellFoundedLT' [∀ i, CanonicallyOrderedAddCommMonoid (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  DFinsupp.wellFoundedLT fun _i a => (zero_le a).not_lt
#align dfinsupp.well_founded_lt' DFinsupp.wellFoundedLT'

instance Pi.wellFoundedLT [Finite ι] [∀ i, Preorder (α i)] [hw : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (∀ i, α i) :=
  ⟨by
    obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
    · convert emptyWf.wf
    letI : ∀ i, Zero (α i) := fun i => ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩
    haveI := Fintype.ofFinite ι
    refine InvImage.wf equivFunOnFintype.symm (DFinsupp.wellFoundedLT fun i a => ?_).wf
    exact (hw i).wf.not_lt_min ⊤ _ trivial⟩
#align pi.well_founded_lt Pi.wellFoundedLT

instance Function.wellFoundedLT {α} [Finite ι] [Preorder α] [WellFoundedLT α] :
    WellFoundedLT (ι → α) :=
  Pi.wellFoundedLT
#align function.well_founded_lt Function.wellFoundedLT

instance DFinsupp.wellFoundedLT_of_finite [Finite ι] [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  have := Fintype.ofFinite ι
  ⟨InvImage.wf equivFunOnFintype Pi.wellFoundedLT.wf⟩
#align dfinsupp.well_founded_lt_of_finite DFinsupp.wellFoundedLT_of_finite
