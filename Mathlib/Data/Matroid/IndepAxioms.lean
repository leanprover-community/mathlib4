/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Matroid.Basic

/-!
# Matroid Independence and Basis axioms

Matroids in mathlib are defined axiomatically in terms of bases,
but can be described just as naturally via their collections of independent sets,
and in fact such a description, being more 'verbose', can often be useful.
As well as this, the definition of a `Matroid` uses an unwieldy 'maximality'
axiom that can be dropped in cases where there is some finiteness assumption.

This file provides several ways to do define a matroid in terms of its independence or base
predicates, using axiom sets that are appropriate in different settings,
and often much simpler than the general definition.
It also contains `simp` lemmas and typeclasses as appropriate.

All the independence axiom sets need nontriviality (the empty set is independent),
monotonicity (subsets of independent sets are independent),
and some form of 'augmentation' axiom, which allows one to enlarge a non-maximal independent set.
This augmentation axiom is still required when there are finiteness assumptions, but is simpler.
It just states that if `I` is a finite independent set and `J` is a larger finite
independent set, then there exists `e ∈ J \ I` for which `insert e I` is independent.
This is the axiom that appears in most of the definitions.

## Implementation Details

To facilitate building a matroid from its independent sets, we define a structure `IndepMatroid`
which has a ground set `E`, an independence predicate `Indep`, and some axioms as its fields.
This structure is another encoding of the data in a `Matroid`; the function `IndepMatroid.matroid`
constructs a `Matroid` from an `IndepMatroid`.

This is convenient because if one wants to define `M : Matroid α` from a known independence
predicate `Ind`, it is easier to define an `M' : IndepMatroid α` so that `M'.Indep = Ind` and
then set `M = M'.matroid` than it is to directly define `M` with the base axioms.
The simp lemma `IndepMatroid.matroid_indep_iff` is important here; it shows that `M.Indep = Ind`,
so the `Matroid` constructed is the right one, and the intermediate `IndepMatroid` can be
made essentially invisible by the simplifier when working with `M`.

Because of this setup, we don't define any API for `IndepMatroid`, as it would be
a redundant copy of the existing API for `Matroid.Indep`.
(In particular, one could define a natural equivalence `e : IndepMatroid α ≃ Matroid α`
with `e.toFun = IndepMatroid.matroid`, but this would be pointless, as there is no need
for the inverse of `e`).

## Main definitions


* `IndepMatroid α` is a matroid structure on `α` described in terms of its independent sets
  in full generality, using infinite versions of the axioms.

* `IndepMatroid.matroid` turns `M' : IndepMatroid α` into `M : Matroid α` with `M'.Indep = M.Indep`.

* `IndepMatroid.ofFinitary` constructs an `IndepMatroid` whose associated `Matroid` is `Finitary`
  in the special case where independence of a set is determined only by that of its
  finite subsets. This construction uses Zorn's lemma.

* `IndepMatroid.ofFinitaryCardAugment` is a variant of `IndepMatroid.ofFinitary` where the
  augmentation axiom resembles the finite augmentation axiom.

* `IndepMatroid.ofBdd` constructs an `IndepMatroid` in the case where there is some known
  absolute upper bound on the size of an independent set. This uses the infinite version of
  the augmentation axiom; the corresponding `Matroid` is `RankFinite`.

* `IndepMatroid.ofBddAugment` is the same as the above, but with a finite augmentation axiom.

* `IndepMatroid.ofFinite` constructs an `IndepMatroid` from a finite ground set in terms of
  its independent sets.

* `IndepMatroid.ofFinset` constructs an `IndepMatroid α` whose corresponding matroid is `Finitary`
  from an independence predicate on `Finset α`.

* `Matroid.ofExistsMatroid` constructs a 'copy' of a matroid that is known only
  existentially, but whose independence predicate is known explicitly.

* `Matroid.ofExistsFiniteIsBase` constructs a matroid from its bases, if it is known that one
  of them is finite. This gives a `RankFinite` matroid.

* `Matroid.ofIsBaseOfFinite` constructs a `Finite` matroid from its bases.
-/

assert_not_exists Field

open Set Matroid

variable {α : Type*}

section IndepMatroid

/-- A matroid as defined by a ground set and an independence predicate.
This definition is an implementation detail whose purpose is to organize the multiple
different versions of the independence axioms;
usually, terms of type `IndepMatroid` should either be directly piped into `IndepMatroid.matroid`,
or should be constructed as a private definition
which is then converted into a matroid via `IndepMatroid.matroid`.

To define a `Matroid α` from a known independence predicate
`MyIndep : Set α → Prop` and ground set `E : Set α`, one can either write
```
def myMatroid (…) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofFoo E MyIndep _ _ … _
```
or, slightly more indirectly,
```
private def myIndepMatroid (…) : IndepMatroid α := IndepMatroid.ofFoo E MyIndep _ _ … _

def myMatroid (…) : Matroid α := (myIndepMatroid …).matroid
```
In both cases, `IndepMatroid.ofFoo` is either `IndepMatroid.mk`,
or one of the several other available constructors for `IndepMatroid`,
and the `_` represent the proofs that this constructor requires.

After such a definition is made, the facts that `myMatroid.Indep = myIndep` and `myMatroid.E = E`
are true by either `rfl` or `simp [myMatroid]`, and can be made directly into @[simp] lemmas.
-/
structure IndepMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The independence predicate -/
  (Indep : Set α → Prop)
  (indep_empty : Indep ∅)
  (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
  (indep_aug : ∀ ⦃I B⦄, Indep I → ¬ Maximal Indep I →
    Maximal Indep B → ∃ x ∈ B \ I, Indep (insert x I))
  (indep_maximal : ∀ X, X ⊆ E → ExistsMaximalSubsetProperty Indep X)
  (subset_ground : ∀ I, Indep I → I ⊆ E)

namespace IndepMatroid

/-- An `M : IndepMatroid α` gives a `Matroid α` whose bases are the maximal `M`-independent sets. -/
@[simps] protected def matroid (M : IndepMatroid α) : Matroid α where
  E := M.E
  IsBase := Maximal M.Indep
  Indep := M.Indep
  indep_iff' := by
    refine fun I ↦ ⟨fun h ↦ ?_, fun ⟨B, ⟨h, _⟩, hIB'⟩ ↦ M.indep_subset h hIB'⟩
    obtain ⟨J, hIJ, hmax⟩ := M.indep_maximal M.E rfl.subset I h (M.subset_ground I h)
    rw [maximal_and_iff_right_of_imp M.subset_ground] at hmax
    exact ⟨J, hmax.1, hIJ⟩
  exists_isBase := by
    obtain ⟨B, -, hB⟩ := M.indep_maximal M.E rfl.subset ∅ M.indep_empty <| empty_subset _
    rw [maximal_and_iff_right_of_imp M.subset_ground] at hB
    exact ⟨B, hB.1⟩
  isBase_exchange B B' hB hB' e he := by
    have hnotmax : ¬ Maximal M.Indep (B \ {e}) :=
      fun h ↦ h.not_prop_of_ssuperset (diff_singleton_ssubset.2 he.1) hB.prop
    obtain ⟨f, hf, hfB⟩ := M.indep_aug (M.indep_subset hB.prop diff_subset) hnotmax hB'
    replace hf := show f ∈ B' \ B by simpa [show f ≠ e by rintro rfl; exact he.2 hf.1] using hf
    refine ⟨f, hf, by_contra fun hnot ↦ ?_⟩
    obtain ⟨x, hxB, hind⟩ := M.indep_aug hfB hnot hB
    obtain ⟨-, rfl⟩ : _ ∧ x = e := by simpa [hxB.1] using hxB
    refine hB.not_prop_of_ssuperset ?_ hind
    rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1]
    exact ssubset_insert hf.2
  maximality := M.indep_maximal
  subset_ground B hB := M.subset_ground B hB.1

@[simp] theorem matroid_indep_iff {M : IndepMatroid α} {I : Set α} :
    M.matroid.Indep I ↔ M.Indep I := Iff.rfl

/-- If `Indep` has the 'compactness' property that each set `I` satisfies `Indep I` if and only if
`Indep J` for every finite subset `J` of `I`,
then an `IndepMatroid` can be constructed without proving the maximality axiom.
This needs choice, since it can be used to prove that every vector space has a basis. -/
@[simps E] protected def ofFinitary (E : Set α) (Indep : Set α → Prop)
    (indep_empty : Indep ∅)
    (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (indep_aug : ∀ ⦃I B⦄, Indep I → ¬ Maximal Indep I → Maximal Indep B →
      ∃ x ∈ B \ I, Indep (insert x I))
    (indep_compact : ∀ I, (∀ J, J ⊆ I → J.Finite → Indep J) → Indep I)
    (subset_ground : ∀ I, Indep I → I ⊆ E) : IndepMatroid α where
  E := E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal := by
    refine fun X _ I hI hIX ↦ zorn_subset_nonempty {Y | Indep Y ∧ Y ⊆ X} ?_ I ⟨hI, hIX⟩
    refine fun Is hIs hchain _ ↦
      ⟨⋃₀ Is, ⟨?_, sUnion_subset fun Y hY ↦ (hIs hY).2⟩, fun _ ↦ subset_sUnion_of_mem⟩
    refine indep_compact _ fun J hJ hJfin ↦ ?_
    have hchoose : ∀ e, e ∈ J → ∃ I, I ∈ Is ∧ (e : α) ∈ I := fun _ he ↦ mem_sUnion.1 <| hJ he
    choose! f hf using hchoose
    refine J.eq_empty_or_nonempty.elim (fun hJ ↦ hJ ▸ indep_empty) (fun hne ↦ ?_)
    obtain ⟨x, hxJ, hxmax⟩ := Finite.exists_maximalFor f _ hJfin hne
    refine indep_subset (hIs (hf x hxJ).1).1 fun y hyJ ↦ ?_
    obtain (hle | hle) := hchain.total (hf _ hxJ).1 (hf _ hyJ).1
    · exact hxmax hyJ hle <| (hf _ hyJ).2
    · exact hle (hf _ hyJ).2
  subset_ground := subset_ground

@[simp] theorem ofFinitary_indep (E : Set α) (Indep : Set α → Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground :
    (IndepMatroid.ofFinitary
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).Indep = Indep := rfl

instance ofFinitary_finitary (E : Set α) (Indep : Set α → Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground : Finitary
    (IndepMatroid.ofFinitary
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).matroid :=
  ⟨by simpa⟩

/-- An independence predicate satisfying the finite matroid axioms determines a matroid,
provided independence is determined by its behaviour on finite sets. -/
@[simps! E] protected def ofFinitaryCardAugment (E : Set α) (Indep : Set α → Prop)
    (indep_empty : Indep ∅)
    (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (indep_aug : ∀ ⦃I J⦄, Indep I → I.Finite → Indep J → J.Finite → I.ncard < J.ncard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (indep_compact : ∀ I, (∀ J, J ⊆ I → J.Finite → Indep J) → Indep I)
    (subset_ground : ∀ I, Indep I → I ⊆ E) : IndepMatroid α :=
  IndepMatroid.ofFinitary
    (E := E)
    (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_compact := indep_compact)
    (indep_aug := by
      have htofin : ∀ I e, Indep I → ¬ Indep (insert e I) →
        ∃ I₀, I₀ ⊆ I ∧ I₀.Finite ∧ ¬ Indep (insert e I₀) := by
        by_contra h; push_neg at h
        obtain ⟨I, e, -, hIe, h⟩ := h
        refine hIe <| indep_compact _ fun J hJss hJfin ↦ ?_
        exact indep_subset (h (J \ {e}) (by rwa [diff_subset_iff]) hJfin.diff) (by simp)
      intro I B hI hImax hBmax
      obtain ⟨e, heI, hins⟩ := exists_insert_of_not_maximal indep_subset hI hImax
      by_cases heB : e ∈ B
      · exact ⟨e, ⟨heB, heI⟩, hins⟩
      by_contra hcon; push_neg at hcon
      have heBdep := hBmax.not_prop_of_ssuperset (ssubset_insert heB)
      -- There is a finite subset `B₀` of `B` so that `B₀ + e` is dependent
      obtain ⟨B₀, hB₀B, hB₀fin, hB₀e⟩ := htofin B e hBmax.1 heBdep
      have hB₀ := indep_subset hBmax.1 hB₀B
      -- `I` has a finite subset `I₀` that doesn't extend into `B₀`
      have hexI₀ : ∃ I₀, I₀ ⊆ I ∧ I₀.Finite ∧ ∀ x, x ∈ B₀ \ I₀ → ¬Indep (insert x I₀) := by
        have hch : ∀ (b : ↑(B₀ \ I)), ∃ Ib, Ib ⊆ I ∧ Ib.Finite ∧ ¬Indep (insert (b : α) Ib) := by
          rintro ⟨b, hb⟩; exact htofin I b hI (hcon b ⟨hB₀B hb.1, hb.2⟩)
        choose! f hf using hch
        have : Finite ↑(B₀ \ I) := hB₀fin.diff.to_subtype
        refine ⟨iUnion f ∪ (B₀ ∩ I),
          union_subset (iUnion_subset (fun i ↦ (hf i).1)) inter_subset_right,
          (finite_iUnion fun i ↦ (hf i).2.1).union (hB₀fin.subset inter_subset_left),
          fun x ⟨hxB₀, hxn⟩ hi ↦ ?_⟩
        have hxI : x ∉ I := fun hxI ↦ hxn <| Or.inr ⟨hxB₀, hxI⟩
        refine (hf ⟨x, ⟨hxB₀, hxI⟩⟩).2.2 (indep_subset hi <| insert_subset_insert ?_)
        apply subset_union_of_subset_left
        apply subset_iUnion
      obtain ⟨I₀, hI₀I, hI₀fin, hI₀⟩ := hexI₀
      set E₀ := insert e (I₀ ∪ B₀)
      have hE₀fin : E₀.Finite := (hI₀fin.union hB₀fin).insert e
      -- Extend `B₀` to a maximal independent subset of `I₀ ∪ B₀ + e`
      obtain ⟨J, ⟨hB₀J, hJ, hJss⟩, hJmax⟩ := Finite.exists_maximalFor (f := id)
        (s := {J | B₀ ⊆ J ∧ Indep J ∧ J ⊆ E₀})
        (hE₀fin.finite_subsets.subset (by simp))
        ⟨B₀, Subset.rfl, hB₀, subset_union_right.trans (subset_insert _ _)⟩
      have heI₀ : e ∉ I₀ := notMem_subset hI₀I heI
      have heI₀i : Indep (insert e I₀) := indep_subset hins (insert_subset_insert hI₀I)
      have heJ : e ∉ J := fun heJ ↦ hB₀e (indep_subset hJ <| insert_subset heJ hB₀J)
      have hJfin := hE₀fin.subset hJss
      -- We have `|I₀ + e| ≤ |J|`, since otherwise we could extend the maximal set `J`
      have hcard : (insert e I₀).ncard ≤ J.ncard := by
        refine not_lt.1 fun hlt ↦ ?_
        obtain ⟨f, hfI, hfJ, hfi⟩ := indep_aug hJ hJfin heI₀i (hI₀fin.insert e) hlt
        have hfE₀ : f ∈ E₀ := mem_of_mem_of_subset hfI (insert_subset_insert subset_union_left)
        exact hfJ <| insert_eq_self.1 <| le_imp_eq_iff_le_imp_ge'.2 (hJmax
          ⟨hB₀J.trans <| subset_insert _ _, hfi, insert_subset hfE₀ hJss⟩) (subset_insert _ _)
      -- But this means `|I₀| < |J|`, and extending `I₀` into `J` gives a contradiction
      rw [ncard_insert_of_notMem heI₀ hI₀fin, ← Nat.lt_iff_add_one_le] at hcard
      obtain ⟨f, hfJ, hfI₀, hfi⟩ := indep_aug (indep_subset hI hI₀I) hI₀fin hJ hJfin hcard
      exact hI₀ f ⟨Or.elim (hJss hfJ) (fun hfe ↦ (heJ <| hfe ▸ hfJ).elim) (by aesop), hfI₀⟩ hfi )
  (subset_ground := subset_ground)

@[simp] theorem ofFinitaryCardAugment_indep (E : Set α) (Indep : Set α → Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground :
    (IndepMatroid.ofFinitaryCardAugment
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).Indep = Indep := rfl

instance ofFinitaryCardAugment_finitary (E : Set α) (Indep : Set α → Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground : Finitary
    (IndepMatroid.ofFinitaryCardAugment
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).matroid :=
  ⟨by simpa⟩

/-- If there is an absolute upper bound on the size of a set satisfying `P`, then the
  maximal subset property always holds. -/
theorem _root_.Matroid.existsMaximalSubsetProperty_of_bdd {P : Set α → Prop}
    (hP : ∃ (n : ℕ), ∀ Y, P Y → Y.encard ≤ n) (X : Set α) : ExistsMaximalSubsetProperty P X := by
  obtain ⟨n, hP⟩ := hP
  rintro I hI hIX
  have hfin : Set.Finite (ncard '' {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}) := by
    rw [finite_iff_bddAbove, bddAbove_def]
    simp_rw [ENat.le_coe_iff] at hP
    use n
    rintro x ⟨Y, ⟨hY,-,-⟩, rfl⟩
    obtain ⟨n₀, heq, hle⟩ := hP Y hY
    rwa [ncard_def, heq, ENat.toNat_coe]
  obtain ⟨Y, ⟨hY, hIY, hYX⟩, hY'⟩ :=
    Finite.exists_maximalFor' ncard _ hfin ⟨I, hI, rfl.subset, hIX⟩
  refine ⟨Y, hIY, ⟨hY, hYX⟩, fun K ⟨hPK, hKX⟩ hYK ↦ ?_⟩
  have hKfin : K.Finite := finite_of_encard_le_coe (hP K hPK)
  refine (eq_of_subset_of_ncard_le hYK ?_ hKfin).symm.subset
  exact hY' ⟨hPK, hIY.trans hYK, hKX⟩ (ncard_le_ncard hYK hKfin)

/-- If there is an absolute upper bound on the size of an independent set, then the maximality axiom
  isn't needed to define a matroid by independent sets. -/
@[simps E] protected def ofBdd (E : Set α) (Indep : Set α → Prop)
    (indep_empty : Indep ∅)
    (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (indep_aug : ∀ ⦃I B⦄, Indep I → ¬ Maximal Indep I → Maximal Indep B →
      ∃ x ∈ B \ I, Indep (insert x I))
    (subset_ground : ∀ I, Indep I → I ⊆ E)
    (indep_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n) : IndepMatroid α where
  E := E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal X _ := Matroid.existsMaximalSubsetProperty_of_bdd indep_bdd X
  subset_ground := subset_ground

@[simp] theorem ofBdd_indep (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground h_bdd : (IndepMatroid.ofBdd
      E Indep indep_empty indep_subset indep_aug subset_ground h_bdd).Indep = Indep := rfl

/-- `IndepMatroid.ofBdd` constructs a `RankFinite` matroid. -/
instance (E : Set α) (Indep : Set α → Prop) indep_empty indep_subset indep_aug subset_ground h_bdd :
    RankFinite (IndepMatroid.ofBdd
      E Indep indep_empty indep_subset indep_aug subset_ground h_bdd).matroid := by
  obtain ⟨B, hB⟩ := (IndepMatroid.ofBdd E Indep _ _ _ _ _).matroid.exists_isBase
  refine hB.rankFinite_of_finite ?_
  obtain ⟨n, hn⟩ := h_bdd
  exact finite_of_encard_le_coe <| hn B (by simpa using hB.indep)

/-- If there is an absolute upper bound on the size of an independent set, then matroids
  can be defined using an 'augmentation' axiom similar to the standard definition of
  finite matroids for independent sets. -/
protected def ofBddAugment (E : Set α) (Indep : Set α → Prop)
    (indep_empty : Indep ∅)
    (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (indep_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (indep_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n)
    (subset_ground : ∀ I, Indep I → I ⊆ E) : IndepMatroid α :=
  IndepMatroid.ofBdd (E := E) (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      rintro I B hI hImax hBmax
      suffices hcard : I.encard < B.encard by
        obtain ⟨e, heB, heI, hi⟩ := indep_aug hI hBmax.prop hcard
        exact ⟨e, ⟨heB, heI⟩, hi⟩
      refine lt_of_not_ge fun hle ↦ ?_
      obtain ⟨x, hxnot, hxI⟩ := exists_insert_of_not_maximal indep_subset hI hImax
      have hlt : B.encard < (insert x I).encard := by
        rwa [encard_insert_of_notMem hxnot, ← not_le, ENat.add_one_le_iff, not_lt]
        rw [encard_ne_top_iff]
        obtain ⟨n, hn⟩ := indep_bdd
        exact finite_of_encard_le_coe (hn _ hI)
      obtain ⟨y, -, hyB, hi⟩ := indep_aug hBmax.prop hxI hlt
      exact hBmax.not_prop_of_ssuperset (ssubset_insert hyB) hi)
    (indep_bdd := indep_bdd) (subset_ground := subset_ground)

@[simp] theorem ofBddAugment_E (E : Set α) Indep indep_empty indep_subset indep_aug
    indep_bdd subset_ground : (IndepMatroid.ofBddAugment
      E Indep indep_empty indep_subset indep_aug indep_bdd subset_ground).E = E := rfl

@[simp] theorem ofBddAugment_indep (E : Set α) Indep indep_empty indep_subset indep_aug
    indep_bdd subset_ground : (IndepMatroid.ofBddAugment
      E Indep indep_empty indep_subset indep_aug indep_bdd subset_ground).Indep = Indep := rfl

instance ofBddAugment_rankFinite (E : Set α) Indep indep_empty indep_subset indep_aug
    indep_bdd subset_ground : RankFinite (IndepMatroid.ofBddAugment
      E Indep indep_empty indep_subset indep_aug indep_bdd subset_ground).matroid := by
  rw [IndepMatroid.ofBddAugment]
  infer_instance

/-- If `E` is finite, then any collection of subsets of `E` satisfying
  the usual independence axioms determines a matroid -/
protected def ofFinite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (indep_empty : Indep ∅)
    (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (indep_aug :
      ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (subset_ground : ∀ ⦃I⦄, Indep I → I ⊆ E) : IndepMatroid α :=
  IndepMatroid.ofBddAugment (E := E) (Indep := Indep) (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      refine fun {I J} hI hJ hIJ ↦ indep_aug hI hJ ?_
      rwa [← Nat.cast_lt (α := ℕ∞), (hE.subset (subset_ground hJ)).cast_ncard_eq,
        (hE.subset (subset_ground hI)).cast_ncard_eq] )
    (indep_bdd := ⟨E.ncard, fun I hI ↦ by
      rw [hE.cast_ncard_eq]
      exact encard_le_encard <| subset_ground hI ⟩)
    (subset_ground := subset_ground)

@[simp] theorem ofFinite_E {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground :
    (IndepMatroid.ofFinite
      (hE : E.Finite) Indep indep_empty indep_subset indep_aug subset_ground).E = E := rfl

@[simp] theorem ofFinite_indep {E : Set α} hE Indep indep_empty indep_subset indep_aug
    subset_ground : (IndepMatroid.ofFinite
      (hE : E.Finite) Indep indep_empty indep_subset indep_aug subset_ground).Indep = Indep := rfl

instance ofFinite_finite {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground :
    (IndepMatroid.ofFinite
      (hE : E.Finite) Indep indep_empty indep_subset indep_aug subset_ground).matroid.Finite :=
  ⟨hE⟩

/-- An independence predicate on `Finset α` that obeys the finite matroid axioms determines a
  finitary matroid on `α`. -/
protected def ofFinset [DecidableEq α] (E : Set α) (Indep : Finset α → Prop)
    (indep_empty : Indep ∅)
    (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (indep_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.card < J.card → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (subset_ground : ∀ ⦃I⦄, Indep I → (I : Set α) ⊆ E) : IndepMatroid α :=
  IndepMatroid.ofFinitaryCardAugment
    (E := E)
    (Indep := (fun I ↦ (∀ (J : Finset α), (J : Set α) ⊆ I → Indep J)))
    (indep_empty := by simpa [subset_empty_iff])
    (indep_subset := ( fun _ _ hJ hIJ _ hKI ↦ hJ _ (hKI.trans hIJ) ))
    (indep_aug := by
      intro I J hI hIfin hJ hJfin hIJ
      rw [ncard_eq_toFinset_card _ hIfin, ncard_eq_toFinset_card _ hJfin] at hIJ
      have aug := indep_aug (hI _ (by simp [Subset.rfl])) (hJ _ (by simp [Subset.rfl])) hIJ
      simp only [Finite.mem_toFinset] at aug
      obtain ⟨e, heJ, heI, hi⟩ := aug
      exact ⟨e, heJ, heI, fun K hK ↦ indep_subset hi <| Finset.coe_subset.1 (by simpa)⟩ )
    (indep_compact := fun _ h J hJ ↦ h _ hJ J.finite_toSet _ Subset.rfl )
    (subset_ground := fun I hI x hxI ↦ by simpa using subset_ground <| hI {x} (by simpa) )

@[simp] theorem ofFinset_E [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground : (IndepMatroid.ofFinset
      E Indep indep_empty indep_subset indep_aug subset_ground).E = E := rfl

@[simp] theorem ofFinset_indep [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground {I : Finset α} : (IndepMatroid.ofFinset
      E Indep indep_empty indep_subset indep_aug subset_ground).Indep I ↔ Indep I := by
  simp only [IndepMatroid.ofFinset, ofFinitaryCardAugment_indep, Finset.coe_subset]
  exact ⟨fun h ↦ h _ Subset.rfl, fun h J hJI ↦ indep_subset h hJI⟩

/-- This can't be `@[simp]`, because it would cause the more useful
  `Matroid.ofIndepFinset_apply` not to be in simp normal form. -/
theorem ofFinset_indep' [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground {I : Set α} : (IndepMatroid.ofFinset
      E Indep indep_empty indep_subset indep_aug subset_ground).Indep I ↔
        ∀ (J : Finset α), (J : Set α) ⊆ I → Indep J := by
  simp only [IndepMatroid.ofFinset, ofFinitaryCardAugment_indep]

end IndepMatroid

section IsBase

namespace Matroid

/-- Construct an `Matroid` from an independence predicate that agrees with that of some matroid `M`.
  This is computable even if `M` is only known existentially, or when `M` exists for different
  reasons in different cases. This can also be used to change the independence predicate to a
  more useful definitional form. -/
@[simps! E] protected def ofExistsMatroid (E : Set α) (Indep : Set α → Prop)
    (hM : ∃ (M : Matroid α), E = M.E ∧ ∀ I, M.Indep I ↔ Indep I) : Matroid α :=
  IndepMatroid.matroid <|
  have hex : ∃ (M : Matroid α), E = M.E ∧ M.Indep = Indep := by
    obtain ⟨M, rfl, h⟩ := hM; refine ⟨_, rfl, funext (by simp [h])⟩
  IndepMatroid.mk (E := E) (Indep := Indep)
  (indep_empty := by obtain ⟨M, -, rfl⟩ := hex; exact M.empty_indep)
  (indep_subset := by obtain ⟨M, -, rfl⟩ := hex; exact fun I J hJ hIJ ↦ hJ.subset hIJ)
  (indep_aug := by obtain ⟨M, -, rfl⟩ := hex; exact Indep.exists_insert_of_not_maximal M)
  (indep_maximal := by obtain ⟨M, rfl, rfl⟩ := hex; exact M.existsMaximalSubsetProperty_indep)
  (subset_ground := by obtain ⟨M, rfl, rfl⟩ := hex; exact fun I ↦ Indep.subset_ground)

/-- A matroid defined purely in terms of its bases. -/
@[simps E] protected def ofBase (E : Set α) (IsBase : Set α → Prop) (exists_isBase : ∃ B, IsBase B)
    (isBase_exchange : ExchangeProperty IsBase)
    (maximality : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty (∃ B, IsBase B ∧ · ⊆ B) X)
    (subset_ground : ∀ B, IsBase B → B ⊆ E) : Matroid α where
  E := E
  IsBase := IsBase
  Indep I := (∃ B, IsBase B ∧ I ⊆ B)
  indep_iff' _ := Iff.rfl
  exists_isBase := exists_isBase
  isBase_exchange := isBase_exchange
  maximality := maximality
  subset_ground := subset_ground

/-- A collection of bases with the exchange property and at least one finite member is a matroid -/
@[simps! E] protected def ofExistsFiniteIsBase (E : Set α) (IsBase : Set α → Prop)
    (exists_finite_base : ∃ B, IsBase B ∧ B.Finite) (isBase_exchange : ExchangeProperty IsBase)
    (subset_ground : ∀ B, IsBase B → B ⊆ E) : Matroid α := Matroid.ofBase
  (E := E)
  (IsBase := IsBase)
  (exists_isBase := by obtain ⟨B,h⟩ := exists_finite_base; exact ⟨B, h.1⟩)
  (isBase_exchange := isBase_exchange)
  (maximality := by
    obtain ⟨B, hB, hfin⟩ := exists_finite_base
    refine fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd
      ⟨B.ncard, fun Y ⟨B', hB', hYB'⟩ ↦ ?_⟩ X
    rw [hfin.cast_ncard_eq, isBase_exchange.encard_isBase_eq hB hB']
    exact encard_mono hYB')
  (subset_ground := subset_ground)

@[simp] theorem ofExistsFiniteIsBase_isBase (E : Set α) IsBase exists_finite_base
    isBase_exchange subset_ground : (Matroid.ofExistsFiniteIsBase
      E IsBase exists_finite_base isBase_exchange subset_ground).IsBase = IsBase := rfl

instance ofExistsFiniteIsBase_rankFinite (E : Set α) IsBase exists_finite_base
    isBase_exchange subset_ground : RankFinite (Matroid.ofExistsFiniteIsBase
      E IsBase exists_finite_base isBase_exchange subset_ground) := by
  obtain ⟨B, hB, hfin⟩ := exists_finite_base
  exact Matroid.IsBase.rankFinite_of_finite (by simpa) hfin

/-- If `E` is finite, then any nonempty collection of its subsets
  with the exchange property is the collection of bases of a matroid on `E`. -/
protected def ofIsBaseOfFinite {E : Set α} (hE : E.Finite) (IsBase : Set α → Prop)
    (exists_isBase : ∃ B, IsBase B) (isBase_exchange : ExchangeProperty IsBase)
    (subset_ground : ∀ B, IsBase B → B ⊆ E) : Matroid α :=
  Matroid.ofExistsFiniteIsBase (E := E) (IsBase := IsBase)
    (exists_finite_base :=
      let ⟨B, hB⟩ := exists_isBase
      ⟨B, hB, hE.subset (subset_ground B hB)⟩)
    (isBase_exchange := isBase_exchange)
    (subset_ground := subset_ground)

@[simp] theorem ofIsBaseOfFinite_E {E : Set α} (hE : E.Finite) IsBase exists_isBase isBase_exchange
    subset_ground : (Matroid.ofIsBaseOfFinite
      hE IsBase exists_isBase isBase_exchange subset_ground).E = E := rfl

@[simp] theorem ofIsBaseOfFinite_isBase {E : Set α} (hE : E.Finite) IsBase exists_isBase
    isBase_exchange subset_ground : (Matroid.ofIsBaseOfFinite
      hE IsBase exists_isBase isBase_exchange subset_ground).IsBase = IsBase := rfl

instance ofBaseOfFinite_finite {E : Set α} (hE : E.Finite) IsBase exists_isBase
    isBase_exchange subset_ground : (Matroid.ofIsBaseOfFinite
      hE IsBase exists_isBase isBase_exchange subset_ground).Finite :=
  ⟨hE⟩

end Matroid

end IsBase

end IndepMatroid
