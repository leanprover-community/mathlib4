/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Reid Barton
-/
import Mathlib.Topology.Separation

#align_import topology.shrinking_lemma from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# The shrinking lemma

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → Set X` there exists a refinement `v : ι → Set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_iUnion_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_iUnion_eq_closure_subset` deals with a covering of the whole space.

## Tags

normal space, shrinking lemma
-/


open Set Function

open scoped Classical

noncomputable section

variable {ι X : Type*} [TopologicalSpace X] [NormalSpace X]

namespace ShrinkingLemma

-- the trivial refinement needs `u` to be a covering
/-- Auxiliary definition for the proof of the shrinking lemma. A partial refinement of a covering
`⋃ i, u i` of a set `s` is a map `v : ι → Set X` and a set `carrier : Set ι` such that

* `s ⊆ ⋃ i, v i`;
* all `v i` are open;
* if `i ∈ carrier v`, then `closure (v i) ⊆ u i`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the following partial order: `v ≤ v'` if `v.carrier ⊆ v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use Zorn's lemma to prove that this type has
a maximal element, then show that the maximal element must have `carrier = univ`. -/
-- porting note: @[nolint has_nonempty_instance] is not here yet
@[ext] structure PartialRefinement (u : ι → Set X) (s : Set X) where
  /-- A family of sets that form a partial refinement of `u`. -/
  toFun : ι → Set X
  /-- The set of indexes `i` such that `i`-th set is already shrunk. -/
  carrier : Set ι
  /-- Each set from the partially refined family is open. -/
  protected isOpen : ∀ i, IsOpen (toFun i)
  /-- The partially refined family still covers the set. -/
  subset_iUnion : s ⊆ ⋃ i, toFun i
  /-- For each `i ∈ carrier`, the original set includes the closure of the refined set. -/
  closure_subset : ∀ {i}, i ∈ carrier → closure (toFun i) ⊆ u i
  /-- Sets that correspond to `i ∉ carrier` are not modified. -/
  apply_eq : ∀ {i}, i ∉ carrier → toFun i = u i
#align shrinking_lemma.partial_refinement ShrinkingLemma.PartialRefinement

namespace PartialRefinement

variable {u : ι → Set X} {s : Set X}

instance : CoeFun (PartialRefinement u s) fun _ => ι → Set X := ⟨toFun⟩

#align shrinking_lemma.partial_refinement.subset_Union ShrinkingLemma.PartialRefinement.subset_iUnion
#align shrinking_lemma.partial_refinement.closure_subset ShrinkingLemma.PartialRefinement.closure_subset
#align shrinking_lemma.partial_refinement.apply_eq ShrinkingLemma.PartialRefinement.apply_eq
#align shrinking_lemma.partial_refinement.is_open ShrinkingLemma.PartialRefinement.isOpen

protected theorem subset (v : PartialRefinement u s) (i : ι) : v i ⊆ u i :=
  if h : i ∈ v.carrier then subset_closure.trans (v.closure_subset h) else (v.apply_eq h).le
#align shrinking_lemma.partial_refinement.subset ShrinkingLemma.PartialRefinement.subset

instance : PartialOrder (PartialRefinement u s) where
  le v₁ v₂ := v₁.carrier ⊆ v₂.carrier ∧ ∀ i ∈ v₁.carrier, v₁ i = v₂ i
  le_refl v := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans v₁ v₂ v₃ h₁₂ h₂₃ :=
    ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm v₁ v₂ h₁₂ h₂₁ :=
    have hc : v₁.carrier = v₂.carrier := Subset.antisymm h₁₂.1 h₂₁.1
    PartialRefinement.ext _ _
      (funext fun x =>
        if hx : x ∈ v₁.carrier then h₁₂.2 _ hx
        else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

/-- If two partial refinements `v₁`, `v₂` belong to a chain (hence, they are comparable)
and `i` belongs to the carriers of both partial refinements, then `v₁ i = v₂ i`. -/
theorem apply_eq_of_chain {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c) {v₁ v₂}
    (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) :
    v₁ i = v₂ i :=
  (hc.total h₁ h₂).elim (fun hle => hle.2 _ hi₁) (fun hle => (hle.2 _ hi₂).symm)
#align shrinking_lemma.partial_refinement.apply_eq_of_chain ShrinkingLemma.PartialRefinement.apply_eq_of_chain

/-- The carrier of the least upper bound of a non-empty chain of partial refinements is the union of
their carriers. -/
def chainSupCarrier (c : Set (PartialRefinement u s)) : Set ι :=
  ⋃ v ∈ c, carrier v
#align shrinking_lemma.partial_refinement.chain_Sup_carrier ShrinkingLemma.PartialRefinement.chainSupCarrier

/-- Choice of an element of a nonempty chain of partial refinements. If `i` belongs to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements. -/
def find (c : Set (PartialRefinement u s)) (ne : c.Nonempty) (i : ι) : PartialRefinement u s :=
  if hi : ∃ v ∈ c, i ∈ carrier v then hi.choose else ne.some
#align shrinking_lemma.partial_refinement.find ShrinkingLemma.PartialRefinement.find

theorem find_mem {c : Set (PartialRefinement u s)} (i : ι) (ne : c.Nonempty) : find c ne i ∈ c := by
  rw [find]
  -- ⊢ (if hi : ∃ v, v ∈ c ∧ i ∈ v.carrier then Exists.choose hi else Set.Nonempty. …
  split_ifs with h
  -- ⊢ Exists.choose h ∈ c
  exacts [h.choose_spec.1, ne.some_mem]
  -- 🎉 no goals
#align shrinking_lemma.partial_refinement.find_mem ShrinkingLemma.PartialRefinement.find_mem

theorem mem_find_carrier_iff {c : Set (PartialRefinement u s)} {i : ι} (ne : c.Nonempty) :
    i ∈ (find c ne i).carrier ↔ i ∈ chainSupCarrier c := by
  rw [find]
  -- ⊢ i ∈ (if hi : ∃ v, v ∈ c ∧ i ∈ v.carrier then Exists.choose hi else Set.Nonem …
  split_ifs with h
  -- ⊢ i ∈ (Exists.choose h).carrier ↔ i ∈ chainSupCarrier c
  · have := h.choose_spec
    -- ⊢ i ∈ (Exists.choose h).carrier ↔ i ∈ chainSupCarrier c
    exact iff_of_true this.2 (mem_iUnion₂.2 ⟨_, this.1, this.2⟩)
    -- 🎉 no goals
  · push_neg at h
    -- ⊢ i ∈ (Set.Nonempty.some ne).carrier ↔ i ∈ chainSupCarrier c
    refine iff_of_false (h _ ne.some_mem) ?_
    -- ⊢ ¬i ∈ chainSupCarrier c
    simpa only [chainSupCarrier, mem_iUnion₂, not_exists]
    -- 🎉 no goals
#align shrinking_lemma.partial_refinement.mem_find_carrier_iff ShrinkingLemma.PartialRefinement.mem_find_carrier_iff

theorem find_apply_of_mem {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c)
    (ne : c.Nonempty) {i v} (hv : v ∈ c) (hi : i ∈ carrier v) : find c ne i i = v i :=
  apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_iUnion₂.2 ⟨v, hv, hi⟩)
    hi
#align shrinking_lemma.partial_refinement.find_apply_of_mem ShrinkingLemma.PartialRefinement.find_apply_of_mem

/-- Least upper bound of a nonempty chain of partial refinements. -/
def chainSup (c : Set (PartialRefinement u s)) (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) : PartialRefinement u s where
  toFun i := find c ne i i
  carrier := chainSupCarrier c
  isOpen i := (find _ _ _).isOpen i
  subset_iUnion x hxs := mem_iUnion.2 <| by
    rcases em (∃ i, i ∉ chainSupCarrier c ∧ x ∈ u i) with (⟨i, hi, hxi⟩ | hx)
    -- ⊢ ∃ i, x ∈ (fun i => toFun (find c ne i) i) i
    · use i
      -- ⊢ x ∈ (fun i => toFun (find c ne i) i) i
      simpa only [(find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
      -- 🎉 no goals
    · simp_rw [not_exists, not_and, not_imp_not, chainSupCarrier, mem_iUnion₂] at hx
      -- ⊢ ∃ i, x ∈ (fun i => toFun (find c ne i) i) i
      haveI : Nonempty (PartialRefinement u s) := ⟨ne.some⟩
      -- ⊢ ∃ i, x ∈ (fun i => toFun (find c ne i) i) i
      choose! v hvc hiv using hx
      -- ⊢ ∃ i, x ∈ (fun i => toFun (find c ne i) i) i
      rcases(hfin x hxs).exists_maximal_wrt v _ (mem_iUnion.1 (hU hxs)) with
        ⟨i, hxi : x ∈ u i, hmax : ∀ j, x ∈ u j → v i ≤ v j → v i = v j⟩
      rcases mem_iUnion.1 ((v i).subset_iUnion hxs) with ⟨j, hj⟩
      -- ⊢ ∃ i, x ∈ (fun i => toFun (find c ne i) i) i
      use j
      -- ⊢ x ∈ (fun i => toFun (find c ne i) i) j
      have hj' : x ∈ u j := (v i).subset _ hj
      -- ⊢ x ∈ (fun i => toFun (find c ne i) i) j
      have : v j ≤ v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (fun h => (hmax j hj' h).ge) id
      -- ⊢ x ∈ (fun i => toFun (find c ne i) i) j
      simpa only [find_apply_of_mem hc ne (hvc _ hxi) (this.1 <| hiv _ hj')]
      -- 🎉 no goals
  closure_subset hi := (find c ne _).closure_subset ((mem_find_carrier_iff _).2 hi)
  apply_eq hi := (find c ne _).apply_eq (mt (mem_find_carrier_iff _).1 hi)
#align shrinking_lemma.partial_refinement.chain_Sup ShrinkingLemma.PartialRefinement.chainSup

/-- `chainSup hu c hc ne hfin hU` is an upper bound of the chain `c`. -/
theorem le_chainSup {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) {v} (hv : v ∈ c) :
    v ≤ chainSup c hc ne hfin hU :=
  ⟨fun _ hi => mem_biUnion hv hi, fun _ hi => (find_apply_of_mem hc _ hv hi).symm⟩
#align shrinking_lemma.partial_refinement.le_chain_Sup ShrinkingLemma.PartialRefinement.le_chainSup

/-- If `s` is a closed set, `v` is a partial refinement, and `i` is an index such that
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater than `v`. -/
theorem exists_gt (v : PartialRefinement u s) (hs : IsClosed s) (i : ι) (hi : i ∉ v.carrier) :
    ∃ v' : PartialRefinement u s, v < v' := by
  have I : (s ∩ ⋂ (j) (_ : j ≠ i), (v j)ᶜ) ⊆ v i := by
    simp only [subset_def, mem_inter_iff, mem_iInter, and_imp]
    intro x hxs H
    rcases mem_iUnion.1 (v.subset_iUnion hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s ∩ ⋂ (j) (_ : j ≠ i), (v j)ᶜ) :=
    IsClosed.inter hs (isClosed_biInter fun _ _ => isClosed_compl_iff.2 <| v.isOpen _)
  rcases normal_exists_closure_subset C (v.isOpen i) I with ⟨vi, ovi, hvi, cvi⟩
  -- ⊢ ∃ v', v < v'
  refine' ⟨⟨update v i vi, insert i v.carrier, _, _, _, _⟩, _, _⟩
  · intro j
    -- ⊢ IsOpen (update v.toFun i vi j)
    rcases eq_or_ne j i with (rfl| hne) <;> simp [*, v.isOpen]
    -- ⊢ IsOpen (update v.toFun j vi j)
                                            -- 🎉 no goals
                                            -- 🎉 no goals
  · refine' fun x hx => mem_iUnion.2 _
    -- ⊢ ∃ i_1, x ∈ update v.toFun i vi i_1
    rcases em (∃ (j : _) (_ : j ≠ i), x ∈ v j) with (⟨j, hji, hj⟩ | h)
    -- ⊢ ∃ i_1, x ∈ update v.toFun i vi i_1
    · use j
      -- ⊢ x ∈ update v.toFun i vi j
      rwa [update_noteq hji]
      -- 🎉 no goals
    · push_neg at h
      -- ⊢ ∃ i_1, x ∈ update v.toFun i vi i_1
      use i
      -- ⊢ x ∈ update v.toFun i vi i
      rw [update_same]
      -- ⊢ x ∈ vi
      exact hvi ⟨hx, mem_biInter h⟩
      -- 🎉 no goals
  · rintro j (rfl | hj)
    -- ⊢ closure (update v.toFun j vi j) ⊆ u j
    · rwa [update_same, ← v.apply_eq hi]
      -- 🎉 no goals
    · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
      -- ⊢ closure (toFun v j) ⊆ u j
      exact v.closure_subset hj
      -- 🎉 no goals
  · intro j hj
    -- ⊢ update v.toFun i vi j = u j
    rw [mem_insert_iff, not_or] at hj
    -- ⊢ update v.toFun i vi j = u j
    rw [update_noteq hj.1, v.apply_eq hj.2]
    -- 🎉 no goals
  · refine' ⟨subset_insert _ _, fun j hj => _⟩
    -- ⊢ toFun v j = toFun { toFun := update v.toFun i vi, carrier := insert i v.carr …
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm
    -- 🎉 no goals
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
    -- 🎉 no goals
#align shrinking_lemma.partial_refinement.exists_gt ShrinkingLemma.PartialRefinement.exists_gt

end PartialRefinement

end ShrinkingLemma

open ShrinkingLemma

variable {u : ι → Set X} {s : Set X}

/-- **Shrinking lemma**. A point-finite open cover of a closed subset of a normal space can be
"shrunk" to a new open cover so that the closure of each new open set is contained in the
corresponding original open set. -/
theorem exists_subset_iUnion_closure_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i := by
  haveI : Nonempty (PartialRefinement u s) := ⟨⟨u, ∅, uo, us, False.elim, fun _ => rfl⟩⟩
  -- ⊢ ∃ v, s ⊆ iUnion v ∧ (∀ (i : ι), IsOpen (v i)) ∧ ∀ (i : ι), closure (v i) ⊆ u i
  have : ∀ c : Set (PartialRefinement u s),
      IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_nonempty_partialOrder this with ⟨v, hv⟩
  -- ⊢ ∃ v, s ⊆ iUnion v ∧ (∀ (i : ι), IsOpen (v i)) ∧ ∀ (i : ι), closure (v i) ⊆ u i
  suffices : ∀ i, i ∈ v.carrier
  -- ⊢ ∃ v, s ⊆ iUnion v ∧ (∀ (i : ι), IsOpen (v i)) ∧ ∀ (i : ι), closure (v i) ⊆ u i
  exact ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i)⟩
  -- ⊢ ∀ (i : ι), i ∈ v.carrier
  contrapose! hv
  -- ⊢ ∃ a, v ≤ a ∧ a ≠ v
  rcases hv with ⟨i, hi⟩
  -- ⊢ ∃ a, v ≤ a ∧ a ≠ v
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  -- ⊢ ∃ a, v ≤ a ∧ a ≠ v
  exact ⟨v', hlt.le, hlt.ne'⟩
  -- 🎉 no goals
#align exists_subset_Union_closure_subset exists_subset_iUnion_closure_subset

/-- **Shrinking lemma**. A point-finite open cover of a closed subset of a normal space can be
"shrunk" to a new closed cover so that each new closed set is contained in the corresponding
original open set. See also `exists_subset_iUnion_closure_subset` for a stronger statement. -/
theorem exists_subset_iUnion_closed_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (iUnion_mono fun _ => subset_closure),
    fun _ => isClosed_closure, hv⟩
#align exists_subset_Union_closed_subset exists_subset_iUnion_closed_subset

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_iUnion_eq_closure_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, iUnion v = univ ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩
#align exists_Union_eq_closure_subset exists_iUnion_eq_closure_subset

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the corresponding
original open set. See also `exists_iUnion_eq_closure_subset` for a stronger statement. -/
theorem exists_iUnion_eq_closed_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, iUnion v = univ ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closed_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩
#align exists_Union_eq_closed_subset exists_iUnion_eq_closed_subset
