/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic

#align_import data.set.pairwise.lattice from "leanprover-community/mathlib"@"c4c2ed622f43768eff32608d4a0f8a6cec1c047d"

/-!
# Relations holding pairwise

In this file we prove many facts about `Pairwise` and the set lattice.
-/


open Function Set Order

variable {α β γ ι ι' : Type*} {κ : Sort*} {r p q : α → α → Prop}
section Pairwise

variable {f g : ι → α} {s t u : Set α} {a b : α}

namespace Set

theorem pairwise_iUnion {f : κ → Set α} (h : Directed (· ⊆ ·) f) :
    (⋃ n, f n).Pairwise r ↔ ∀ n, (f n).Pairwise r := by
  constructor
  -- ⊢ Set.Pairwise (⋃ (n : κ), f n) r → ∀ (n : κ), Set.Pairwise (f n) r
  · intro H n
    -- ⊢ Set.Pairwise (f n) r
    exact Pairwise.mono (subset_iUnion _ _) H
    -- 🎉 no goals
  · intro H i hi j hj hij
    -- ⊢ r i j
    rcases mem_iUnion.1 hi with ⟨m, hm⟩
    -- ⊢ r i j
    rcases mem_iUnion.1 hj with ⟨n, hn⟩
    -- ⊢ r i j
    rcases h m n with ⟨p, mp, np⟩
    -- ⊢ r i j
    exact H p (mp hm) (np hn) hij
    -- 🎉 no goals
#align set.pairwise_Union Set.pairwise_iUnion

theorem pairwise_sUnion {r : α → α → Prop} {s : Set (Set α)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).Pairwise r ↔ ∀ a ∈ s, Set.Pairwise a r := by
  rw [sUnion_eq_iUnion, pairwise_iUnion h.directed_val, SetCoe.forall]
  -- 🎉 no goals
#align set.pairwise_sUnion Set.pairwise_sUnion

end Set

end Pairwise

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s t : Set ι} {f g : ι → α}

theorem pairwiseDisjoint_iUnion {g : ι' → Set ι} (h : Directed (· ⊆ ·) g) :
    (⋃ n, g n).PairwiseDisjoint f ↔ ∀ ⦃n⦄, (g n).PairwiseDisjoint f :=
  pairwise_iUnion h
#align set.pairwise_disjoint_Union Set.pairwiseDisjoint_iUnion

theorem pairwiseDisjoint_sUnion {s : Set (Set ι)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).PairwiseDisjoint f ↔ ∀ ⦃a⦄, a ∈ s → Set.PairwiseDisjoint a f :=
  pairwise_sUnion h
#align set.pairwise_disjoint_sUnion Set.pairwiseDisjoint_sUnion

end PartialOrderBot

section CompleteLattice

variable [CompleteLattice α] {s : Set ι} {t : Set ι'}

/-- Bind operation for `Set.PairwiseDisjoint`. If you want to only consider finsets of indices, you
can use `Set.PairwiseDisjoint.biUnion_finset`. -/
theorem PairwiseDisjoint.biUnion {s : Set ι'} {g : ι' → Set ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => ⨆ i ∈ g i', f i)
    (hg : ∀ i ∈ s, (g i).PairwiseDisjoint f) : (⋃ i ∈ s, g i).PairwiseDisjoint f := by
  rintro a ha b hb hab
  -- ⊢ (Disjoint on f) a b
  simp_rw [Set.mem_iUnion] at ha hb
  -- ⊢ (Disjoint on f) a b
  obtain ⟨c, hc, ha⟩ := ha
  -- ⊢ (Disjoint on f) a b
  obtain ⟨d, hd, hb⟩ := hb
  -- ⊢ (Disjoint on f) a b
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  -- ⊢ (Disjoint on f) a b
  · exact hg d hd (hcd.subst ha) hb hab
    -- 🎉 no goals
  -- Porting note: the elaborator couldn't figure out `f` here.
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono
      (le_iSup₂ (f := fun i (_ : i ∈ g c) => f i) a ha)
      (le_iSup₂ (f := fun i (_ : i ∈ g d) => f i) b hb)
#align set.pairwise_disjoint.bUnion Set.PairwiseDisjoint.biUnion

/-- If the suprema of columns are pairwise disjoint and suprema of rows as well, then everything is
pairwise disjoint. Not to be confused with `Set.PairwiseDisjoint.prod`. -/
theorem PairwiseDisjoint.prod_left {f : ι × ι' → α}
    (hs : s.PairwiseDisjoint fun i => ⨆ i' ∈ t, f (i, i'))
    (ht : t.PairwiseDisjoint fun i' => ⨆ i ∈ s, f (i, i')) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f := by
  rintro ⟨i, i'⟩ hi ⟨j, j'⟩ hj h
  -- ⊢ (Disjoint on f) (i, i') (j, j')
  rw [mem_prod] at hi hj
  -- ⊢ (Disjoint on f) (i, i') (j, j')
  obtain rfl | hij := eq_or_ne i j
  -- ⊢ (Disjoint on f) (i, i') (i, j')
  · refine' (ht hi.2 hj.2 <| (Prod.mk.inj_left _).ne_iff.1 h).mono _ _
    -- ⊢ f (i, i') ≤ (fun i' => ⨆ (i : ι) (_ : i ∈ s), f (i, i')) (i, i').snd
    · convert le_iSup₂ (α := α) i hi.1; rfl
      -- ⊢ f (i, i') = f (i, (i, i').snd)
                                        -- 🎉 no goals
    · convert le_iSup₂ (α := α) i hj.1; rfl
      -- ⊢ f (i, j') = f (i, (i, j').snd)
                                        -- 🎉 no goals
  · refine' (hs hi.1 hj.1 hij).mono _ _
    -- ⊢ f (i, i') ≤ (fun i => ⨆ (i' : ι') (_ : i' ∈ t), f (i, i')) (i, i').fst
    · convert le_iSup₂ (α := α) i' hi.2; rfl
      -- ⊢ f (i, i') = f ((i, i').fst, i')
                                         -- 🎉 no goals
    · convert le_iSup₂ (α := α) j' hj.2; rfl
      -- ⊢ f (j, j') = f ((j, j').fst, j')
                                         -- 🎉 no goals
#align set.pairwise_disjoint.prod_left Set.PairwiseDisjoint.prod_left

end CompleteLattice

section Frame

variable [Frame α]

theorem pairwiseDisjoint_prod_left {s : Set ι} {t : Set ι'} {f : ι × ι' → α} :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f ↔
      (s.PairwiseDisjoint fun i => ⨆ i' ∈ t, f (i, i')) ∧
        t.PairwiseDisjoint fun i' => ⨆ i ∈ s, f (i, i') := by
  refine'
        ⟨fun h => ⟨fun i hi j hj hij => _, fun i hi j hj hij => _⟩, fun h => h.1.prod_left h.2⟩ <;>
      simp_rw [Function.onFun, iSup_disjoint_iff, disjoint_iSup_iff] <;>
      -- ⊢ ∀ (i_1 : ι'), i_1 ∈ t → ∀ (i_3 : ι'), i_3 ∈ t → Disjoint (f (i, i_1)) (f (j, …
      -- ⊢ ∀ (i_1 : ι), i_1 ∈ s → ∀ (i_3 : ι), i_3 ∈ s → Disjoint (f (i_1, i)) (f (i_3, …
    intro i' hi' j' hj'
    -- ⊢ Disjoint (f (i, i')) (f (j, j'))
    -- ⊢ Disjoint (f (i', i)) (f (j', j))
  · exact h (mk_mem_prod hi hi') (mk_mem_prod hj hj') (ne_of_apply_ne Prod.fst hij)
    -- 🎉 no goals
  · exact h (mk_mem_prod hi' hi) (mk_mem_prod hj' hj) (ne_of_apply_ne Prod.snd hij)
    -- 🎉 no goals
#align set.pairwise_disjoint_prod_left Set.pairwiseDisjoint_prod_left

end Frame

theorem biUnion_diff_biUnion_eq {s t : Set ι} {f : ι → Set α} (h : (s ∪ t).PairwiseDisjoint f) :
    ((⋃ i ∈ s, f i) \ ⋃ i ∈ t, f i) = ⋃ i ∈ s \ t, f i := by
  refine'
    (biUnion_diff_biUnion_subset f s t).antisymm
      (iUnion₂_subset fun i hi a ha => (mem_diff _).2 ⟨mem_biUnion hi.1 ha, _⟩)
  rw [mem_iUnion₂]; rintro ⟨j, hj, haj⟩
  -- ⊢ ¬∃ i j, a ∈ f i
                    -- ⊢ False
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩
  -- 🎉 no goals
#align set.bUnion_diff_bUnion_eq Set.biUnion_diff_biUnion_eq


/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def biUnionEqSigmaOfDisjoint {s : Set ι} {f : ι → Set α} (h : s.PairwiseDisjoint f) :
    (⋃ i ∈ s, f i) ≃ Σi : s, f i :=
  (Equiv.setCongr (biUnion_eq_iUnion _ _)).trans <|
    unionEqSigmaOfDisjoint fun ⟨_i, hi⟩ ⟨_j, hj⟩ ne => h hi hj fun eq => ne <| Subtype.eq eq
#align set.bUnion_eq_sigma_of_disjoint Set.biUnionEqSigmaOfDisjoint

end Set

section

variable {f : ι → Set α} {s t : Set ι}

theorem Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀ : (s ∪ t).PairwiseDisjoint f)
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : ⋃ i ∈ s, f i ⊆ ⋃ i ∈ t, f i) : s ⊆ t := by
  rintro i hi
  -- ⊢ i ∈ t
  obtain ⟨a, hai⟩ := h₁ i hi
  -- ⊢ i ∈ t
  obtain ⟨j, hj, haj⟩ := mem_iUnion₂.1 (h <| mem_iUnion₂_of_mem hi hai)
  -- ⊢ i ∈ t
  rwa [h₀.eq (subset_union_left _ _ hi) (subset_union_right _ _ hj)
      (not_disjoint_iff.2 ⟨a, hai, haj⟩)]
#align set.pairwise_disjoint.subset_of_bUnion_subset_bUnion Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion

theorem Pairwise.subset_of_biUnion_subset_biUnion (h₀ : Pairwise (Disjoint on f))
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : ⋃ i ∈ s, f i ⊆ ⋃ i ∈ t, f i) : s ⊆ t :=
  Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀.set_pairwise _) h₁ h
#align pairwise.subset_of_bUnion_subset_bUnion Pairwise.subset_of_biUnion_subset_biUnion

theorem Pairwise.biUnion_injective (h₀ : Pairwise (Disjoint on f)) (h₁ : ∀ i, (f i).Nonempty) :
    Injective fun s : Set ι => ⋃ i ∈ s, f i := fun _s _t h =>
  ((h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) <| h.subset).antisymm <|
    (h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) <| h.superset
#align pairwise.bUnion_injective Pairwise.biUnion_injective

end
