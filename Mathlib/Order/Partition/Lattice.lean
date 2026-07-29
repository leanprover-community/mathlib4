/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Hyeokjun Kwon
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Partition.Set

/-!
# Complete lattice structure on partitions

When `α` is a frame, `Partition α` is a complete lattice under refinement. Finite meets already
exist via `Partition.instSemilatticeInf` in `Basic`; this file adds arbitrary meets and joins.

Joins are constructed using `nonDisjointComponents`, the partition of a set of elements into
connected components under non-disjointness, obtained as `ofRel` of the `TransGen` of that step
relation.

## Main declarations

* `Partition.NonDisjointOn` / `Partition.nonDisjointComponents`
* `Partition.instCompleteLattice`
-/

@[expose] public section
variable {α : Type*}

open Set Relation

namespace Partition

variable [Order.Frame α] {P Q R : Partition α} {S : Set α} {a b c : α} {s t : Set α}
  {Ps : Set (Partition α)} {ι : Sort*} {Pι : ι → Partition α}

/-- The relation of being non-disjoint elements of `S`. -/
def NonDisjointOn (S : Set α) (a b : α) : Prop :=
  ¬Disjoint a b ∧ a ∈ S ∧ b ∈ S

instance (S : Set α) : Std.Symm (NonDisjointOn S) where
  symm _ _ h := ⟨fun hdj ↦ h.1 hdj.symm, h.2.2, h.2.1⟩

/-- Two parts are equal if they respectively contain non-disjoint elements. -/
lemma eq_of_le_not_disjoint {x r : α} (hx : x ∈ R) (hxs : b ≤ x) (hr : r ∈ R) (hrs : c ≤ r)
    (hndisj : ¬Disjoint b c) : r = x := by
  refine R.eq_of_not_disjoint hr hx ?_
  contrapose! hndisj
  exact hndisj.symm.mono hxs hrs

/-- The partition of the nontrivial elements of `S` into connected components under
non-disjointness. -/
def nonDisjointComponents (S : Set α) : Partition (Set α) :=
  ofRel (TransGen (NonDisjointOn S))

@[simp]
lemma sUnion_nonDisjointComponents : ⋃₀ (nonDisjointComponents S : Set (Set α)) = S \ {⊥} := by
  change (nonDisjointComponents S).supp = S \ {⊥}
  rw [nonDisjointComponents, supp_ofRel]
  ext a
  simp only [mem_ofPred, mem_sdiff, mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨b, hab, -⟩ := TransGen.head'_iff.mp h
    exact ⟨hab.2.1, fun ha ↦ hab.1 (by simp [ha])⟩
  · rintro ⟨haS, hane⟩
    exact TransGen.single ⟨fun h ↦ hane (disjoint_self.1 h), haS, haS⟩

/-- Every element of a non-disjointness component belongs to the original set. -/
lemma mem_of_mem_nonDisjointComponents (ht : t ∈ nonDisjointComponents S) (ha : a ∈ t) : a ∈ S :=
  ((sUnion_nonDisjointComponents (S := S)).symm ▸ mem_sUnion_of_mem ha ht).1

/-- Every element of a non-disjointness component is nontrivial. -/
lemma ne_bot_of_mem_nonDisjointComponents (ht : t ∈ nonDisjointComponents S) (ha : a ∈ t) : a ≠ ⊥ :=
  ((sUnion_nonDisjointComponents (S := S)).symm ▸ mem_sUnion_of_mem ha ht).2

/-- The supremum of a non-disjointness component lies below any partition part containing one of
its elements, provided every element of the original set lies below a partition part. -/
lemma sSup_le_of_mem_nonDisjointComponents (h : ∀ s ∈ S, ∃ p ∈ P, s ≤ p)
    (hs : s ∈ nonDisjointComponents S) (has : a ∈ s) (hbP : b ∈ P) (hab : a ≤ b) : sSup s ≤ b := by
  have : ∀ c, TransGen (NonDisjointOn S) a c → c ≤ b := by
    intro c hc
    induction hc with
    | single hstep =>
      obtain ⟨p, hpP, hcp⟩ := h _ hstep.2.2
      convert hcp
      exact eq_of_le_not_disjoint hpP hcp hbP hab fun hd ↦ hstep.1 hd.symm
    | tail _ hbc IH =>
      obtain ⟨p, hpP, hcp⟩ := h _ hbc.2.2
      convert hcp
      exact eq_of_le_not_disjoint hpP hcp hbP IH fun hd ↦ hbc.1 hd.symm
  rw [sSup_le_iff]
  intro c hc
  have hrel : (nonDisjointComponents S).Rel a c := ⟨s, hs, has, hc⟩
  simp only [nonDisjointComponents, rel_ofRel_eq] at hrel
  exact this c hrel

/-- Choosing one part from each partition and taking their infimum gives an independent family. -/
lemma sSupIndep_iInf_image_pi (Ps : Set (Partition α)) :
    _root_.sSupIndep (iInf '' (pi univ fun p : Ps ↦ (p : Partition α).parts)) := by
  rintro _ ⟨f, hf, rfl⟩
  rw [disjoint_sSup_iff]
  rintro _ ⟨⟨g, hg, rfl⟩, hne⟩
  have hfg : f ≠ g := fun h ↦ hne (h ▸ rfl)
  contrapose! hfg
  ext p
  refine (p : Partition α).eq_of_not_disjoint (hf p (mem_univ _)) (hg p (mem_univ _)) ?_
  contrapose! hfg
  exact hfg.mono (iInf_le f p) (iInf_le g p)

/-- Distinct non-disjointness components have disjoint suprema. -/
lemma eq_of_not_disjoint_sSup_mem_nonDisjointComponents (hs : s ∈ nonDisjointComponents S)
    (ht : t ∈ nonDisjointComponents S) (h : ¬Disjoint (sSup s) (sSup t)) : s = t := by
  have h1 : ∃ x ∈ s, ¬Disjoint x (sSup t) := by
    contrapose! h
    rwa [sSup_disjoint_iff]
  obtain ⟨c, hcS, hct⟩ := h1
  have h2 : ∃ y ∈ t, ¬Disjoint c y := by
    contrapose! hct
    rwa [disjoint_sSup_iff]
  obtain ⟨d, hdT, hcd⟩ := h2
  have hrel : (nonDisjointComponents S).Rel c d := by
    simpa [nonDisjointComponents, rel_ofRel_eq] using
      TransGen.single ⟨hcd, mem_of_mem_nonDisjointComponents hs hcS,
        mem_of_mem_nonDisjointComponents ht hdT⟩
  exact eq_of_mem_of_mem hs ht hcS <| (Rel.forall hrel ht).mpr hdT

/-- The join of a family of partitions: suprema of non-disjointness components of the union of
parts. -/
instance instSupSet : SupSet (Partition α) where
  sSup Ps := {
    parts := SupSet.sSup '' (nonDisjointComponents (⋃ P ∈ Ps, (P : Set α)) : Set (Set α))
    sSupIndep' := by
      refine PairwiseDisjoint.sSupIndep ?_
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hne
      exact not_not.mp fun h ↦ hne <|
        congrArg SupSet.sSup <| eq_of_not_disjoint_sSup_mem_nonDisjointComponents hs ht h
    bot_notMem' := by
      rintro ⟨s, hs, heq⟩
      have hsne : s.Nonempty := nonempty_iff_ne_empty.mpr <|
        (nonDisjointComponents (⋃ P ∈ Ps, (P : Set α))).ne_bot_of_mem hs
      exact (ne_bot_of_mem_nonDisjointComponents hs hsne.some_mem) <|
        sSup_eq_bot.mp heq hsne.some hsne.some_mem}

lemma mem_sSup_iff : a ∈ sSup Ps ↔
    ∃ s ∈ nonDisjointComponents (⋃ P ∈ Ps, (P : Set α)), SupSet.sSup s = a := by
  change a ∈ SupSet.sSup '' (nonDisjointComponents (⋃ P ∈ Ps, (P : Set α)) : Set (Set α)) ↔ _
  simp [mem_image]

/-- The constructed supremum of a family of partitions is its least upper bound. -/
lemma isLUB_sSup (Ps : Set (Partition α)) : IsLUB Ps (sSup Ps) := by
  refine ⟨fun P hP a haP ↦ ?_, fun P hP a ha ↦ ?_⟩
  · have hane : a ≠ ⊥ := P.ne_bot_of_mem haP
    have : a ∈ (⋃ Q ∈ Ps, (Q : Set α)) \ {⊥} := by
      simp only [mem_sdiff, mem_iUnion, SetLike.mem_coe, mem_singleton_iff, hane,
        not_false_eq_true, and_true]
      exact ⟨P, hP, haP⟩
    rw [← sUnion_nonDisjointComponents] at this
    obtain ⟨s, hs, haS⟩ := this
    exact ⟨SupSet.sSup s, mem_sSup_iff.mpr ⟨s, hs, rfl⟩, _root_.le_sSup haS⟩
  obtain ⟨s, hs, rfl⟩ := mem_sSup_iff.mp ha
  have hsne : s.Nonempty := nonempty_iff_ne_empty.mpr <|
    (nonDisjointComponents _).ne_bot_of_mem hs
  obtain ⟨x, hx⟩ := hsne
  obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp (mem_of_mem_nonDisjointComponents hs hx)
  obtain ⟨y, hyP, hxy⟩ := hP hQ hxQ
  refine ⟨y, hyP, sSup_le_of_mem_nonDisjointComponents (fun z hz ↦ ?_) hs hx hyP hxy⟩
  obtain ⟨R, hR, hzR⟩ := mem_iUnion₂.mp hz
  exact hP hR hzR

/-- When `α` is a frame, partitions form a complete lattice under refinement. -/
instance instCompleteLattice : CompleteLattice (Partition α) where
  __ := (inferInstance : SemilatticeInf (Partition α))
  __ := (inferInstance : OrderBot (Partition α))
  __ := (inferInstance : OrderTop (Partition α))
  sInf Ps := removeBot (iInf '' (pi univ fun p : Ps ↦ (p : Partition α).parts))
    (sSupIndep_iInf_image_pi Ps)
  isGLB_sInf Ps := by
    refine ⟨fun P hP a ha ↦ ?_, fun P hP a haP ↦ ?_⟩
    · simp only [coe_parts, mem_removeBot, mem_image, mem_pi, mem_univ, SetLike.mem_coe,
      forall_const, Subtype.forall, ne_eq] at ha
      obtain ⟨⟨f, hf, rfl⟩, hne⟩ := ha
      exact ⟨f ⟨P, hP⟩, hf P hP, iInf_le f _⟩
    · refine ⟨iInf fun (p : Ps) ↦ (hP p.property haP).choose, ?_,
        le_iInf fun (p : Ps) ↦ (hP p.property haP).choose_spec.2⟩
      refine (mem_removeBot _ _).2 ⟨?_, ?_⟩
      · refine mem_image_of_mem _ ?_
        simpa [mem_pi] using fun (p : Ps) ↦ (hP p.property haP).choose_spec.1
      · exact ne_bot_of_le_ne_bot (P.ne_bot_of_mem haP) <|
          le_iInf fun (p : Ps) ↦ (hP p.property haP).choose_spec.2
  __ := completeLatticeOfSup (Partition α) isLUB_sSup

lemma mem_sup_iff : a ∈ P ⊔ Q ↔
    ∃ s ∈ nonDisjointComponents ((P : Set α) ∪ Q), SupSet.sSup s = a := by
  change a ∈ sSup {P, Q} ↔ _
  simp only [mem_sSup_iff, biUnion_pair]

lemma mem_iSup_iff : a ∈ ⨆ i, Pι i ↔
    ∃ s ∈ nonDisjointComponents (⋃ i, (Pι i : Set α)), SupSet.sSup s = a := by
  change a ∈ sSup (range Pι) ↔ _
  simp only [mem_sSup_iff]
  refine exists_congr fun s ↦ and_congr_left' ?_
  rw [show (⋃ P ∈ range Pι, (P : Set α)) = ⋃ i, (Pι i : Set α) by
    ext x; simp [mem_iUnion, mem_range]]

@[simp]
lemma supp_sSup (Ps : Set (Partition α)) : (sSup Ps).supp = ⨆ P ∈ Ps, P.supp := by
  change SupSet.sSup (SupSet.sSup '' _) = ⨆ P ∈ Ps, P.supp
  rw [sSup_image, ← sSup_sUnion, sUnion_nonDisjointComponents, sSup_sdiff_singleton_bot,
    ← sUnion_image, sSup_sUnion, iSup_image]
  simp only [sSup_eq]

@[simp]
lemma supp_iSup (Pι : ι → Partition α) : (⨆ i, Pι i).supp = ⨆ i, (Pι i).supp := by
  change (sSup (range Pι)).supp = _
  rw [supp_sSup, iSup_range]

@[simp]
lemma supp_sup (P Q : Partition α) : (P ⊔ Q).supp = P.supp ⊔ Q.supp := by
  change (sSup {P, Q}).supp = _
  rw [supp_sSup, iSup_pair]

end Partition
