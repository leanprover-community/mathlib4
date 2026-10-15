/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Order.CountableSupClosed
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.
* `compactClosedSquareCylinders`: The square cylinders in a product space whose sides are
  compact and closed.

## Main results

* `isCompactSystem_insert_univ_iff`: A set system is a compact system iff inserting `univ`
  gives a compact system.
* `isCompactSystem_isCompact_isClosed`: The set of closed and compact sets is a compact system.
* `isCompactSystem_isCompact`: In a `T2Space`, the set of compact sets is a compact system.
* `IsCompactSystem.supClosure`: If `S` is a compact system, then the set of finite unions of sets
  in `S` is also a compact system.
* `IsCompactSystem.countableInfClosure`: If `S` is a compact system, then the set of countable
  intersections of sets in `S` is a compact system.
* `IsCompactSystem.prod`, `IsCompactSystem.pi`: Products of sets from compact systems form a
  compact system.
* `isCompactSystem_compactClosedSquareCylinders`: Compact and closed square cylinders form a
  compact system.
* `isCompactSystem_countableInfClosure_supClosure_compactClosedSquareCylinders`: Countable
  intersections of finite unions of compact and closed square cylinders form a compact system.
* `cylinder_mem_countableInfClosure_supClosure`: In a product of second-countable R₁ spaces, a
  cylinder with a compact closed base is a countable intersection of finite unions of compact and
  closed square cylinders.
-/

@[expose] public section

open Set Nat

variable {α : Type*} {S : Set (Set α)} {C : ℕ → Set α}

section definition

/-- A set of sets is a compact system if, whenever a countable subfamily has empty intersection,
then finitely many of them already have empty intersection. -/
def IsCompactSystem (S : Set (Set α)) : Prop :=
  ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ (n : ℕ), dissipate C n = ∅

end definition

namespace IsCompactSystem

lemma of_nonempty_iInter
    (h : ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty) :
    IsCompactSystem S := by
  intro C hC
  contrapose!
  exact h C hC

lemma nonempty_iInter (hp : IsCompactSystem S) {C : ℕ → Set α} (hC : ∀ i, C i ∈ S)
    (h_nonempty : ∀ n, (dissipate C n).Nonempty) :
    (⋂ i, C i).Nonempty := by
  revert h_nonempty
  contrapose!
  exact hp C hC

theorem iff_nonempty_iInter (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (dissipate C n).Nonempty) → (⋂ i, C i).Nonempty :=
  ⟨nonempty_iInter, of_nonempty_iInter⟩

@[simp]
lemma of_IsEmpty [IsEmpty α] (S : Set (Set α)) : IsCompactSystem S :=
  fun s _ _ ↦ ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/-- Any subset of a compact system is a compact system. -/
theorem mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S ⊆ T) :
    IsCompactSystem S := fun C hC1 hC2 ↦ hT C (fun i ↦ hST (hC1 i)) hC2

/-- Inserting `∅` into a compact system gives a compact system. -/
lemma insert_empty (h : IsCompactSystem S) : IsCompactSystem (insert ∅ S) := by
  intro s h' hd
  by_cases! g : ∃ n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · exact h s (fun i ↦ (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

/-- Inserting `univ` into a compact system gives a compact system. -/
lemma insert_univ (h : IsCompactSystem S) : IsCompactSystem (insert univ S) := by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases! h₀ : ∀ n, s n ∉ S
  · simp_all
  classical
  let n := Nat.find h₀
  let s' := fun i ↦ if s i ∈ S then s i else s n
  have h₁ : ∀ i, s' i ∈ S := by grind
  have h₂ : ⋂ i, s i = ⋂ i, s' i := by ext; simp; grind
  apply h₂ ▸ h s' h₁
  by_contra! ⟨j, hj⟩
  have h₃ (v : ℕ) (hv : n ≤ v) : dissipate s v = dissipate s' v := by ext; simp; grind
  have h₇ : dissipate s' (max j n) = ∅ := by
    rw [← subset_empty_iff] at hj ⊢
    exact (antitone_dissipate (Nat.le_max_left j n)).trans hj
  specialize h₃ (max j n) (Nat.le_max_right j n)
  specialize hd (max j n)
  simp [h₃, h₇] at hd

end IsCompactSystem

/-- In this equivalent formulation for a compact system,
note that we use `⋂ k < n, C k` rather than `⋂ k ≤ n, C k`. -/
lemma isCompactSystem_iff_nonempty_iInter_of_lt (S : Set (Set α)) :
    IsCompactSystem S ↔
      ∀ C : ℕ → Set α, (∀ i, C i ∈ S) → (∀ n, (⋂ k < n, C k).Nonempty) → (⋂ i, C i).Nonempty := by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'↦ h C hi (fun n ↦ dissipate_eq_biInter_lt ▸ (h' (n + 1))),
    fun h C hi h' ↦ h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g ↦ h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le_trans (fun x ↦ by simp; grind) g

/-- A set system is a compact system iff adding `∅` gives a compact system. -/
lemma isCompactSystem_insert_empty_iff :
    IsCompactSystem (insert ∅ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_empty⟩

/-- A set system is a compact system iff adding `univ` gives a compact system. -/
lemma isCompactSystem_insert_univ_iff : IsCompactSystem (insert univ S) ↔ IsCompactSystem S :=
  ⟨fun h ↦ h.mono (subset_insert _ _), .insert_univ⟩

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
theorem isCompactSystem_iff_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
      ∀ (C : ℕ → Set α), Directed (· ⊇ ·) C → (∀ i, C i ∈ S) → ⋂ i, C i = ∅ → ∃ n, C n = ∅ := by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h ↦ fun C hdi hi ↦ ?_, fun h C h1 h2 ↦ ?_⟩
  · rw [← exists_dissipate_eq_empty_iff_of_directed hdi]
    exact h C (by simp [hi])
  rw [← biInter_le_eq_iInter] at h2
  suffices (∀ n, dissipate C n ∈ S ∨ dissipate C n = ∅) ∧ (⋂ n, dissipate C n = ∅) by
    by_cases! f : ∀ n, dissipate C n ∈ S
    · exact h (dissipate C) directed_dissipate f this.2
    · obtain ⟨n, hn⟩ := f
      exact ⟨n, by simpa [hn] using this.1 n⟩
  refine ⟨fun n ↦ ?_, h2⟩
  by_cases g : (dissipate C n).Nonempty
  · simpa [or_comm] using hpi.insert_empty.dissipate_mem h1 n g
  · exact .inr (Set.not_nonempty_iff_eq_empty.mp g)

/-- To prove that a set of sets is a compact system, it suffices to consider directed families of
sets. -/
theorem isCompactSystem_iff_nonempty_iInter_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
    ∀ (C : ℕ → Set α), (Directed (· ⊇ ·) C) → (∀ i, C i ∈ S) → (∀ n, (C n).Nonempty) →
      (⋂ i, C i).Nonempty := by
  rw [isCompactSystem_iff_of_directed hpi]
  refine ⟨fun h1 C h3 h4 ↦ ?_, fun h1 C h3 s ↦ ?_⟩ <;> contrapose!
  · exact h1 C h3 h4
  · exact h1 C h3 s

section IsCompactIsClosed

/-- The set of compact and closed sets is a compact system. -/
theorem isCompactSystem_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem {s : Set α | IsCompact s ∧ IsClosed s} := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty ↦ ?_
  rw [← iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n ↦ ?_) h_nonempty ?_
    (fun n ↦ isClosed_biInter (s := {i | i ≤ n}) (fun i _ ↦ (hC_cc i).2))
  · exact Set.antitone_dissipate (by lia)
  · simpa using (hC_cc 0).1

/-- In a `T2Space` the set of compact sets is a compact system. -/
theorem isCompactSystem_isCompact (α : Type*) [TopologicalSpace α] [T2Space α] :
    IsCompactSystem {s : Set α | IsCompact s} := by
  convert! isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

/-- The set of sets which are either compact and closed, or `univ`, is a compact system. -/
theorem isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s}) :=
  (isCompactSystem_isCompact_isClosed α).insert_univ

end IsCompactIsClosed

namespace IsCompactSystem

open Filter in
/-- If `S` is a compact system, then so is the set of finite unions of sets in `S`. -/
protected theorem supClosure (hS : IsCompactSystem S) :
    IsCompactSystem (supClosure S) := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC hne ↦ ?_
  -- write each `C i` as a finite union `⋃₀ L i` of sets in `S`
  have : ∀ i, ∃ L : Finset (Set α), ↑L ⊆ S ∧ C i = ⋃₀ ↑L := fun i ↦ by
    obtain ⟨L, hL, hLS, hCL⟩ := hC i
    exact ⟨L, hLS, by rw [← hCL, Finset.sup'_eq_sup, Finset.sup_id_set_eq_sUnion]⟩
  choose L hLS hCL using this
  -- the filter generated by the sets `C n`; it has basis `dissipate C`
  set F : Filter α := ⨅ n, 𝓟 (dissipate C n)
  have hFb : F.HasBasis (fun _ ↦ True) (dissipate C) :=
    hasBasis_iInf_principal antitone_dissipate.directed_ge
  have hFC (n : ℕ) : C n ∈ F :=
    mem_of_superset (hFb.mem_of_mem (i := n) trivial) (dissipate_subset le_rfl)
  -- if `A` is `F`-frequent, then so is `A ∩ a` for some `a ∈ L n`
  have step (n : ℕ) (A : Set α) (hA : ∃ᶠ x in F, x ∈ A) :
      ∃ a ∈ L n, ∃ᶠ x in F, x ∈ A ∩ a := by
    refine (frequently_exists_finset (L n)).1 <| (hA.and_eventually (hFC n)).mono fun x hx ↦ ?_
    obtain ⟨a, ha, hxa⟩ : x ∈ ⋃₀ ↑(L n) := hCL n ▸ hx.2
    exact ⟨a, ha, hx.1, hxa⟩
  choose! f hfL hf using step
  -- build the sequence `K n = f n (A n)`, where `A n = ⋂ k < n, K k` is the running intersection
  let A : ℕ → Set α := fun n ↦ Nat.rec univ (fun n A ↦ A ∩ f n A) n
  let K : ℕ → Set α := fun n ↦ f n (A n)
  have hA : ∀ n, ∃ᶠ x in F, x ∈ A n := fun n ↦ by
    induction n with
    | zero =>
      have : F.NeBot := hFb.neBot_iff.2 fun _ ↦ hne _
      exact (frequently_true_iff_neBot F).2 this
    | succ n ih => exact hf n (A n) ih
  have hAK n : A (n + 1) = dissipate K n := by
    induction n with
    | zero => simp [A, K]
    | succ n ih => rw [dissipate_succ, ← ih]
  refine (hS.nonempty_iInter (C := K) (fun n ↦ hLS n (hfL n (A n) (hA n))) fun n ↦ ?_).mono
    (iInter_mono fun n ↦ ?_)
  · exact hAK n ▸ (hA (n + 1)).exists
  · exact hCL n ▸ subset_sUnion_of_mem (hfL n (A n) (hA n))

/-- If `S` is a compact system, then the set of countable intersections of sets in `S` is also a
compact system. -/
protected theorem countableInfClosure (hS : IsCompactSystem S) :
    IsCompactSystem (countableInfClosure S) := by
  intro D hD hD_empty
  simp only [mem_countableInfClosure_iff_iInf, iInf_eq_iInter] at hD
  choose t ht hDt using hD
  obtain rfl : D = fun i ↦ ⋂ n, t i n := funext fun i ↦ (hDt i).symm
  obtain ⟨n, hn⟩ := hS (fun k ↦ t k.unpair.1 k.unpair.2) (fun k ↦ ht _ _)
    (by rwa [iInter_unpair])
  refine ⟨n, subset_eq_empty (fun x hx ↦ ?_) hn⟩
  simp only [mem_dissipate, mem_iInter] at hx ⊢
  exact fun k hk ↦ hx _ ((unpair_left_le k).trans hk) _

/-- Products of sets from two compact systems form a compact system. -/
protected theorem prod {β : Type*} {T : Set (Set β)}
    (hS : IsCompactSystem S) (hT : IsCompactSystem T) :
    IsCompactSystem (image2 (· ×ˢ ·) S T) := by
  intro u hu h_empty
  choose s hs t ht hst using hu
  obtain rfl : u = fun n ↦ s n ×ˢ t n := funext fun n ↦ (hst n).symm
  rw [← iInter_prod_iInter, prod_eq_empty_iff] at h_empty
  simp_rw [dissipate, ← iInter_prod_iInter, prod_eq_empty_iff]
  obtain h | h := h_empty
  · obtain ⟨n, hn⟩ := hS s hs h
    exact ⟨n, .inl hn⟩
  · obtain ⟨n, hn⟩ := hT t ht h
    exact ⟨n, .inr hn⟩

variable {ι : Type*} {α : ι → Type*}

/-- Boxes formed by compact systems form a compact system. -/
protected theorem pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCompactSystem (C i)) :
    IsCompactSystem (univ.pi '' univ.pi C) := by
  intro S hS h_empty
  choose x hx hxS using hS
  obtain rfl : S = fun n ↦ univ.pi (x n) := funext fun n ↦ (hxS n).symm
  obtain ⟨i, hi⟩ := iInter_univ_pi_eq_empty_iff.mp h_empty
  obtain ⟨n, hn⟩ := hC i (fun n ↦ x n i) (fun n ↦ hx n i (mem_univ i)) hi
  exact ⟨n, biInter_univ_pi_eq_empty_iff.mpr ⟨i, hn⟩⟩

end IsCompactSystem

section CompactClosedSquareCylinders

variable {ι : Type*} (α : ι → Type*) [∀ i, TopologicalSpace (α i)]

/-- The set of sets of the form `s.pi t`, where `s : Finset ι` and `t i` is both closed and
compact for all `i ∈ s`. -/
def compactClosedSquareCylinders : Set (Set (Π i, α i)) :=
  MeasureTheory.squareCylinders fun i ↦ {t : Set (α i) | IsCompact t ∧ IsClosed t}

/-- Compact and closed square cylinders form a compact system. -/
theorem isCompactSystem_compactClosedSquareCylinders :
    IsCompactSystem (compactClosedSquareCylinders α) := by
  refine (IsCompactSystem.pi fun i ↦ isCompactSystem_insert_univ_isCompact_isClosed (α i)).mono ?_
  rintro _ ⟨s, t, ht, rfl⟩
  classical
  exact ⟨fun i ↦ if i ∈ s then t i else univ, by grind⟩

/-- Countable intersections of finite unions of compact closed square cylinders (and of `∅`)
form a compact system. -/
theorem isCompactSystem_countableInfClosure_supClosure_compactClosedSquareCylinders :
    IsCompactSystem
      (countableInfClosure (supClosure (insert ∅ (compactClosedSquareCylinders α)))) :=
  (isCompactSystem_compactClosedSquareCylinders α).insert_empty.supClosure.countableInfClosure

variable {α}

open MeasureTheory

/-- A cylinder whose base is a product of compact closed sets is a compact closed square
cylinder. -/
lemma cylinder_univ_pi_mem_compactClosedSquareCylinders {J : Finset ι}
    {t : ∀ j : J, Set (α j)} (ht_compact : ∀ j, IsCompact (t j))
    (ht_closed : ∀ j, IsClosed (t j)) :
    cylinder J (univ.pi t) ∈ compactClosedSquareCylinders α := by
  classical
  refine ⟨J, fun i ↦ if h : i ∈ J then t ⟨i, h⟩ else ∅, fun i _ ↦ ?_, ?_⟩
  · by_cases h : i ∈ J <;> simp [h, ht_compact, ht_closed]
  · ext x
    simpa [cylinder] using forall₂_congr fun i hi ↦ by simp [hi]

/-- A cylinder with a compact closed base is a countable intersection of finite unions of compact
closed square cylinders. -/
lemma cylinder_mem_countableInfClosure_supClosure [∀ i, SecondCountableTopology (α i)]
    [∀ i, R1Space (α i)] {J : Finset ι} {K : Set (Π j : J, α j)} (hK_compact : IsCompact K)
    (hK_closed : IsClosed K) :
    cylinder J K ∈
      countableInfClosure (supClosure (insert ∅ (compactClosedSquareCylinders α))) := by
  classical
  -- `K` is contained in the box with compact closed sides `A j`
  let A : ∀ j : J, Set (α j) := fun j ↦ closure ((fun y ↦ y j) '' K)
  have hA_compact j : IsCompact (A j) := (hK_compact.image (continuous_apply j)).closure
  have hA_closed j : IsClosed (A j) := isClosed_closure
  have hKA : K ⊆ univ.pi A := fun y hy j _ ↦ subset_closure (mem_image_of_mem _ hy)
  -- the complement of `K` is a countable union of open boxes which do not meet `K`
  let 𝒰 : Set (∀ j : J, Set (α j)) := {u | (∀ j, IsOpen (u j)) ∧ Disjoint (univ.pi u) K}
  obtain ⟨T, hT𝒰, hT_count, hT⟩ := TopologicalSpace.isOpen_biUnion_countable 𝒰 (fun u ↦ univ.pi u)
    fun u hu ↦ isOpen_set_pi finite_univ fun j _ ↦ hu.1 j
  have hK_compl : Kᶜ = ⋃ u ∈ T, univ.pi u := by
    rw [hT]
    refine Subset.antisymm (fun y hy ↦ ?_)
      (iUnion₂_subset fun u hu ↦ subset_compl_iff_disjoint_right.mpr hu.2)
    obtain ⟨u, hu, hu_sub⟩ := isOpen_pi_iff'.mp hK_closed.isOpen_compl y hy
    exact mem_biUnion (x := u) ⟨fun j ↦ (hu j).1, subset_compl_iff_disjoint_right.mp hu_sub⟩
      fun j _ ↦ (hu j).2
  -- for each such box `univ.pi u`, `K` is covered by the boxes `B u j` for `j : J`, obtained by
  -- replacing the side `A j` by `A j \ u j`
  let B : (∀ j : J, Set (α j)) → J → ∀ k : J, Set (α k) :=
    fun u j k ↦ if k = j then A k \ u k else A k
  have hB_compact u (hu : u ∈ 𝒰) j k : IsCompact (B u j k) := by
    simp only [B]
    split_ifs
    exacts [(hA_compact k).diff (hu.1 k), hA_compact k]
  have hB_closed u (hu : u ∈ 𝒰) j k : IsClosed (B u j k) := by
    simp only [B]
    split_ifs
    exacts [(hA_closed k).sdiff (hu.1 k), hA_closed k]
  have hK_eq : K = univ.pi A ∩ ⋂ u : T, ⋃ j, univ.pi (B u j) := by
    refine Subset.antisymm (fun y hy ↦ ⟨hKA hy, mem_iInter.mpr fun u ↦ ?_⟩)
      fun y ⟨hyA, hy⟩ ↦ ?_
    · have hyu : y ∉ univ.pi u.1 := fun h ↦ (hT𝒰 u.2).2.notMem_of_mem_left h hy
      simp only [mem_univ_pi, not_forall] at hyu
      obtain ⟨j, hj⟩ := hyu
      refine mem_iUnion.mpr ⟨j, fun k _ ↦ ?_⟩
      simp only [B]
      split_ifs with hkj
      · subst hkj
        exact ⟨hKA hy k trivial, hj⟩
      · exact hKA hy k trivial
    · by_contra hyK
      rw [← mem_compl_iff, hK_compl, mem_iUnion₂] at hyK
      obtain ⟨u, hu, hyu⟩ := hyK
      obtain ⟨j, hj⟩ := mem_iUnion.mp (mem_iInter.mp hy ⟨u, hu⟩)
      have hj' := hj j trivial
      simp only [B, ite_true] at hj'
      exact hj'.2 (hyu j trivial)
  -- conclude by taking preimages
  have : Countable T := hT_count.to_subtype
  have h_eq : cylinder J K = ⋂ o : Option T, o.elim (cylinder J (univ.pi A))
      fun u ↦ ⋃ j, cylinder J (univ.pi (B u j)) := by
    rw [iInter_option]
    conv_lhs => rw [hK_eq]
    simp only [cylinder, preimage_inter, preimage_iInter, preimage_iUnion, Option.elim]
  rw [h_eq, ← iInf_eq_iInter]
  refine iInf_mem_countableInfClosure fun o ↦ ?_
  cases o with
  | none =>
    exact subset_supClosure (mem_insert_of_mem _
      (cylinder_univ_pi_mem_compactClosedSquareCylinders hA_compact hA_closed))
  | some u =>
    exact supClosed_supClosure.iSup_mem (subset_supClosure (mem_insert _ _)) fun j ↦
      subset_supClosure (mem_insert_of_mem _ (cylinder_univ_pi_mem_compactClosedSquareCylinders
        (hB_compact u (hT𝒰 u.2) j) (hB_closed u (hT𝒰 u.2) j)))

end CompactClosedSquareCylinders
