/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finite.Powerset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Vector
import Mathlib.Logic.Embedding.Set

/-!
# Finite sets

This file provides `Fintype` instances for many set constructions. It also proves basic facts
about finite sets and gives ways to manipulate `Set.Finite` expressions.

## Implementation

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

assert_not_exists OrderedRing
assert_not_exists MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

instance fintypeiUnion [DecidableEq α] [Fintype (PLift ι)] (f : ι → Set α) [∀ i, Fintype (f i)] :
    Fintype (⋃ i, f i) :=
  Fintype.ofFinset (Finset.univ.biUnion fun i : PLift ι => (f i.down).toFinset) <| by simp

instance fintypesUnion [DecidableEq α] {s : Set (Set α)} [Fintype s]
    [H : ∀ t : s, Fintype (t : Set α)] : Fintype (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Set.fintypeiUnion _ _ _ _ _ H

lemma toFinset_iUnion [Fintype β] [DecidableEq α] (f : β → Set α)
    [∀ w, Fintype (f w)] :
    Set.toFinset (⋃ (x : β), f x) =
    Finset.biUnion (Finset.univ : Finset β) (fun x => (f x).toFinset) := by
  ext v
  simp only [mem_toFinset, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]

section monad
attribute [local instance] Set.monad

/-- If `s : Set α` is a set with `Fintype` instance and `f : α → Set β` is a function such that
each `f a`, `a ∈ s`, has a `Fintype` structure, then `s >>= f` has a `Fintype` structure. -/
def fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    (H : ∀ a ∈ s, Fintype (f a)) : Fintype (s >>= f) :=
  Set.fintypeBiUnion s f H

instance fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    [∀ a, Fintype (f a)] : Fintype (s >>= f) :=
  Set.fintypeBiUnion' s f

end monad

instance fintypeRange [DecidableEq α] (f : ι → α) [Fintype (PLift ι)] : Fintype (range f) :=
  Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) <| by simp

instance fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] :
    Fintype (s ×ˢ t : Set (α × β)) :=
  Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) <| by simp

instance fintypeOffDiag [DecidableEq α] (s : Set α) [Fintype s] : Fintype s.offDiag :=
  Fintype.ofFinset s.toFinset.offDiag <| by simp

/-- `image2 f s t` is `Fintype` if `s` and `t` are. -/
instance fintypeImage2 [DecidableEq γ] (f : α → β → γ) (s : Set α) (t : Set β) [hs : Fintype s]
    [ht : Fintype t] : Fintype (image2 f s t : Set γ) := by
  rw [← image_prod]
  apply Set.fintypeImage

instance fintypeSeq [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBiUnion'

instance fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f]
    [Fintype s] : Fintype (f <*> s) :=
  Set.fintypeSeq f s

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

open scoped Classical

instance finite_range (f : ι → α) [Finite ι] : Finite (range f) := by
  haveI := Fintype.ofFinite (PLift ι)
  infer_instance

instance finite_iUnion [Finite ι] (f : ι → Set α) [∀ i, Finite (f i)] : Finite (⋃ i, f i) := by
  rw [iUnion_eq_range_psigma]
  apply Set.finite_range

instance finite_sUnion {s : Set (Set α)} [Finite s] [H : ∀ t : s, Finite (t : Set α)] :
    Finite (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Finite.Set.finite_iUnion _ _ _ _ H

theorem finite_biUnion {ι : Type*} (s : Set ι) [Finite s] (t : ι → Set α)
    (H : ∀ i ∈ s, Finite (t i)) : Finite (⋃ x ∈ s, t x) := by
  rw [biUnion_eq_iUnion]
  haveI : ∀ i : s, Finite (t i) := fun i => H i i.property
  infer_instance

instance finite_biUnion' {ι : Type*} (s : Set ι) [Finite s] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋃ x ∈ s, t x) :=
  finite_biUnion s t fun _ _ => inferInstance

/-- Example: `Finite (⋃ (i < n), f i)` where `f : ℕ → Set α` and `[∀ i, Finite (f i)]`
(when given instances from `Order.Interval.Finset.Nat`).
-/
instance finite_biUnion'' {ι : Type*} (p : ι → Prop) [h : Finite { x | p x }] (t : ι → Set α)
    [∀ i, Finite (t i)] : Finite (⋃ (x) (_ : p x), t x) :=
  @Finite.Set.finite_biUnion' _ _ (setOf p) h t _

instance finite_iInter {ι : Sort*} [Nonempty ι] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋂ i, t i) :=
  Finite.Set.subset (t <| Classical.arbitrary ι) (iInter_subset _ _)

instance finite_replacement [Finite α] (f : α → β) :
    Finite {f x | x : α} :=
  Finite.Set.finite_range f

instance finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (s ×ˢ t : Set (α × β)) :=
  Finite.of_equiv _ (Equiv.Set.prod s t).symm

instance finite_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (image2 f s t : Set γ) := by
  rw [← image_prod]
  infer_instance

instance finite_seq (f : Set (α → β)) (s : Set α) [Finite f] [Finite s] : Finite (f.seq s) := by
  rw [seq_def]
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

theorem finite_iUnion [Finite ι] {f : ι → Set α} (H : ∀ i, (f i).Finite) : (⋃ i, f i).Finite :=
  haveI := fun i => (H i).to_subtype
  toFinite _

/-- Dependent version of `Finite.biUnion`. -/
theorem Finite.biUnion' {ι} {s : Set ι} (hs : s.Finite) {t : ∀ i ∈ s, Set α}
    (ht : ∀ i (hi : i ∈ s), (t i hi).Finite) : (⋃ i ∈ s, t i ‹_›).Finite := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]
  apply finite_iUnion fun i : s => ht i.1 i.2

theorem Finite.biUnion {ι} {s : Set ι} (hs : s.Finite) {t : ι → Set α}
    (ht : ∀ i ∈ s, (t i).Finite) : (⋃ i ∈ s, t i).Finite :=
  hs.biUnion' ht

theorem Finite.sUnion {s : Set (Set α)} (hs : s.Finite) (H : ∀ t ∈ s, Set.Finite t) :
    (⋃₀ s).Finite := by
  simpa only [sUnion_eq_biUnion] using hs.biUnion H

theorem Finite.sInter {α : Type*} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Finite) :
    (⋂₀ s).Finite :=
  hf.subset (sInter_subset_of_mem ht)

/-- If sets `s i` are finite for all `i` from a finite set `t` and are empty for `i ∉ t`, then the
union `⋃ i, s i` is a finite set. -/
theorem Finite.iUnion {ι : Type*} {s : ι → Set α} {t : Set ι} (ht : t.Finite)
    (hs : ∀ i ∈ t, (s i).Finite) (he : ∀ i, i ∉ t → s i = ∅) : (⋃ i, s i).Finite := by
  suffices ⋃ i, s i ⊆ ⋃ i ∈ t, s i by exact (ht.biUnion hs).subset this
  refine iUnion_subset fun i x hx => ?_
  by_cases hi : i ∈ t
  · exact mem_biUnion hi hx
  · rw [he i hi, mem_empty_iff_false] at hx
    contradiction

section monad
attribute [local instance] Set.monad

theorem Finite.bind {α β} {s : Set α} {f : α → Set β} (h : s.Finite) (hf : ∀ a ∈ s, (f a).Finite) :
    (s >>= f).Finite :=
  h.biUnion hf

end monad

theorem finite_range (f : ι → α) [Finite ι] : (range f).Finite :=
  toFinite _

theorem Finite.dependent_image {s : Set α} (hs : s.Finite) (F : ∀ i ∈ s, β) :
    {y : β | ∃ x hx, F x hx = y}.Finite := by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2

section preimage
variable {f : α → β} {s : Set β}

theorem Finite.preimage' (h : s.Finite) (hf : ∀ b ∈ s, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).Finite := by
  rw [← Set.biUnion_preimage_singleton]
  exact Set.Finite.biUnion h hf

end preimage

section Prod

variable {s : Set α} {t : Set β}

protected theorem Finite.prod (hs : s.Finite) (ht : t.Finite) : (s ×ˢ t : Set (α × β)).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

theorem Finite.of_prod_left (h : (s ×ˢ t : Set (α × β)).Finite) : t.Nonempty → s.Finite :=
  fun ⟨b, hb⟩ => (h.image Prod.fst).subset fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem Finite.of_prod_right (h : (s ×ˢ t : Set (α × β)).Finite) : s.Nonempty → t.Finite :=
  fun ⟨a, ha⟩ => (h.image Prod.snd).subset fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩

protected theorem Infinite.prod_left (hs : s.Infinite) (ht : t.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => hs <| h.of_prod_left ht

protected theorem Infinite.prod_right (ht : t.Infinite) (hs : s.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => ht <| h.of_prod_right hs

protected theorem infinite_prod :
    (s ×ˢ t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [Set.Infinite, @and_comm ¬_, ← Classical.not_imp]
    by_contra!
    exact h ((this.1 h.nonempty.snd).prod <| this.2 h.nonempty.fst)
  · rintro (h | h)
    · exact h.1.prod_left h.2
    · exact h.1.prod_right h.2

theorem finite_prod : (s ×ˢ t).Finite ↔ (s.Finite ∨ t = ∅) ∧ (t.Finite ∨ s = ∅) := by
  simp only [← not_infinite, Set.infinite_prod, not_or, not_and_or, not_nonempty_iff_eq_empty]

protected theorem Finite.offDiag {s : Set α} (hs : s.Finite) : s.offDiag.Finite :=
  (hs.prod hs).subset s.offDiag_subset_prod

protected theorem Finite.image2 (f : α → β → γ) (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite

end Prod

theorem Finite.seq {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f.seq s).Finite :=
  hf.image2 _ hs

theorem Finite.seq' {α β : Type u} {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f <*> s).Finite :=
  hf.seq hs

/-- There are finitely many subsets of a given finite set -/
theorem Finite.finite_subsets {α : Type u} {a : Set α} (h : a.Finite) : { b | b ⊆ a }.Finite := by
  convert ((Finset.powerset h.toFinset).map Finset.coeEmb.1).finite_toSet
  ext s
  simpa [← @exists_finite_iff_finset α fun t => t ⊆ a ∧ t = s, Finite.subset_toFinset,
    ← and_assoc, Finset.coeEmb] using h.subset

protected theorem Finite.powerset {s : Set α} (h : s.Finite) : (𝒫 s).Finite :=
  h.finite_subsets

section Pi
variable {ι : Type*} [Finite ι] {κ : ι → Type*} {t : ∀ i, Set (κ i)}

/-- Finite product of finite sets is finite -/
theorem Finite.pi (ht : ∀ i, (t i).Finite) : (pi univ t).Finite := by
  cases nonempty_fintype ι
  lift t to ∀ d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet

/-- Finite product of finite sets is finite. Note this is a variant of `Set.Finite.pi` without the
extra `i ∈ univ` binder. -/
lemma Finite.pi' (ht : ∀ i, (t i).Finite) : {f : ∀ i, κ i | ∀ i, f i ∈ t i}.Finite := by
  simpa [Set.pi] using Finite.pi ht

end Pi

/-- A finite union of finsets is finite. -/
theorem union_finset_finite_of_range_finite (f : α → Finset β) (h : (range f).Finite) :
    (⋃ a, (f a : Set β)).Finite := by
  rw [← biUnion_range]
  exact h.biUnion fun y _ => y.finite_toSet

end SetFiniteConstructors

/-! ### Properties -/

theorem Finite.toFinset_prod {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    hs.toFinset ×ˢ ht.toFinset = (hs.prod ht).toFinset :=
  Finset.ext <| by simp

theorem Finite.toFinset_offDiag {s : Set α} [DecidableEq α] (hs : s.Finite) :
    hs.offDiag.toFinset = hs.toFinset.offDiag :=
  Finset.ext <| by simp

theorem Finite.fin_embedding {s : Set α} (h : s.Finite) :
    ∃ (n : ℕ) (f : Fin n ↪ α), range f = s :=
  ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by
    simp only [Finset.coe_sort_coe, Equiv.asEmbedding_range, Finite.coe_toFinset, setOf_mem_eq]⟩

theorem Finite.fin_param {s : Set α} (h : s.Finite) :
    ∃ (n : ℕ) (f : Fin n → α), Injective f ∧ range f = s :=
  let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.injective, hf⟩

theorem finite_image_fst_and_snd_iff {s : Set (α × β)} :
    (Prod.fst '' s).Finite ∧ (Prod.snd '' s).Finite ↔ s.Finite :=
  ⟨fun h => (h.1.prod h.2).subset fun _ h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
    fun h => ⟨h.image _, h.image _⟩⟩

theorem forall_finite_image_eval_iff {δ : Type*} [Finite δ] {κ : δ → Type*} {s : Set (∀ d, κ d)} :
    (∀ d, (eval d '' s).Finite) ↔ s.Finite :=
  ⟨fun h => (Finite.pi h).subset <| subset_pi_eval_image _ _, fun h _ => h.image _⟩

theorem finite_subset_iUnion {s : Set α} (hs : s.Finite) {ι} {t : ι → Set α} (h : s ⊆ ⋃ i, t i) :
    ∃ I : Set ι, I.Finite ∧ s ⊆ ⋃ i ∈ I, t i := by
  have := hs.to_subtype
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ t i by simpa [subset_def] using h
  refine ⟨range f, finite_range f, fun x hx => ?_⟩
  rw [biUnion_range, mem_iUnion]
  exact ⟨⟨x, hx⟩, hf _⟩

theorem eq_finite_iUnion_of_finite_subset_iUnion {ι} {s : ι → Set α} {t : Set α} (tfin : t.Finite)
    (h : t ⊆ ⋃ i, s i) :
    ∃ I : Set ι,
      I.Finite ∧
        ∃ σ : { i | i ∈ I } → Set α, (∀ i, (σ i).Finite) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
  let ⟨I, Ifin, hI⟩ := finite_subset_iUnion tfin h
  ⟨I, Ifin, fun x => s x ∩ t, fun _ => tfin.subset inter_subset_right, fun _ =>
    inter_subset_left, by
    ext x
    rw [mem_iUnion]
    constructor
    · intro x_in
      rcases mem_iUnion.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      exact ⟨⟨i, hi⟩, ⟨H, x_in⟩⟩
    · rintro ⟨i, -, H⟩
      exact H⟩

/-- Induction up to a finite set `S`. -/
theorem Finite.induction_to {C : Set α → Prop} {S : Set α} (h : S.Finite)
    (S0 : Set α) (hS0 : S0 ⊆ S) (H0 : C S0) (H1 : ∀ s ⊂ S, C s → ∃ a ∈ S \ s, C (insert a s)) :
    C S := by
  have : Finite S := Finite.to_subtype h
  have : Finite {T : Set α // T ⊆ S} := Finite.of_equiv (Set S) (Equiv.Set.powerset S).symm
  rw [← Subtype.coe_mk (p := (· ⊆ S)) _ le_rfl]
  rw [← Subtype.coe_mk (p := (· ⊆ S)) _ hS0] at H0
  refine Finite.to_wellFoundedGT.wf.induction_bot' (fun s hs hs' ↦ ?_) H0
  obtain ⟨a, ⟨ha1, ha2⟩, ha'⟩ := H1 s (ssubset_of_ne_of_subset hs s.2) hs'
  exact ⟨⟨insert a s.1, insert_subset ha1 s.2⟩, Set.ssubset_insert ha2, ha'⟩

/-- Induction up to `univ`. -/
theorem Finite.induction_to_univ [Finite α] {C : Set α → Prop} (S0 : Set α)
    (H0 : C S0) (H1 : ∀ S ≠ univ, C S → ∃ a ∉ S, C (insert a S)) : C univ :=
  finite_univ.induction_to S0 (subset_univ S0) H0 (by simpa [ssubset_univ_iff])

/-! ### Infinite sets -/

variable {s t : Set α}

section Image2

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}

protected theorem Infinite.image2_left (hs : s.Infinite) (hb : b ∈ t)
    (hf : InjOn (fun a => f a b) s) : (image2 f s t).Infinite :=
  (hs.image hf).mono <| image_subset_image2_left hb

protected theorem Infinite.image2_right (ht : t.Infinite) (ha : a ∈ s) (hf : InjOn (f a) t) :
    (image2 f s t).Infinite :=
  (ht.image hf).mono <| image_subset_image2_right ha

theorem infinite_image2 (hfs : ∀ b ∈ t, InjOn (fun a => f a b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => Set.infinite_prod.1 ?_, ?_⟩
  · rw [← image_uncurry_prod] at h
    exact h.of_image _
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact hs.image2_left hb (hfs _ hb)
    · exact ht.image2_right ha (hft _ ha)

lemma finite_image2 (hfs : ∀ b ∈ t, InjOn (f · b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := by
  rw [← not_infinite, infinite_image2 hfs hft]
  simp [not_or, -not_and, not_and_or, not_nonempty_iff_eq_empty]
  aesop

end Image2

theorem infinite_iUnion {ι : Type*} [Infinite ι] {s : ι → Set α} (hs : Function.Injective s) :
    (⋃ i, s i).Infinite :=
  fun hfin ↦ @not_injective_infinite_finite ι _ _ hfin.finite_subsets.to_subtype
    (fun i ↦ ⟨s i, subset_iUnion _ _⟩) fun i j h_eq ↦ hs (by simpa using h_eq)

theorem Infinite.biUnion {ι : Type*} {s : ι → Set α} {a : Set ι} (ha : a.Infinite)
    (hs : a.InjOn s) : (⋃ i ∈ a, s i).Infinite := by
  rw [biUnion_eq_iUnion]
  have _ := ha.to_subtype
  exact infinite_iUnion fun ⟨i,hi⟩ ⟨j,hj⟩ hij ↦ by simp [hs hi hj hij]

theorem Infinite.sUnion {s : Set (Set α)} (hs : s.Infinite) : (⋃₀ s).Infinite := by
  rw [sUnion_eq_iUnion]
  have _ := hs.to_subtype
  exact infinite_iUnion Subtype.coe_injective

/-! ### Order properties -/

theorem exists_min_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_min_image f ⟨x, h1.mem_toFinset.2 hx⟩

theorem exists_max_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_max_image f ⟨x, h1.mem_toFinset.2 hx⟩

theorem exists_lower_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f a ≤ f b := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ‹Nonempty α›.elim fun a => ⟨a, fun _ => False.elim⟩
  · rcases Set.exists_min_image s f h hs with ⟨x₀, _, hx₀⟩
    exact ⟨x₀, fun x hx => hx₀ x hx⟩

theorem exists_upper_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f b ≤ f a :=
  exists_lower_bound_image (β := βᵒᵈ) s f h

lemma map_finite_biSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [SupBotHomClass F α β] {s : Set ι} (hs : s.Finite) (f : F) (g : ι → α) :
    f (⨆ x ∈ s, g x) = ⨆ x ∈ s, f (g x) := by
  have := map_finset_sup f hs.toFinset g
  simp only [Finset.sup_eq_iSup, hs.mem_toFinset, comp_apply] at this
  exact this

lemma map_finite_biInf {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [InfTopHomClass F α β] {s : Set ι} (hs : s.Finite) (f : F) (g : ι → α) :
    f (⨅ x ∈ s, g x) = ⨅ x ∈ s, f (g x) := by
  have := map_finset_inf f hs.toFinset g
  simp only [Finset.inf_eq_iInf, hs.mem_toFinset, comp_apply] at this
  exact this

lemma map_finite_iSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [SupBotHomClass F α β] [Finite ι] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [← iSup_univ (f := g), ← iSup_univ (f := fun i ↦ f (g i))]
  exact map_finite_biSup finite_univ f g

lemma map_finite_iInf {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [InfTopHomClass F α β] [Finite ι] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by
  rw [← iInf_univ (f := g), ← iInf_univ (f := fun i ↦ f (g i))]
  exact map_finite_biInf finite_univ f g

theorem Finite.iSup_biInf_of_monotone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Monotone (f i)) : ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈ s, ⨆ j, f i j := by
  induction s, hs using Set.Finite.dinduction_on with
  | H0 => simp [iSup_const]
  | H1 _ _ ihs =>
    rw [forall_mem_insert] at hf
    simp only [iInf_insert, ← ihs hf.2]
    exact iSup_inf_of_monotone hf.1 fun j₁ j₂ hj => iInf₂_mono fun i hi => hf.2 i hi hj

theorem Finite.iSup_biInf_of_antitone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Antitone (f i)) : ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈ s, ⨆ j, f i j :=
  @Finite.iSup_biInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ fun i hi => (hf i hi).dual_left

theorem Finite.iInf_biSup_of_monotone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Coframe α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Monotone (f i)) : ⨅ j, ⨆ i ∈ s, f i j = ⨆ i ∈ s, ⨅ j, f i j :=
  hs.iSup_biInf_of_antitone (α := αᵒᵈ) fun i hi => (hf i hi).dual_right

theorem Finite.iInf_biSup_of_antitone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Coframe α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Antitone (f i)) : ⨅ j, ⨆ i ∈ s, f i j = ⨆ i ∈ s, ⨅ j, f i j :=
  hs.iSup_biInf_of_monotone (α := αᵒᵈ) fun i hi => (hf i hi).dual_right

theorem iSup_iInf_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Monotone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j := by
  simpa only [iInf_univ] using finite_univ.iSup_biInf_of_monotone fun i _ => hf i

theorem iSup_iInf_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Antitone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j :=
  @iSup_iInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ fun i => (hf i).dual_left

theorem iInf_iSup_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Coframe α] {f : ι → ι' → α} (hf : ∀ i, Monotone (f i)) :
    ⨅ j, ⨆ i, f i j = ⨆ i, ⨅ j, f i j :=
  iSup_iInf_of_antitone (α := αᵒᵈ) fun i => (hf i).dual_right

theorem iInf_iSup_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Coframe α] {f : ι → ι' → α} (hf : ∀ i, Antitone (f i)) :
    ⨅ j, ⨆ i, f i j = ⨆ i, ⨅ j, f i j :=
  iSup_iInf_of_monotone (α := αᵒᵈ) fun i => (hf i).dual_right

/-- An increasing union distributes over finite intersection. -/
theorem iUnion_iInter_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirected ι' (· ≤ ·)]
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_monotone hs

/-- A decreasing union distributes over finite intersection. -/
theorem iUnion_iInter_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsDirected ι' (swap (· ≤ ·))] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_antitone hs

/-- An increasing intersection distributes over finite union. -/
theorem iInter_iUnion_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsDirected ι' (swap (· ≤ ·))] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_monotone hs

/-- A decreasing intersection distributes over finite union. -/
theorem iInter_iUnion_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirected ι' (· ≤ ·)]
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_antitone hs

theorem iUnion_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] {α : ι → Type*}
    {I : Set ι} {s : ∀ i, ι' → Set (α i)} (hI : I.Finite) (hs : ∀ i ∈ I, Monotone (s i)) :
    ⋃ j : ι', I.pi (fun i => s i j) = I.pi fun i => ⋃ j, s i j := by
  simp only [pi_def, biInter_eq_iInter, preimage_iUnion]
  haveI := hI.fintype.finite
  refine iUnion_iInter_of_monotone (ι' := ι') (fun (i : I) j₁ j₂ h => ?_)
  exact preimage_mono <| hs i i.2 h

theorem iUnion_univ_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] [Finite ι]
    {α : ι → Type*} {s : ∀ i, ι' → Set (α i)} (hs : ∀ i, Monotone (s i)) :
    ⋃ j : ι', pi univ (fun i => s i j) = pi univ fun i => ⋃ j, s i j :=
  iUnion_pi_of_monotone finite_univ fun i _ => hs i

section

variable [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α] {s : Set α}

/-- A finite set is bounded above. -/
protected theorem Finite.bddAbove (hs : s.Finite) : BddAbove s :=
  Finite.induction_on hs bddAbove_empty fun _ _ h => h.insert _

/-- A finite union of sets which are all bounded above is still bounded above. -/
theorem Finite.bddAbove_biUnion {I : Set β} {S : β → Set α} (H : I.Finite) :
    BddAbove (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddAbove (S i) :=
  Finite.induction_on H (by simp only [biUnion_empty, bddAbove_empty, forall_mem_empty])
    fun _ _ hs => by simp only [biUnion_insert, forall_mem_insert, bddAbove_union, hs]

theorem infinite_of_not_bddAbove : ¬BddAbove s → s.Infinite :=
  mt Finite.bddAbove

end

section

variable [Preorder α] [IsDirected α (· ≥ ·)] [Nonempty α] {s : Set α}

/-- A finite set is bounded below. -/
protected theorem Finite.bddBelow (hs : s.Finite) : BddBelow s :=
  Finite.bddAbove (α := αᵒᵈ) hs

/-- A finite union of sets which are all bounded below is still bounded below. -/
theorem Finite.bddBelow_biUnion {I : Set β} {S : β → Set α} (H : I.Finite) :
    BddBelow (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddBelow (S i) :=
  Finite.bddAbove_biUnion (α := αᵒᵈ) H

theorem infinite_of_not_bddBelow : ¬BddBelow s → s.Infinite := mt Finite.bddBelow

end

end Set

namespace Finset

/-- A finset is bounded above. -/
protected theorem bddAbove [SemilatticeSup α] [Nonempty α] (s : Finset α) : BddAbove (↑s : Set α) :=
  s.finite_toSet.bddAbove

/-- A finset is bounded below. -/
protected theorem bddBelow [SemilatticeInf α] [Nonempty α] (s : Finset α) : BddBelow (↑s : Set α) :=
  s.finite_toSet.bddBelow

end Finset

section LinearOrder
variable [LinearOrder α] {s : Set α}

lemma Set.finite_diff_iUnion_Ioo (s : Set α) : (s \ ⋃ (x ∈ s) (y ∈ s), Ioo x y).Finite :=
  Set.finite_of_forall_not_lt_lt fun _x hx _y hy _z hz hxy hyz => hy.2 <| mem_iUnion₂_of_mem hx.1 <|
    mem_iUnion₂_of_mem hz.1 ⟨hxy, hyz⟩

lemma Set.finite_diff_iUnion_Ioo' (s : Set α) : (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite := by
  simpa only [iUnion, iSup_prod, iSup_subtype] using s.finite_diff_iUnion_Ioo

theorem DirectedOn.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι → Set α}
    {c : Set ι} (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i ⊆ f j) c) {s : Finset α}
    (hs : (s : Set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : Set α) ⊆ f i := by
  rw [Set.biUnion_eq_iUnion] at hs
  haveI := hn.coe_sort
  simpa using (directed_comp.2 hc.directed_val).exists_mem_subset_of_finset_subset_biUnion hs

end LinearOrder

namespace List
variable (α) [Finite α] (n : ℕ)

lemma finite_length_eq : {l : List α | l.length = n}.Finite := Mathlib.Vector.finite

lemma finite_length_lt : {l : List α | l.length < n}.Finite := by
  convert (Finset.range n).finite_toSet.biUnion fun i _ ↦ finite_length_eq α i; ext; simp

lemma finite_length_le : {l : List α | l.length ≤ n}.Finite := by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)

end List
