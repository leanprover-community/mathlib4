/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Pi.Notation
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter.Defs

/-!
# Theory of filters on sets

A *filter* on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

## Main definitions

In this file, we endow `Filter α` it with a complete lattice structure.
This structure is lifted from the lattice structure on `Set (Set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `Filter` is a monadic functor, with a push-forward operation
`Filter.map` and a pull-back operation `Filter.comap` that form a Galois connections for the
order on filters.

The examples of filters appearing in the description of the two motivating ideas are:
* `(Filter.atTop : Filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in `Mathlib/Topology/UniformSpace/Basic.lean`)
* `MeasureTheory.ae` : made of sets whose complement has zero measure with respect to `μ`
  (defined in `Mathlib/MeasureTheory/OuterMeasure/AE`)

The predicate "happening eventually" is `Filter.Eventually`, and "happening often" is
`Filter.Frequently`, whose definitions are immediate after `Filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).
## Notations

* `∀ᶠ x in f, p x` : `f.Eventually p`;
* `∃ᶠ x in f, p x` : `f.Frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `Filter.Principal s`, localized in `Filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `Filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[NeBot f]` in a number of lemmas and definitions.
-/

assert_not_exists OrderedSemiring Fintype

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

instance inhabitedMem : Inhabited { s : Set α // s ∈ f } :=
  ⟨⟨univ, f.univ_sets⟩⟩

theorem filter_eq_iff : f = g ↔ f.sets = g.sets :=
  ⟨congr_arg _, filter_eq⟩

@[simp] theorem sets_subset_sets : f.sets ⊆ g.sets ↔ g ≤ f := .rfl
@[simp] theorem sets_ssubset_sets : f.sets ⊂ g.sets ↔ g < f := .rfl

/-- An extensionality lemma that is useful for filters with good lemmas about `sᶜ ∈ f` (e.g.,
`Filter.comap`, `Filter.coprod`, `Filter.Coprod`, `Filter.cofinite`). -/
protected theorem coext (h : ∀ s, sᶜ ∈ f ↔ sᶜ ∈ g) : f = g :=
  Filter.ext <| compl_surjective.forall.2 h

instance : Trans (· ⊇ ·) ((· ∈ ·) : Set α → Filter α → Prop) (· ∈ ·) where
  trans h₁ h₂ := mem_of_superset h₂ h₁

instance : Trans Membership.mem (· ⊆ ·) (Membership.mem : Filter α → Set α → Prop) where
  trans h₁ h₂ := mem_of_superset h₁ h₂

@[simp]
theorem inter_mem_iff {s t : Set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f :=
  ⟨fun h => ⟨mem_of_superset h inter_subset_left, mem_of_superset h inter_subset_right⟩,
    and_imp.2 inter_mem⟩

theorem diff_mem {s t : Set α} (hs : s ∈ f) (ht : tᶜ ∈ f) : s \ t ∈ f :=
  inter_mem hs ht

theorem congr_sets (h : { x | x ∈ s ↔ x ∈ t } ∈ f) : s ∈ f ↔ t ∈ f :=
  ⟨fun hs => mp_mem hs (mem_of_superset h fun _ => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun _ => Iff.mpr)⟩

lemma copy_eq {S} (hmem : ∀ s, s ∈ S ↔ s ∈ f) : f.copy S hmem = f := Filter.ext hmem

/-- Weaker version of `Filter.biInter_mem` that assumes `Subsingleton β` rather than `Finite β`. -/
theorem biInter_mem' {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Subsingleton) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f := by
  apply Subsingleton.induction_on hf <;> simp

/-- Weaker version of `Filter.iInter_mem` that assumes `Subsingleton β` rather than `Finite β`. -/
theorem iInter_mem' {β : Sort v} {s : β → Set α} [Subsingleton β] :
    (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f := by
  rw [← sInter_range, sInter_eq_biInter, biInter_mem' (subsingleton_range s), forall_mem_range]

theorem exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
  ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩

theorem monotone_mem {f : Filter α} : Monotone fun s => s ∈ f := fun _ _ hst h =>
  mem_of_superset h hst

theorem exists_mem_and_iff {P : Set α → Prop} {Q : Set α → Prop} (hP : Antitone P)
    (hQ : Antitone Q) : ((∃ u ∈ f, P u) ∧ ∃ u ∈ f, Q u) ↔ ∃ u ∈ f, P u ∧ Q u := by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u ∩ v, inter_mem huf hvf, hP inter_subset_left hPu, hQ inter_subset_right hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩

theorem forall_in_swap {β : Type*} {p : Set α → β → Prop} :
    (∀ a ∈ f, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ f, p a b :=
  Set.forall_in_swap

end Filter


namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

theorem mem_principal_self (s : Set α) : s ∈ 𝓟 s := Subset.rfl

section Lattice

variable {f g : Filter α} {s t : Set α}

protected theorem not_le : ¬f ≤ g ↔ ∃ s ∈ g, s ∉ f := by simp_rw [le_def, not_forall, exists_prop]

/-- `GenerateSets g s`: `s` is in the filter closure of `g`. -/
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)

/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter

lemma mem_generate_of_mem {s : Set <| Set α} {U : Set α} (h : U ∈ s) :
    U ∈ generate s := GenerateSets.basic h

theorem le_generate_iff {s : Set (Set α)} {f : Filter α} : f ≤ generate s ↔ s ⊆ f.sets :=
  Iff.intro (fun h _ hu => h <| GenerateSets.basic <| hu) fun h _ hu =>
    hu.recOn (fun h' => h h') univ_mem (fun _ hxy hx => mem_of_superset hx hxy) fun _ _ hx hy =>
      inter_mem hx hy

@[simp] lemma generate_singleton (s : Set α) : generate {s} = 𝓟 s :=
  le_antisymm (fun _t ht ↦ mem_of_superset (mem_generate_of_mem <| mem_singleton _) ht) <|
    le_generate_iff.2 <| singleton_subset_iff.2 Subset.rfl

/-- `mkOfClosure s hs` constructs a filter on `α` whose elements set is exactly
`s : Set (Set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
protected def mkOfClosure (s : Set (Set α)) (hs : (generate s).sets = s) : Filter α where
  sets := s
  univ_sets := hs ▸ univ_mem
  sets_of_superset := hs ▸ mem_of_superset
  inter_sets := hs ▸ inter_mem

theorem mkOfClosure_sets {s : Set (Set α)} {hs : (generate s).sets = s} :
    Filter.mkOfClosure s hs = generate s :=
  Filter.ext fun u =>
    show u ∈ (Filter.mkOfClosure s hs).sets ↔ u ∈ (generate s).sets from hs.symm ▸ Iff.rfl

/-- Galois insertion from sets of sets into filters. -/
def giGenerate (α : Type*) :
    @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ Filter.generate Filter.sets where
  gc _ _ := le_generate_iff
  le_l_u _ _ h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

theorem mem_inf_iff {f g : Filter α} {s : Set α} : s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ :=
  Iff.rfl

theorem mem_inf_of_left {f g : Filter α} {s : Set α} (h : s ∈ f) : s ∈ f ⊓ g :=
  ⟨s, h, univ, univ_mem, (inter_univ s).symm⟩

theorem mem_inf_of_right {f g : Filter α} {s : Set α} (h : s ∈ g) : s ∈ f ⊓ g :=
  ⟨univ, univ_mem, s, h, (univ_inter s).symm⟩

theorem inter_mem_inf {α : Type u} {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) :
    s ∩ t ∈ f ⊓ g :=
  ⟨s, hs, t, ht, rfl⟩

theorem mem_inf_of_inter {f g : Filter α} {s t u : Set α} (hs : s ∈ f) (ht : t ∈ g)
    (h : s ∩ t ⊆ u) : u ∈ f ⊓ g :=
  mem_of_superset (inter_mem_inf hs ht) h

theorem mem_inf_iff_superset {f g : Filter α} {s : Set α} :
    s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ∩ t₂ ⊆ s :=
  ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ Subset.rfl⟩, fun ⟨_, h₁, _, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩

section CompleteLattice

/-- Complete lattice structure on `Filter α`. -/
instance instCompleteLatticeFilter : CompleteLattice (Filter α) where
  inf a b := min a b
  sup a b := max a b
  le_sup_left _ _ _ h := h.1
  le_sup_right _ _ _ h := h.2
  sup_le _ _ _ h₁ h₂ _ h := ⟨h₁ h, h₂ h⟩
  inf_le_left _ _ _ := mem_inf_of_left
  inf_le_right _ _ _ := mem_inf_of_right
  le_inf := fun _ _ _ h₁ h₂ _s ⟨_a, ha, _b, hb, hs⟩ => hs.symm ▸ inter_mem (h₁ ha) (h₂ hb)
  le_sSup _ _ h₁ _ h₂ := h₂ h₁
  sSup_le _ _ h₁ _ h₂ _ h₃ := h₁ _ h₃ h₂
  sInf_le _ _ h₁ _ h₂ := by rw [← Filter.sSup_lowerBounds]; exact fun _ h₃ ↦ h₃ h₁ h₂
  le_sInf _ _ h₁ _ h₂ := by rw [← Filter.sSup_lowerBounds] at h₂; exact h₂ h₁
  le_top _ _ := univ_mem'
  bot_le _ _ _ := trivial

instance : Inhabited (Filter α) := ⟨⊥⟩

end CompleteLattice

theorem NeBot.ne {f : Filter α} (hf : NeBot f) : f ≠ ⊥ := hf.ne'

@[simp] theorem not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥ := neBot_iff.not_left

theorem NeBot.mono {f g : Filter α} (hf : NeBot f) (hg : f ≤ g) : NeBot g :=
  ⟨ne_bot_of_le_ne_bot hf.1 hg⟩

theorem neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f ≤ g) : NeBot g :=
  hf.mono hg

@[simp] theorem sup_neBot {f g : Filter α} : NeBot (f ⊔ g) ↔ NeBot f ∨ NeBot g := by
  simp only [neBot_iff, not_and_or, Ne, sup_eq_bot_iff]

theorem not_disjoint_self_iff : ¬Disjoint f f ↔ f.NeBot := by rw [disjoint_self, neBot_iff]

theorem bot_sets_eq : (⊥ : Filter α).sets = univ := rfl

/-- Either `f = ⊥` or `Filter.NeBot f`. This is a version of `eq_or_ne` that uses `Filter.NeBot`
as the second alternative, to be used as an instance. -/
theorem eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f := (eq_or_ne f ⊥).imp_right NeBot.mk

theorem sup_sets_eq {f g : Filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
  (giGenerate α).gc.u_inf

theorem sSup_sets_eq {s : Set (Filter α)} : (sSup s).sets = ⋂ f ∈ s, (f : Filter α).sets :=
  (giGenerate α).gc.u_sInf

theorem iSup_sets_eq {f : ι → Filter α} : (iSup f).sets = ⋂ i, (f i).sets :=
  (giGenerate α).gc.u_iInf

theorem generate_empty : Filter.generate ∅ = (⊤ : Filter α) :=
  (giGenerate α).gc.l_bot

theorem generate_univ : Filter.generate univ = (⊥ : Filter α) :=
  bot_unique fun _ _ => GenerateSets.basic (mem_univ _)

theorem generate_union {s t : Set (Set α)} :
    Filter.generate (s ∪ t) = Filter.generate s ⊓ Filter.generate t :=
  (giGenerate α).gc.l_sup

theorem generate_iUnion {s : ι → Set (Set α)} :
    Filter.generate (⋃ i, s i) = ⨅ i, Filter.generate (s i) :=
  (giGenerate α).gc.l_iSup

@[simp]
theorem mem_sup {f g : Filter α} {s : Set α} : s ∈ f ⊔ g ↔ s ∈ f ∧ s ∈ g :=
  Iff.rfl

theorem union_mem_sup {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∪ t ∈ f ⊔ g :=
  ⟨mem_of_superset hs subset_union_left, mem_of_superset ht subset_union_right⟩

@[simp]
theorem mem_iSup {x : Set α} {f : ι → Filter α} : x ∈ iSup f ↔ ∀ i, x ∈ f i := by
  simp only [← Filter.mem_sets, iSup_sets_eq, mem_iInter]

@[simp]
theorem iSup_neBot {f : ι → Filter α} : (⨆ i, f i).NeBot ↔ ∃ i, (f i).NeBot := by
  simp [neBot_iff]

theorem iInf_eq_generate (s : ι → Filter α) : iInf s = generate (⋃ i, (s i).sets) :=
  eq_of_forall_le_iff fun _ ↦ by simp [le_generate_iff]

theorem mem_iInf_of_mem {f : ι → Filter α} (i : ι) {s} (hs : s ∈ f i) : s ∈ ⨅ i, f i :=
  iInf_le f i hs

@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩

theorem Iic_principal (s : Set α) : Iic (𝓟 s) = { l | s ∈ l } :=
  Set.ext fun _ => le_principal_iff

theorem principal_mono {s t : Set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  simp only [le_principal_iff, mem_principal]

@[gcongr] alias ⟨_, _root_.GCongr.filter_principal_mono⟩ := principal_mono

@[mono]
theorem monotone_principal : Monotone (𝓟 : Set α → Filter α) := fun _ _ => principal_mono.2

@[simp] theorem principal_eq_iff_eq {s t : Set α} : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal]; rfl

@[simp] theorem join_principal_eq_sSup {s : Set (Filter α)} : join (𝓟 s) = sSup s := rfl

@[simp] theorem principal_univ : 𝓟 (univ : Set α) = ⊤ :=
  top_unique <| by simp only [le_principal_iff, mem_top, eq_self_iff_true]

@[simp]
theorem principal_empty : 𝓟 (∅ : Set α) = ⊥ :=
  bot_unique fun _ _ => empty_subset _

theorem generate_eq_biInf (S : Set (Set α)) : generate S = ⨅ s ∈ S, 𝓟 s :=
  eq_of_forall_le_iff fun f => by simp [le_generate_iff, le_principal_iff, subset_def]

/-! ### Lattice equations -/

theorem empty_mem_iff_bot {f : Filter α} : ∅ ∈ f ↔ f = ⊥ :=
  ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩

theorem nonempty_of_mem {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id

theorem NeBot.nonempty_of_mem {f : Filter α} (hf : NeBot f) {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  @Filter.nonempty_of_mem α f hf s hs

@[simp]
theorem empty_not_mem (f : Filter α) [NeBot f] : ¬∅ ∈ f := fun h => (nonempty_of_mem h).ne_empty rfl

theorem nonempty_of_neBot (f : Filter α) [NeBot f] : Nonempty α :=
  nonempty_of_exists <| nonempty_of_mem (univ_mem : univ ∈ f)

theorem compl_not_mem {f : Filter α} {s : Set α} [NeBot f] (h : s ∈ f) : sᶜ ∉ f := fun hsc =>
  (nonempty_of_mem (inter_mem h hsc)).ne_empty <| inter_compl_self s

theorem filter_eq_bot_of_isEmpty [IsEmpty α] (f : Filter α) : f = ⊥ :=
  empty_mem_iff_bot.mp <| univ_mem' isEmptyElim

protected lemma disjoint_iff {f g : Filter α} : Disjoint f g ↔ ∃ s ∈ f, ∃ t ∈ g, Disjoint s t := by
  simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff, inf_eq_inter, bot_eq_empty,
    @eq_comm _ ∅]

theorem disjoint_of_disjoint_of_mem {f g : Filter α} {s t : Set α} (h : Disjoint s t) (hs : s ∈ f)
    (ht : t ∈ g) : Disjoint f g :=
  Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩

theorem NeBot.not_disjoint (hf : f.NeBot) (hs : s ∈ f) (ht : t ∈ f) : ¬Disjoint s t := fun h =>
  not_disjoint_self_iff.2 hf <| Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩

theorem inf_eq_bot_iff {f g : Filter α} : f ⊓ g = ⊥ ↔ ∃ U ∈ f, ∃ V ∈ g, U ∩ V = ∅ := by
  simp only [← disjoint_iff, Filter.disjoint_iff, Set.disjoint_iff_inter_eq_empty]

/-- There is exactly one filter on an empty type. -/
instance unique [IsEmpty α] : Unique (Filter α) where
  default := ⊥
  uniq := filter_eq_bot_of_isEmpty

theorem NeBot.nonempty (f : Filter α) [hf : f.NeBot] : Nonempty α :=
  not_isEmpty_iff.mp fun _ ↦ hf.ne (Subsingleton.elim _ _)

/-- There are only two filters on a `Subsingleton`: `⊥` and `⊤`. If the type is empty, then they are
equal. -/
theorem eq_top_of_neBot [Subsingleton α] (l : Filter α) [NeBot l] : l = ⊤ := by
  refine top_unique fun s hs => ?_
  obtain rfl : s = univ := Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem

theorem forall_mem_nonempty_iff_neBot {f : Filter α} :
    (∀ s : Set α, s ∈ f → s.Nonempty) ↔ NeBot f :=
  ⟨fun h => ⟨fun hf => not_nonempty_empty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩

instance instNontrivialFilter [Nonempty α] : Nontrivial (Filter α) :=
  ⟨⟨⊤, ⊥, NeBot.ne <| forall_mem_nonempty_iff_neBot.1
    fun s hs => by rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]⟩⟩

theorem nontrivial_iff_nonempty : Nontrivial (Filter α) ↔ Nonempty α :=
  ⟨fun _ =>
    by_contra fun h' =>
      haveI := not_nonempty_iff.1 h'
      not_subsingleton (Filter α) inferInstance,
    @Filter.instNontrivialFilter α⟩

theorem eq_sInf_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = sInf S :=
  le_antisymm (le_sInf fun f hf _ hs => h.2 ⟨f, hf, hs⟩)
    fun _ hs => let ⟨_, hf, hs⟩ := h.1 hs; (sInf_le hf) hs

theorem eq_iInf_of_mem_iff_exists_mem {f : ι → Filter α} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) : l = iInf f :=
  eq_sInf_of_mem_iff_exists_mem <| h.trans (exists_range_iff (p := (_ ∈ ·))).symm

theorem eq_biInf_of_mem_iff_exists_mem {f : ι → Filter α} {p : ι → Prop} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, p i ∧ s ∈ f i) : l = ⨅ (i) (_ : p i), f i := by
  rw [iInf_subtype']
  exact eq_iInf_of_mem_iff_exists_mem fun {_} => by simp only [Subtype.exists, h, exists_prop]

theorem iInf_sets_eq {f : ι → Filter α} (h : Directed (· ≥ ·) f) [ne : Nonempty ι] :
    (iInf f).sets = ⋃ i, (f i).sets :=
  let ⟨i⟩ := ne
  let u :=
    { sets := ⋃ i, (f i).sets
      univ_sets := mem_iUnion.2 ⟨i, univ_mem⟩
      sets_of_superset := by
        simp only [mem_iUnion, exists_imp]
        exact fun i hx hxy => ⟨i, mem_of_superset hx hxy⟩
      inter_sets := by
        simp only [mem_iUnion, exists_imp]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exact ⟨c, inter_mem (ha hx) (hb hy)⟩ }
  have : u = iInf f := eq_iInf_of_mem_iff_exists_mem mem_iUnion
  -- Porting note: it was just `congr_arg filter.sets this.symm`
  (congr_arg Filter.sets this.symm).trans <| by simp only [u]

theorem mem_iInf_of_directed {f : ι → Filter α} (h : Directed (· ≥ ·) f) [Nonempty ι] (s) :
    s ∈ iInf f ↔ ∃ i, s ∈ f i := by
  simp only [← Filter.mem_sets, iInf_sets_eq h, mem_iUnion]

theorem mem_biInf_of_directed {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) {t : Set α} : (t ∈ ⨅ i ∈ s, f i) ↔ ∃ i ∈ s, t ∈ f i := by
  haveI := ne.to_subtype
  simp_rw [iInf_subtype', mem_iInf_of_directed h.directed_val, Subtype.exists, exists_prop]

theorem biInf_sets_eq {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) : (⨅ i ∈ s, f i).sets = ⋃ i ∈ s, (f i).sets :=
  ext fun t => by simp [mem_biInf_of_directed h ne]

@[simp]
theorem sup_join {f₁ f₂ : Filter (Filter α)} : join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂) :=
  Filter.ext fun x => by simp only [mem_sup, mem_join]

@[simp]
theorem iSup_join {ι : Sort w} {f : ι → Filter (Filter α)} : ⨆ x, join (f x) = join (⨆ x, f x) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_join]

instance : DistribLattice (Filter α) :=
  { Filter.instCompleteLatticeFilter with
    le_sup_inf := by
      intro x y z s
      simp only [and_assoc, mem_inf_iff, mem_sup, exists_prop, exists_imp, and_imp]
      rintro hs t₁ ht₁ t₂ ht₂ rfl
      exact
        ⟨t₁, x.sets_of_superset hs inter_subset_left, ht₁, t₂,
          x.sets_of_superset hs inter_subset_right, ht₂, rfl⟩ }

/-- If `f : ι → Filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `iInf f ≠ ⊥`.
See also `iInf_neBot_of_directed` for a version assuming `Nonempty α` instead of `Nonempty ι`. -/
theorem iInf_neBot_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    (∀ i, NeBot (f i)) → NeBot (iInf f) :=
  not_imp_not.1 <| by simpa only [not_forall, not_neBot, ← empty_mem_iff_bot,
    mem_iInf_of_directed hd] using id

/-- If `f : ι → Filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `iInf f ≠ ⊥`.
See also `iInf_neBot_of_directed'` for a version assuming `Nonempty ι` instead of `Nonempty α`. -/
theorem iInf_neBot_of_directed {f : ι → Filter α} [hn : Nonempty α] (hd : Directed (· ≥ ·) f)
    (hb : ∀ i, NeBot (f i)) : NeBot (iInf f) := by
  cases isEmpty_or_nonempty ι
  · constructor
    simp [iInf_of_empty f, top_ne_bot]
  · exact iInf_neBot_of_directed' hd hb

theorem sInf_neBot_of_directed' {s : Set (Filter α)} (hne : s.Nonempty) (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    @iInf_neBot_of_directed' _ _ _ hne.to_subtype hd.directed_val fun ⟨_, hf⟩ =>
      ⟨ne_of_mem_of_not_mem hf hbot⟩

theorem sInf_neBot_of_directed [Nonempty α] {s : Set (Filter α)} (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    iInf_neBot_of_directed hd.directed_val fun ⟨_, hf⟩ => ⟨ne_of_mem_of_not_mem hf hbot⟩

theorem iInf_neBot_iff_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    NeBot (iInf f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed' hd⟩

theorem iInf_neBot_iff_of_directed {f : ι → Filter α} [Nonempty α] (hd : Directed (· ≥ ·) f) :
    NeBot (iInf f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed hd⟩

/-! #### `principal` equations -/

@[simp]
theorem inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) :=
  le_antisymm
    (by simp only [le_principal_iff, mem_inf_iff]; exact ⟨s, Subset.rfl, t, Subset.rfl, rfl⟩)
    (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp]
theorem sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) :=
  Filter.ext fun u => by simp only [union_subset_iff, mem_sup, mem_principal]

@[simp]
theorem iSup_principal {ι : Sort w} {s : ι → Set α} : ⨆ x, 𝓟 (s x) = 𝓟 (⋃ i, s i) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_principal, iUnion_subset_iff]

@[simp]
theorem principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ ↔ s = ∅ :=
  empty_mem_iff_bot.symm.trans <| mem_principal.trans subset_empty_iff

@[simp]
theorem principal_neBot_iff {s : Set α} : NeBot (𝓟 s) ↔ s.Nonempty :=
  neBot_iff.trans <| (not_congr principal_eq_bot_iff).trans nonempty_iff_ne_empty.symm

alias ⟨_, _root_.Set.Nonempty.principal_neBot⟩ := principal_neBot_iff

theorem isCompl_principal (s : Set α) : IsCompl (𝓟 s) (𝓟 sᶜ) :=
  IsCompl.of_eq (by rw [inf_principal, inter_compl_self, principal_empty]) <| by
    rw [sup_principal, union_compl_self, principal_univ]

theorem mem_inf_principal' {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ tᶜ ∪ s ∈ f := by
  simp only [← le_principal_iff, (isCompl_principal s).le_left_iff, disjoint_assoc, inf_principal,
    ← (isCompl_principal (t ∩ sᶜ)).le_right_iff, compl_inter, compl_compl]

lemma mem_inf_principal {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ { x | x ∈ t → x ∈ s } ∈ f := by
  simp only [mem_inf_principal', imp_iff_not_or, setOf_or, compl_def, setOf_mem_eq]

lemma iSup_inf_principal (f : ι → Filter α) (s : Set α) : ⨆ i, f i ⊓ 𝓟 s = (⨆ i, f i) ⊓ 𝓟 s := by
  ext
  simp only [mem_iSup, mem_inf_principal]

theorem inf_principal_eq_bot {f : Filter α} {s : Set α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ ∈ f := by
  rw [← empty_mem_iff_bot, mem_inf_principal]
  simp only [mem_empty_iff_false, imp_false, compl_def]

theorem mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 𝓟 sᶜ = ⊥) : s ∈ f := by
  rwa [inf_principal_eq_bot, compl_compl] at h

theorem diff_mem_inf_principal_compl {f : Filter α} {s : Set α} (hs : s ∈ f) (t : Set α) :
    s \ t ∈ f ⊓ 𝓟 tᶜ :=
  inter_mem_inf hs <| mem_principal_self tᶜ

theorem principal_le_iff {s : Set α} {f : Filter α} : 𝓟 s ≤ f ↔ ∀ V ∈ f, s ⊆ V := by
  simp_rw [le_def, mem_principal]

end Lattice

@[mono, gcongr]
theorem join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ ≤ f₂) : join f₁ ≤ join f₂ := fun _ hs => h hs

/-! ### Eventually -/

theorem eventually_iff {f : Filter α} {P : α → Prop} : (∀ᶠ x in f, P x) ↔ { x | P x } ∈ f :=
  Iff.rfl

@[simp]
theorem eventually_mem_set {s : Set α} {l : Filter α} : (∀ᶠ x in l, x ∈ s) ↔ s ∈ l :=
  Iff.rfl

protected theorem ext' {f₁ f₂ : Filter α}
    (h : ∀ p : α → Prop, (∀ᶠ x in f₁, p x) ↔ ∀ᶠ x in f₂, p x) : f₁ = f₂ :=
  Filter.ext h

theorem Eventually.filter_mono {f₁ f₂ : Filter α} (h : f₁ ≤ f₂) {p : α → Prop}
    (hp : ∀ᶠ x in f₂, p x) : ∀ᶠ x in f₁, p x :=
  h hp

theorem eventually_of_mem {f : Filter α} {P : α → Prop} {U : Set α} (hU : U ∈ f)
    (h : ∀ x ∈ U, P x) : ∀ᶠ x in f, P x :=
  mem_of_superset hU h

protected theorem Eventually.and {p q : α → Prop} {f : Filter α} :
    f.Eventually p → f.Eventually q → ∀ᶠ x in f, p x ∧ q x :=
  inter_mem

@[simp] theorem eventually_true (f : Filter α) : ∀ᶠ _ in f, True := univ_mem

theorem Eventually.of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp

@[simp]
theorem eventually_false_iff_eq_bot {f : Filter α} : (∀ᶠ _ in f, False) ↔ f = ⊥ :=
  empty_mem_iff_bot

@[simp]
theorem eventually_const {f : Filter α} [t : NeBot f] {p : Prop} : (∀ᶠ _ in f, p) ↔ p := by
  by_cases h : p <;> simp [h, t.ne]

theorem eventually_iff_exists_mem {p : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x) ↔ ∃ v ∈ f, ∀ y ∈ v, p y :=
  exists_mem_subset_iff.symm

theorem Eventually.exists_mem {p : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) :
    ∃ v ∈ f, ∀ y ∈ v, p y :=
  eventually_iff_exists_mem.1 hp

theorem Eventually.mp {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, p x → q x) : ∀ᶠ x in f, q x :=
  mp_mem hp hq

theorem Eventually.mono {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ x, p x → q x) : ∀ᶠ x in f, q x :=
  hp.mp (Eventually.of_forall hq)

theorem forall_eventually_of_eventually_forall {f : Filter α} {p : α → β → Prop}
    (h : ∀ᶠ x in f, ∀ y, p x y) : ∀ y, ∀ᶠ x in f, p x y :=
  fun y => h.mono fun _ h => h y

@[simp]
theorem eventually_and {p q : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in f, q x :=
  inter_mem_iff

theorem Eventually.congr {f : Filter α} {p q : α → Prop} (h' : ∀ᶠ x in f, p x)
    (h : ∀ᶠ x in f, p x ↔ q x) : ∀ᶠ x in f, q x :=
  h'.mp (h.mono fun _ hx => hx.mp)

theorem eventually_congr {f : Filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
    (∀ᶠ x in f, p x) ↔ ∀ᶠ x in f, q x :=
  ⟨fun hp => hp.congr h, fun hq => hq.congr <| by simpa only [Iff.comm] using h⟩

@[simp]
theorem eventually_or_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p ∨ q x) ↔ p ∨ ∀ᶠ x in f, q x :=
  by_cases (fun h : p => by simp [h]) fun h => by simp [h]

@[simp]
theorem eventually_or_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x ∨ q) ↔ (∀ᶠ x in f, p x) ∨ q := by
  simp only [@or_comm _ q, eventually_or_distrib_left]

theorem eventually_imp_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p → q x) ↔ p → ∀ᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or_distrib_left]

@[simp]
theorem eventually_bot {p : α → Prop} : ∀ᶠ x in ⊥, p x :=
  ⟨⟩

@[simp]
theorem eventually_top {p : α → Prop} : (∀ᶠ x in ⊤, p x) ↔ ∀ x, p x :=
  Iff.rfl

@[simp]
theorem eventually_sup {p : α → Prop} {f g : Filter α} :
    (∀ᶠ x in f ⊔ g, p x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in g, p x :=
  Iff.rfl

@[simp]
theorem eventually_sSup {p : α → Prop} {fs : Set (Filter α)} :
    (∀ᶠ x in sSup fs, p x) ↔ ∀ f ∈ fs, ∀ᶠ x in f, p x :=
  Iff.rfl

@[simp]
theorem eventually_iSup {p : α → Prop} {fs : ι → Filter α} :
    (∀ᶠ x in ⨆ b, fs b, p x) ↔ ∀ b, ∀ᶠ x in fs b, p x :=
  mem_iSup

@[simp]
theorem eventually_principal {a : Set α} {p : α → Prop} : (∀ᶠ x in 𝓟 a, p x) ↔ ∀ x ∈ a, p x :=
  Iff.rfl

theorem Eventually.forall_mem {α : Type*} {f : Filter α} {s : Set α} {P : α → Prop}
    (hP : ∀ᶠ x in f, P x) (hf : 𝓟 s ≤ f) : ∀ x ∈ s, P x :=
  Filter.eventually_principal.mp (hP.filter_mono hf)

theorem eventually_inf {f g : Filter α} {p : α → Prop} :
    (∀ᶠ x in f ⊓ g, p x) ↔ ∃ s ∈ f, ∃ t ∈ g, ∀ x ∈ s ∩ t, p x :=
  mem_inf_iff_superset

theorem eventually_inf_principal {f : Filter α} {p : α → Prop} {s : Set α} :
    (∀ᶠ x in f ⊓ 𝓟 s, p x) ↔ ∀ᶠ x in f, x ∈ s → p x :=
  mem_inf_principal

theorem eventually_iff_all_subsets {f : Filter α} {p : α → Prop} :
    (∀ᶠ x in f, p x) ↔ ∀ (s : Set α), ∀ᶠ x in f, x ∈ s → p x where
  mp h _ := by filter_upwards [h] with _ pa _ using pa
  mpr h := by filter_upwards [h univ] with _ pa using pa (by simp)

/-! ### Frequently -/

theorem Eventually.frequently {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ᶠ x in f, p x) :
    ∃ᶠ x in f, p x :=
  compl_not_mem h

theorem Frequently.of_forall {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ x, p x) :
    ∃ᶠ x in f, p x :=
  Eventually.frequently (Eventually.of_forall h)

theorem Frequently.mp {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ᶠ x in f, p x → q x) : ∃ᶠ x in f, q x :=
  mt (fun hq => hq.mp <| hpq.mono fun _ => mt) h

lemma frequently_congr {p q : α → Prop} {f : Filter α} (h : ∀ᶠ x in f, p x ↔ q x) :
    (∃ᶠ x in f, p x) ↔ ∃ᶠ x in f, q x :=
  ⟨fun h' ↦ h'.mp (h.mono fun _ ↦ Iff.mp), fun h' ↦ h'.mp (h.mono fun _ ↦ Iff.mpr)⟩

theorem Frequently.filter_mono {p : α → Prop} {f g : Filter α} (h : ∃ᶠ x in f, p x) (hle : f ≤ g) :
    ∃ᶠ x in g, p x :=
  mt (fun h' => h'.filter_mono hle) h

theorem Frequently.mono {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ x, p x → q x) : ∃ᶠ x in f, q x :=
  h.mp (Eventually.of_forall hpq)

theorem Frequently.and_eventually {p q : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x := by
  refine mt (fun h => hq.mp <| h.mono ?_) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩

theorem Eventually.and_frequently {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∃ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x := by
  simpa only [and_comm] using hq.and_eventually hp

theorem Frequently.exists {p : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x) : ∃ x, p x := by
  by_contra H
  replace H : ∀ᶠ x in f, ¬p x := Eventually.of_forall (not_exists.1 H)
  exact hp H

theorem Eventually.exists {p : α → Prop} {f : Filter α} [NeBot f] (hp : ∀ᶠ x in f, p x) :
    ∃ x, p x :=
  hp.frequently.exists

lemma frequently_iff_neBot {l : Filter α} {p : α → Prop} :
    (∃ᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x}) := by
  rw [neBot_iff, Ne, inf_principal_eq_bot]; rfl

lemma frequently_mem_iff_neBot {l : Filter α} {s : Set α} : (∃ᶠ x in l, x ∈ s) ↔ NeBot (l ⊓ 𝓟 s) :=
  frequently_iff_neBot

theorem frequently_iff_forall_eventually_exists_and {p : α → Prop} {f : Filter α} :
    (∃ᶠ x in f, p x) ↔ ∀ {q : α → Prop}, (∀ᶠ x in f, q x) → ∃ x, p x ∧ q x :=
  ⟨fun hp _ hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [and_not_self_iff, exists_false] using H hp⟩

theorem frequently_iff {f : Filter α} {P : α → Prop} :
    (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x := by
  simp only [frequently_iff_forall_eventually_exists_and, @and_comm (P _)]
  rfl

@[simp]
theorem not_eventually {p : α → Prop} {f : Filter α} : (¬∀ᶠ x in f, p x) ↔ ∃ᶠ x in f, ¬p x := by
  simp [Filter.Frequently]

@[simp]
theorem not_frequently {p : α → Prop} {f : Filter α} : (¬∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, ¬p x := by
  simp only [Filter.Frequently, not_not]

@[simp]
theorem frequently_true_iff_neBot (f : Filter α) : (∃ᶠ _ in f, True) ↔ NeBot f := by
  simp [frequently_iff_neBot]

@[simp]
theorem frequently_false (f : Filter α) : ¬∃ᶠ _ in f, False := by simp

@[simp]
theorem frequently_const {f : Filter α} [NeBot f] {p : Prop} : (∃ᶠ _ in f, p) ↔ p := by
  by_cases p <;> simp [*]

@[simp]
theorem frequently_or_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x ∨ q x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, ← not_and_or, not_or, eventually_and]

theorem frequently_or_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∨ q x) ↔ p ∨ ∃ᶠ x in f, q x := by simp

theorem frequently_or_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∨ q) ↔ (∃ᶠ x in f, p x) ∨ q := by simp

theorem frequently_imp_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∃ᶠ x in f, q x := by
  simp [imp_iff_not_or]

theorem frequently_imp_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p → q x) ↔ p → ∃ᶠ x in f, q x := by simp [frequently_imp_distrib]

theorem frequently_imp_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x → q) ↔ (∀ᶠ x in f, p x) → q := by
  simp only [frequently_imp_distrib, frequently_const]

theorem eventually_imp_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x → q) ↔ (∃ᶠ x in f, p x) → q := by
  simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]

@[simp]
theorem frequently_and_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∧ q x) ↔ p ∧ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, not_and, eventually_imp_distrib_left, Classical.not_imp]

@[simp]
theorem frequently_and_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∧ q) ↔ (∃ᶠ x in f, p x) ∧ q := by
  simp only [@and_comm _ q, frequently_and_distrib_left]

@[simp]
theorem frequently_bot {p : α → Prop} : ¬∃ᶠ x in ⊥, p x := by simp

@[simp]
theorem frequently_top {p : α → Prop} : (∃ᶠ x in ⊤, p x) ↔ ∃ x, p x := by simp [Filter.Frequently]

@[simp]
theorem frequently_principal {a : Set α} {p : α → Prop} : (∃ᶠ x in 𝓟 a, p x) ↔ ∃ x ∈ a, p x := by
  simp [Filter.Frequently, not_forall]

theorem frequently_inf_principal {f : Filter α} {s : Set α} {p : α → Prop} :
    (∃ᶠ x in f ⊓ 𝓟 s, p x) ↔ ∃ᶠ x in f, x ∈ s ∧ p x := by
  simp only [Filter.Frequently, eventually_inf_principal, not_and]

alias ⟨Frequently.of_inf_principal, Frequently.inf_principal⟩ := frequently_inf_principal

theorem frequently_sup {p : α → Prop} {f g : Filter α} :
    (∃ᶠ x in f ⊔ g, p x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in g, p x := by
  simp only [Filter.Frequently, eventually_sup, not_and_or]

@[simp]
theorem frequently_sSup {p : α → Prop} {fs : Set (Filter α)} :
    (∃ᶠ x in sSup fs, p x) ↔ ∃ f ∈ fs, ∃ᶠ x in f, p x := by
  simp only [Filter.Frequently, not_forall, eventually_sSup, exists_prop]

@[simp]
theorem frequently_iSup {p : α → Prop} {fs : β → Filter α} :
    (∃ᶠ x in ⨆ b, fs b, p x) ↔ ∃ b, ∃ᶠ x in fs b, p x := by
  simp only [Filter.Frequently, eventually_iSup, not_forall]

theorem Eventually.choice {r : α → β → Prop} {l : Filter α} [l.NeBot] (h : ∀ᶠ x in l, ∃ y, r x y) :
    ∃ f : α → β, ∀ᶠ x in l, r x (f x) := by
  haveI : Nonempty β := let ⟨_, hx⟩ := h.exists; hx.nonempty
  choose! f hf using fun x (hx : ∃ y, r x y) => hx
  exact ⟨f, h.mono hf⟩

lemma skolem {ι : Type*} {α : ι → Type*} [∀ i, Nonempty (α i)]
    {P : ∀ i : ι, α i → Prop} {F : Filter ι} :
    (∀ᶠ i in F, ∃ b, P i b) ↔ ∃ b : (Π i, α i), ∀ᶠ i in F, P i (b i) := by
  classical
  refine ⟨fun H ↦ ?_, fun ⟨b, hb⟩ ↦ hb.mp (.of_forall fun x a ↦ ⟨_, a⟩)⟩
  refine ⟨fun i ↦ if h : ∃ b, P i b then h.choose else Nonempty.some inferInstance, ?_⟩
  filter_upwards [H] with i hi
  exact dif_pos hi ▸ hi.choose_spec

/-!
### Relation “eventually equal”
-/

section EventuallyEq
variable {l : Filter α} {f g : α → β}

theorem EventuallyEq.eventually (h : f =ᶠ[l] g) : ∀ᶠ x in l, f x = g x := h

@[simp] lemma eventuallyEq_top : f =ᶠ[⊤] g ↔ f = g := by simp [EventuallyEq, funext_iff]

theorem EventuallyEq.rw {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (p : α → β → Prop)
    (hf : ∀ᶠ x in l, p x (f x)) : ∀ᶠ x in l, p x (g x) :=
  hf.congr <| h.mono fun _ hx => hx ▸ Iff.rfl

theorem eventuallyEq_set {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ s ↔ x ∈ t :=
  eventually_congr <| Eventually.of_forall fun _ ↦ eq_iff_iff

alias ⟨EventuallyEq.mem_iff, Eventually.set_eq⟩ := eventuallyEq_set

@[simp]
theorem eventuallyEq_univ {s : Set α} {l : Filter α} : s =ᶠ[l] univ ↔ s ∈ l := by
  simp [eventuallyEq_set]

theorem EventuallyEq.exists_mem {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) :
    ∃ s ∈ l, EqOn f g s :=
  Eventually.exists_mem h

theorem eventuallyEq_of_mem {l : Filter α} {f g : α → β} {s : Set α} (hs : s ∈ l) (h : EqOn f g s) :
    f =ᶠ[l] g :=
  eventually_of_mem hs h

theorem eventuallyEq_iff_exists_mem {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ ∃ s ∈ l, EqOn f g s :=
  eventually_iff_exists_mem

theorem EventuallyEq.filter_mono {l l' : Filter α} {f g : α → β} (h₁ : f =ᶠ[l] g) (h₂ : l' ≤ l) :
    f =ᶠ[l'] g :=
  h₂ h₁

@[refl, simp]
theorem EventuallyEq.refl (l : Filter α) (f : α → β) : f =ᶠ[l] f :=
  Eventually.of_forall fun _ => rfl

protected theorem EventuallyEq.rfl {l : Filter α} {f : α → β} : f =ᶠ[l] f :=
  EventuallyEq.refl l f

theorem EventuallyEq.of_eq {l : Filter α} {f g : α → β} (h : f = g) : f =ᶠ[l] g := h ▸ .rfl
alias _root_.Eq.eventuallyEq := EventuallyEq.of_eq

@[symm]
theorem EventuallyEq.symm {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) : g =ᶠ[l] f :=
  H.mono fun _ => Eq.symm

lemma eventuallyEq_comm {f g : α → β} {l : Filter α} : f =ᶠ[l] g ↔ g =ᶠ[l] f := ⟨.symm, .symm⟩

@[trans]
theorem EventuallyEq.trans {l : Filter α} {f g h : α → β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) :
    f =ᶠ[l] h :=
  H₂.rw (fun x y => f x = y) H₁

theorem EventuallyEq.congr_left {l : Filter α} {f g h : α → β} (H : f =ᶠ[l] g) :
    f =ᶠ[l] h ↔ g =ᶠ[l] h :=
  ⟨H.symm.trans, H.trans⟩

theorem EventuallyEq.congr_right {l : Filter α} {f g h : α → β} (H : g =ᶠ[l] h) :
    f =ᶠ[l] g ↔ f =ᶠ[l] h :=
  ⟨(·.trans H), (·.trans H.symm)⟩

instance {l : Filter α} :
    Trans ((· =ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· =ᶠ[l] ·) (· =ᶠ[l] ·) where
  trans := EventuallyEq.trans

theorem EventuallyEq.prodMk {l} {f f' : α → β} (hf : f =ᶠ[l] f') {g g' : α → γ} (hg : g =ᶠ[l] g') :
    (fun x => (f x, g x)) =ᶠ[l] fun x => (f' x, g' x) :=
  hf.mp <|
    hg.mono <| by
      intros
      simp only [*]

@[deprecated (since := "2025-02-22")]
alias EventuallyEq.prod_mk := EventuallyEq.prodMk

-- See `EventuallyEq.comp_tendsto` further below for a similar statement w.r.t.
-- composition on the right.
theorem EventuallyEq.fun_comp {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) (h : β → γ) :
    h ∘ f =ᶠ[l] h ∘ g :=
  H.mono fun _ hx => congr_arg h hx

theorem EventuallyEq.comp₂ {δ} {f f' : α → β} {g g' : α → γ} {l} (Hf : f =ᶠ[l] f') (h : β → γ → δ)
    (Hg : g =ᶠ[l] g') : (fun x => h (f x) (g x)) =ᶠ[l] fun x => h (f' x) (g' x) :=
  (Hf.prodMk Hg).fun_comp (uncurry h)

@[to_additive]
theorem EventuallyEq.mul [Mul β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : (fun x => f x * f' x) =ᶠ[l] fun x => g x * g' x :=
  h.comp₂ (· * ·) h'

@[to_additive const_smul]
theorem EventuallyEq.pow_const {γ} [Pow β γ] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) (c : γ) :
    (fun x => f x ^ c) =ᶠ[l] fun x => g x ^ c :=
  h.fun_comp (· ^ c)

@[to_additive]
theorem EventuallyEq.inv [Inv β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    (fun x => (f x)⁻¹) =ᶠ[l] fun x => (g x)⁻¹ :=
  h.fun_comp Inv.inv

@[to_additive]
theorem EventuallyEq.div [Div β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : (fun x => f x / f' x) =ᶠ[l] fun x => g x / g' x :=
  h.comp₂ (· / ·) h'

attribute [to_additive] EventuallyEq.const_smul

@[to_additive]
theorem EventuallyEq.smul {𝕜} [SMul 𝕜 β] {l : Filter α} {f f' : α → 𝕜} {g g' : α → β}
    (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : (fun x => f x • g x) =ᶠ[l] fun x => f' x • g' x :=
  hf.comp₂ (· • ·) hg

theorem EventuallyEq.sup [Max β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : (fun x => f x ⊔ g x) =ᶠ[l] fun x => f' x ⊔ g' x :=
  hf.comp₂ (· ⊔ ·) hg

theorem EventuallyEq.inf [Min β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : (fun x => f x ⊓ g x) =ᶠ[l] fun x => f' x ⊓ g' x :=
  hf.comp₂ (· ⊓ ·) hg

theorem EventuallyEq.preimage {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (s : Set β) :
    f ⁻¹' s =ᶠ[l] g ⁻¹' s :=
  h.fun_comp s

theorem EventuallyEq.inter {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∩ s' : Set α) =ᶠ[l] (t ∩ t' : Set α) :=
  h.comp₂ (· ∧ ·) h'

theorem EventuallyEq.union {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∪ s' : Set α) =ᶠ[l] (t ∪ t' : Set α) :=
  h.comp₂ (· ∨ ·) h'

theorem EventuallyEq.compl {s t : Set α} {l : Filter α} (h : s =ᶠ[l] t) :
    (sᶜ : Set α) =ᶠ[l] (tᶜ : Set α) :=
  h.fun_comp Not

theorem EventuallyEq.diff {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s \ s' : Set α) =ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl

protected theorem EventuallyEq.symmDiff {s t s' t' : Set α} {l : Filter α}
    (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') : (s ∆ s' : Set α) =ᶠ[l] (t ∆ t' : Set α) :=
  (h.diff h').union (h'.diff h)

theorem eventuallyEq_empty {s : Set α} {l : Filter α} : s =ᶠ[l] (∅ : Set α) ↔ ∀ᶠ x in l, x ∉ s :=
  eventuallyEq_set.trans <| by simp

theorem inter_eventuallyEq_left {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] s ↔ ∀ᶠ x in l, x ∈ s → x ∈ t := by
  simp only [eventuallyEq_set, mem_inter_iff, and_iff_left_iff_imp]

theorem inter_eventuallyEq_right {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ t → x ∈ s := by
  rw [inter_comm, inter_eventuallyEq_left]

@[simp]
theorem eventuallyEq_principal {s : Set α} {f g : α → β} : f =ᶠ[𝓟 s] g ↔ EqOn f g s :=
  Iff.rfl

theorem eventuallyEq_inf_principal_iff {F : Filter α} {s : Set α} {f g : α → β} :
    f =ᶠ[F ⊓ 𝓟 s] g ↔ ∀ᶠ x in F, x ∈ s → f x = g x :=
  eventually_inf_principal

theorem EventuallyEq.sub_eq [AddGroup β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    f - g =ᶠ[l] 0 := by simpa using ((EventuallyEq.refl l f).sub h).symm

theorem eventuallyEq_iff_sub [AddGroup β] {f g : α → β} {l : Filter α} :
    f =ᶠ[l] g ↔ f - g =ᶠ[l] 0 :=
  ⟨fun h => h.sub_eq, fun h => by simpa using h.add (EventuallyEq.refl l g)⟩

theorem eventuallyEq_iff_all_subsets {f g : α → β} {l : Filter α} :
    f =ᶠ[l] g ↔ ∀ s : Set α, ∀ᶠ x in l, x ∈ s → f x = g x :=
  eventually_iff_all_subsets

section LE

variable [LE β] {l : Filter α}

theorem EventuallyLE.congr {f f' g g' : α → β} (H : f ≤ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f' ≤ᶠ[l] g' :=
  H.mp <| hg.mp <| hf.mono fun x hf hg H => by rwa [hf, hg] at H

theorem eventuallyLE_congr {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f ≤ᶠ[l] g ↔ f' ≤ᶠ[l] g' :=
  ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩

theorem eventuallyLE_iff_all_subsets {f g : α → β} {l : Filter α} :
    f ≤ᶠ[l] g ↔ ∀ s : Set α, ∀ᶠ x in l, x ∈ s → f x ≤ g x :=
  eventually_iff_all_subsets

end LE

section Preorder

variable [Preorder β] {l : Filter α} {f g h : α → β}

theorem EventuallyEq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g :=
  h.mono fun _ => le_of_eq

@[refl]
theorem EventuallyLE.refl (l : Filter α) (f : α → β) : f ≤ᶠ[l] f :=
  EventuallyEq.rfl.le

theorem EventuallyLE.rfl : f ≤ᶠ[l] f :=
  EventuallyLE.refl l f

@[trans]
theorem EventuallyLE.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₂.mp <| H₁.mono fun _ => le_trans

instance : Trans ((· ≤ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· ≤ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyLE.trans

@[trans]
theorem EventuallyEq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.le.trans H₂

instance : Trans ((· =ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· ≤ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyEq.trans_le

@[trans]
theorem EventuallyLE.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.trans H₂.le

instance : Trans ((· ≤ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· =ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyLE.trans_eq

end Preorder

variable {l : Filter α}

theorem EventuallyLE.antisymm [PartialOrder β] {l : Filter α} {f g : α → β} (h₁ : f ≤ᶠ[l] g)
    (h₂ : g ≤ᶠ[l] f) : f =ᶠ[l] g :=
  h₂.mp <| h₁.mono fun _ => le_antisymm

theorem eventuallyLE_antisymm_iff [PartialOrder β] {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ f ≤ᶠ[l] g ∧ g ≤ᶠ[l] f := by
  simp only [EventuallyEq, EventuallyLE, le_antisymm_iff, eventually_and]

theorem EventuallyLE.le_iff_eq [PartialOrder β] {l : Filter α} {f g : α → β} (h : f ≤ᶠ[l] g) :
    g ≤ᶠ[l] f ↔ g =ᶠ[l] f :=
  ⟨fun h' => h'.antisymm h, EventuallyEq.le⟩

theorem Eventually.ne_of_lt [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ᶠ x in l, f x < g x) :
    ∀ᶠ x in l, f x ≠ g x :=
  h.mono fun _ hx => hx.ne

theorem Eventually.ne_top_of_lt [PartialOrder β] [OrderTop β] {l : Filter α} {f g : α → β}
    (h : ∀ᶠ x in l, f x < g x) : ∀ᶠ x in l, f x ≠ ⊤ :=
  h.mono fun _ hx => hx.ne_top

theorem Eventually.lt_top_of_ne [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β}
    (h : ∀ᶠ x in l, f x ≠ ⊤) : ∀ᶠ x in l, f x < ⊤ :=
  h.mono fun _ hx => hx.lt_top

theorem Eventually.lt_top_iff_ne_top [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β} :
    (∀ᶠ x in l, f x < ⊤) ↔ ∀ᶠ x in l, f x ≠ ⊤ :=
  ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩

@[mono]
theorem EventuallyLE.inter {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∩ s' : Set α) ≤ᶠ[l] (t ∩ t' : Set α) :=
  h'.mp <| h.mono fun _ => And.imp

@[mono]
theorem EventuallyLE.union {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∪ s' : Set α) ≤ᶠ[l] (t ∪ t' : Set α) :=
  h'.mp <| h.mono fun _ => Or.imp

@[mono]
theorem EventuallyLE.compl {s t : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) :
    (tᶜ : Set α) ≤ᶠ[l] (sᶜ : Set α) :=
  h.mono fun _ => mt

@[mono]
theorem EventuallyLE.diff {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : t' ≤ᶠ[l] s') :
    (s \ s' : Set α) ≤ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl

theorem set_eventuallyLE_iff_mem_inf_principal {s t : Set α} {l : Filter α} :
    s ≤ᶠ[l] t ↔ t ∈ l ⊓ 𝓟 s :=
  eventually_inf_principal.symm

theorem set_eventuallyLE_iff_inf_principal_le {s t : Set α} {l : Filter α} :
    s ≤ᶠ[l] t ↔ l ⊓ 𝓟 s ≤ l ⊓ 𝓟 t :=
  set_eventuallyLE_iff_mem_inf_principal.trans <| by
    simp only [le_inf_iff, inf_le_left, true_and, le_principal_iff]

theorem set_eventuallyEq_iff_inf_principal {s t : Set α} {l : Filter α} :
    s =ᶠ[l] t ↔ l ⊓ 𝓟 s = l ⊓ 𝓟 t := by
  simp only [eventuallyLE_antisymm_iff, le_antisymm_iff, set_eventuallyLE_iff_inf_principal_le]

theorem EventuallyLE.sup [SemilatticeSup β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂)
    (hg : g₁ ≤ᶠ[l] g₂) : f₁ ⊔ g₁ ≤ᶠ[l] f₂ ⊔ g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using sup_le_sup hfx hgx

theorem EventuallyLE.sup_le [SemilatticeSup β] {l : Filter α} {f g h : α → β} (hf : f ≤ᶠ[l] h)
    (hg : g ≤ᶠ[l] h) : f ⊔ g ≤ᶠ[l] h := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.sup_le hfx hgx

theorem EventuallyLE.le_sup_of_le_left [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hf : h ≤ᶠ[l] f) : h ≤ᶠ[l] f ⊔ g :=
  hf.mono fun _ => _root_.le_sup_of_le_left

theorem EventuallyLE.le_sup_of_le_right [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hg : h ≤ᶠ[l] g) : h ≤ᶠ[l] f ⊔ g :=
  hg.mono fun _ => _root_.le_sup_of_le_right

theorem join_le {f : Filter (Filter α)} {l : Filter α} (h : ∀ᶠ m in f, m ≤ l) : join f ≤ l :=
  fun _ hs => h.mono fun _ hm => hm hs

end EventuallyEq

end Filter

open Filter

theorem Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α → β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g :=
  h

theorem Set.EqOn.eventuallyEq_of_mem {α β} {s : Set α} {l : Filter α} {f g : α → β} (h : EqOn f g s)
    (hl : s ∈ l) : f =ᶠ[l] g :=
  h.eventuallyEq.filter_mono <| Filter.le_principal_iff.2 hl

theorem HasSubset.Subset.eventuallyLE {α} {l : Filter α} {s t : Set α} (h : s ⊆ t) : s ≤ᶠ[l] t :=
  Filter.Eventually.of_forall h

variable {α β : Type*} {F : Filter α} {G : Filter β}

namespace Filter

lemma compl_mem_comk {p : Set α → Prop} {he hmono hunion s} :
    sᶜ ∈ comk p he hmono hunion ↔ p s := by
  simp

end Filter
