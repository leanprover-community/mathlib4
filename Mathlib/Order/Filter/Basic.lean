/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathlib.Data.Set.Finite
import English.Builtins
#align_import order.filter.basic from "leanprover-community/mathlib"@"d4f691b9e5f94cfc64639973f3544c95f8d5d494"

/-!
# Theory of filters on sets

## Main definitions

* `Filter` : filters on a set;
* `Filter.principal` : filter of all sets containing a given set;
* `Filter.map`, `Filter.comap` : operations on filters;
* `Filter.Tendsto` : limit with respect to filters;
* `Filter.Eventually` : `f.eventually p` means `{x | p x} ∈ f`;
* `Filter.Frequently` : `f.frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` :
  a tactic that takes a list of proofs `hᵢ : sᵢ ∈ f`,
  and replaces a goal `s ∈ f` with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `Filter.NeBot f` : a utility class stating that `f` is a non-trivial filter.

Filters on a type `X` are sets of sets of `X` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

In this file, we define the type `Filter X` of filters on `X`, and endow it with a complete lattice
structure. This structure is lifted from the lattice structure on `Set (Set X)` using the Galois
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
* `μ.ae` : made of sets whose complement has zero measure with respect to `μ` (defined in
  `MeasureTheory.MeasureSpace`)

The general notion of limit of a map with respect to filters on the source and target types
is `Filter.Tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `Filter.Eventually`, and "happening often" is
`Filter.Frequently`, whose definitions are immediate after `Filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

For instance, anticipating on Topology.Basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from Topology.Basic.

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

set_option autoImplicit true

open English LeanTeX
open Function Set Order
open scoped Classical

@[english_param const.Set] def param_Set : EnglishParam
| fvarid, _deps, type@(.app _ (.app (.const `Set _) X)), _used => do
  trace[English] "Using the english_param handler for Set"
  addNoun' fvarid #[type]
    { kind := `Set
      article := .a
      text := nt!"set{.s} of sets in {X}"
      inlineText := nt!"set{.s} {fvarid} of sets in {X}" }
| fvarid, _deps, type@(.app _ X), _used => do
  trace[English] "Using the english_param handler for Set"
  addNoun' fvarid #[type]
    { kind := `Set
      article := .a
      text := nt!"set{.s} in {X}"
      inlineText := nt!"set{.s} {fvarid} in {X}" }
| _, _, _, _ => failure

universe u v w x y

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
#align filter Filter

@[english_param const.Filter] def param_Filter : EnglishParam
| fvarid, _deps, type@(.app _ X), _used => do
  trace[English] "Using the english_param handler for Filter"
  addNoun' fvarid #[type]
    { kind := `Filter
      article := .a
      text := nt!"filter{.s} on {X}"
      inlineText := nt!"filter{.s} {fvarid} on {X}" }
| _, _, _, _ => failure

latex_pp_app_rules (const := Filter.sets)
  | _, #[_, f] => do
    let A ← latexPP f
    return A.sub (LatexData.atomString "\\mathrm{Sets}")

latex_pp_app_rules (const := HasCompl.compl)
  | _, #[_, _, f] => do
    let A ← latexPP f
    return A.sup (LatexData.atomString "c")

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
instance {α : Type*} : Membership (Set α) (Filter α) :=
  ⟨fun U F => U ∈ F.sets⟩

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

@[simp]
protected theorem mem_mk {t : Set (Set α)} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t :=
  Iff.rfl
#align filter.mem_mk Filter.mem_mk

@[simp]
protected theorem mem_sets : s ∈ f.sets ↔ s ∈ f :=
  Iff.rfl
#align filter.mem_sets Filter.mem_sets

instance inhabitedMem : Inhabited { s : Set α // s ∈ f } :=
  ⟨⟨univ, f.univ_sets⟩⟩
#align filter.inhabited_mem Filter.inhabitedMem

theorem filter_eq : ∀ {f g : Filter α}, f.sets = g.sets → f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
#align filter.filter_eq Filter.filter_eq

theorem filter_eq_iff : f = g ↔ f.sets = g.sets :=
  ⟨congr_arg _, filter_eq⟩
#align filter.filter_eq_iff Filter.filter_eq_iff

protected theorem ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g := by
  simp only [filter_eq_iff, ext_iff, Filter.mem_sets]
#align filter.ext_iff Filter.ext_iff

@[ext]
protected theorem ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
  Filter.ext_iff.2
#align filter.ext Filter.ext

/-- An extensionality lemma that is useful for filters with good lemmas about `sᶜ ∈ f` (e.g.,
`Filter.comap`, `Filter.coprod`, `Filter.Coprod`, `Filter.cofinite`). -/
protected theorem coext (h : ∀ s, sᶜ ∈ f ↔ sᶜ ∈ g) : f = g :=
  Filter.ext <| compl_surjective.forall.2 h
#align filter.coext Filter.coext

@[simp]
theorem univ_mem : univ ∈ f :=
  f.univ_sets
#align filter.univ_mem Filter.univ_mem

theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy
#align filter.mem_of_superset Filter.mem_of_superset

instance : Trans (· ⊇ ·) ((· ∈ ·) : Set α → Filter α → Prop) (· ∈ ·) where
  trans h₁ h₂ := mem_of_superset h₂ h₁

theorem inter_mem {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
  f.inter_sets hs ht
#align filter.inter_mem Filter.inter_mem

@[simp]
theorem inter_mem_iff {s t : Set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f :=
  ⟨fun h => ⟨mem_of_superset h (inter_subset_left s t), mem_of_superset h (inter_subset_right s t)⟩,
    and_imp.2 inter_mem⟩
#align filter.inter_mem_iff Filter.inter_mem_iff

theorem diff_mem {s t : Set α} (hs : s ∈ f) (ht : tᶜ ∈ f) : s \ t ∈ f :=
  inter_mem hs ht
#align filter.diff_mem Filter.diff_mem

theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x
#align filter.univ_mem' Filter.univ_mem'

theorem mp_mem (hs : s ∈ f) (h : { x | x ∈ s → x ∈ t } ∈ f) : t ∈ f :=
  mem_of_superset (inter_mem hs h) fun _ ⟨h₁, h₂⟩ => h₂ h₁
#align filter.mp_mem Filter.mp_mem

theorem congr_sets (h : { x | x ∈ s ↔ x ∈ t } ∈ f) : s ∈ f ↔ t ∈ f :=
  ⟨fun hs => mp_mem hs (mem_of_superset h fun _ => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun _ => Iff.mpr)⟩
#align filter.congr_sets Filter.congr_sets

/-- Override `sets` field of a filter to provide better definitional equality. -/
protected def copy (f : Filter α) (S : Set (Set α)) (hmem : ∀ s, s ∈ S ↔ s ∈ f) : Filter α where
  sets := S
  univ_sets := (hmem _).2 univ_mem
  sets_of_superset h hsub := (hmem _).2 <| mem_of_superset ((hmem _).1 h) hsub
  inter_sets h₁ h₂ := (hmem _).2 <| inter_mem ((hmem _).1 h₁) ((hmem _).1 h₂)

lemma copy_eq {S} (hmem : ∀ s, s ∈ S ↔ s ∈ f) : f.copy S hmem = f := Filter.ext hmem

@[simp] lemma mem_copy {S hmem} : s ∈ f.copy S hmem ↔ s ∈ S := Iff.rfl

@[simp]
theorem biInter_mem {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Finite) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
  Finite.induction_on hf (by simp) fun _ _ hs => by simp [hs]
#align filter.bInter_mem Filter.biInter_mem

@[simp]
theorem biInter_finset_mem {β : Type v} {s : β → Set α} (is : Finset β) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
  biInter_mem is.finite_toSet
#align filter.bInter_finset_mem Filter.biInter_finset_mem

alias _root_.Finset.iInter_mem_sets := biInter_finset_mem
#align finset.Inter_mem_sets Finset.iInter_mem_sets

-- attribute [protected] Finset.iInter_mem_sets porting note: doesn't work

@[simp]
theorem sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s ∈ f ↔ ∀ U ∈ s, U ∈ f := by
  rw [sInter_eq_biInter, biInter_mem hfin]
#align filter.sInter_mem Filter.sInter_mem

@[simp]
theorem iInter_mem {β : Sort v} {s : β → Set α} [Finite β] : (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f :=
  (sInter_mem (finite_range _)).trans forall_mem_range
#align filter.Inter_mem Filter.iInter_mem

theorem exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
  ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩
#align filter.exists_mem_subset_iff Filter.exists_mem_subset_iff

theorem monotone_mem {f : Filter α} : Monotone fun s => s ∈ f := fun _ _ hst h =>
  mem_of_superset h hst
#align filter.monotone_mem Filter.monotone_mem

theorem exists_mem_and_iff {P : Set α → Prop} {Q : Set α → Prop} (hP : Antitone P)
    (hQ : Antitone Q) : ((∃ u ∈ f, P u) ∧ ∃ u ∈ f, Q u) ↔ ∃ u ∈ f, P u ∧ Q u := by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u ∩ v, inter_mem huf hvf, hP (inter_subset_left _ _) hPu, hQ (inter_subset_right _ _) hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩
#align filter.exists_mem_and_iff Filter.exists_mem_and_iff

theorem forall_in_swap {β : Type*} {p : Set α → β → Prop} :
    (∀ a ∈ f, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ f, p a b :=
  Set.forall_in_swap
#align filter.forall_in_swap Filter.forall_in_swap

end Filter

