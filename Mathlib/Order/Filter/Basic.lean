/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathlib.Data.Set.Finite

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


open Function Set Order
open scoped Classical

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

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/--
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/
syntax (name := filterUpwards) "filter_upwards" (" [" term,* "]")?
  (" with" (ppSpace colGt term:max)*)? (" using " term)? : tactic

elab_rules : tactic
| `(tactic| filter_upwards $[[$[$args],*]]? $[with $wth*]? $[using $usingArg]?) => do
  let config : ApplyConfig := {newGoals := ApplyNewGoals.nonDependentOnly}
  for e in args.getD #[] |>.reverse do
    let goal ← getMainGoal
    replaceMainGoal <| ← goal.withContext <| runTermElab do
      let m ← mkFreshExprMVar none
      let lem ← Term.elabTermEnsuringType
        (← ``(Filter.mp_mem $e $(← Term.exprToSyntax m))) (← goal.getType)
      goal.assign lem
      return [m.mvarId!]
  liftMetaTactic fun goal => do
    goal.apply (← mkConstWithFreshMVarLevels ``Filter.univ_mem') config
  evalTactic <|← `(tactic| dsimp (config := {zeta := false}) only [Set.mem_setOf_eq])
  if let some l := wth then
    evalTactic <|← `(tactic| intro $[$l]*)
  if let some e := usingArg then
    evalTactic <|← `(tactic| exact $e)

end Mathlib.Tactic

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

section Principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter
#align filter.principal Filter.principal

@[inherit_doc]
scoped notation "𝓟" => Filter.principal

@[simp] theorem mem_principal {s t : Set α} : s ∈ 𝓟 t ↔ t ⊆ s := Iff.rfl
#align filter.mem_principal Filter.mem_principal

theorem mem_principal_self (s : Set α) : s ∈ 𝓟 s := Subset.rfl
#align filter.mem_principal_self Filter.mem_principal_self

end Principal

open Filter

section Join

/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join (f : Filter (Filter α)) : Filter α where
  sets := { s | { t : Filter α | s ∈ t } ∈ f }
  univ_sets := by simp only [mem_setOf_eq, univ_sets, ← Filter.mem_sets, setOf_true]
  sets_of_superset hx xy := mem_of_superset hx fun f h => mem_of_superset h xy
  inter_sets hx hy := mem_of_superset (inter_mem hx hy) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂
#align filter.join Filter.join

@[simp]
theorem mem_join {s : Set α} {f : Filter (Filter α)} : s ∈ join f ↔ { t | s ∈ t } ∈ f :=
  Iff.rfl
#align filter.mem_join Filter.mem_join

end Join

section Lattice

variable {f g : Filter α} {s t : Set α}

instance : PartialOrder (Filter α) where
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

theorem le_def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl
#align filter.le_def Filter.le_def

protected theorem not_le : ¬f ≤ g ↔ ∃ s ∈ g, s ∉ f := by simp_rw [le_def, not_forall, exists_prop]
#align filter.not_le Filter.not_le

/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)
#align filter.generate_sets Filter.GenerateSets

/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter
#align filter.generate Filter.generate

lemma mem_generate_of_mem {s : Set <| Set α} {U : Set α} (h : U ∈ s) :
    U ∈ generate s := GenerateSets.basic h

theorem le_generate_iff {s : Set (Set α)} {f : Filter α} : f ≤ generate s ↔ s ⊆ f.sets :=
  Iff.intro (fun h _ hu => h <| GenerateSets.basic <| hu) fun h _ hu =>
    hu.recOn (fun h' => h h') univ_mem (fun _ hxy hx => mem_of_superset hx hxy) fun _ _ hx hy =>
      inter_mem hx hy
#align filter.sets_iff_generate Filter.le_generate_iff

theorem mem_generate_iff {s : Set <| Set α} {U : Set α} :
    U ∈ generate s ↔ ∃ t ⊆ s, Set.Finite t ∧ ⋂₀ t ⊆ U := by
  constructor <;> intro h
  · induction h with
    | @basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).subset⟩
    | univ => exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    | superset _ hVW hV =>
      rcases hV with ⟨t, hts, ht, htV⟩
      exact ⟨t, hts, ht, htV.trans hVW⟩
    | inter _ _ hV hW =>
      rcases hV, hW with ⟨⟨t, hts, ht, htV⟩, u, hus, hu, huW⟩
      exact
        ⟨t ∪ u, union_subset hts hus, ht.union hu,
          (sInter_union _ _).subset.trans <| inter_subset_inter htV huW⟩
  · rcases h with ⟨t, hts, tfin, h⟩
    exact mem_of_superset ((sInter_mem tfin).2 fun V hV => GenerateSets.basic <| hts hV) h
#align filter.mem_generate_iff Filter.mem_generate_iff

@[simp] lemma generate_singleton (s : Set α) : generate {s} = 𝓟 s :=
  le_antisymm (fun _t ht ↦ mem_of_superset (mem_generate_of_mem <| mem_singleton _) ht) <|
    le_generate_iff.2 <| singleton_subset_iff.2 Subset.rfl

/-- `mk_of_closure s hs` constructs a filter on `α` whose elements set is exactly
`s : Set (Set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
protected def mkOfClosure (s : Set (Set α)) (hs : (generate s).sets = s) : Filter α where
  sets := s
  univ_sets := hs ▸ univ_mem
  sets_of_superset := hs ▸ mem_of_superset
  inter_sets := hs ▸ inter_mem
#align filter.mk_of_closure Filter.mkOfClosure

theorem mkOfClosure_sets {s : Set (Set α)} {hs : (generate s).sets = s} :
    Filter.mkOfClosure s hs = generate s :=
  Filter.ext fun u =>
    show u ∈ (Filter.mkOfClosure s hs).sets ↔ u ∈ (generate s).sets from hs.symm ▸ Iff.rfl
#align filter.mk_of_closure_sets Filter.mkOfClosure_sets

/-- Galois insertion from sets of sets into filters. -/
def giGenerate (α : Type*) :
    @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ Filter.generate Filter.sets where
  gc _ _ := le_generate_iff
  le_l_u _ _ h := GenerateSets.basic h
  choice s hs := Filter.mkOfClosure s (le_antisymm hs <| le_generate_iff.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets
#align filter.gi_generate Filter.giGenerate

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
instance : Inf (Filter α) :=
  ⟨fun f g : Filter α =>
    { sets := { s | ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b }
      univ_sets := ⟨_, univ_mem, _, univ_mem, by simp⟩
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine'
          ⟨a ∪ y, mem_of_superset ha (subset_union_left a y), b ∪ y,
            mem_of_superset hb (subset_union_left b y), _⟩
        rw [← inter_union_distrib_right, union_eq_self_of_subset_left xy]
      inter_sets := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine' ⟨a ∩ c, inter_mem ha hc, b ∩ d, inter_mem hb hd, _⟩
        ac_rfl }⟩

theorem mem_inf_iff {f g : Filter α} {s : Set α} : s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ :=
  Iff.rfl
#align filter.mem_inf_iff Filter.mem_inf_iff

theorem mem_inf_of_left {f g : Filter α} {s : Set α} (h : s ∈ f) : s ∈ f ⊓ g :=
  ⟨s, h, univ, univ_mem, (inter_univ s).symm⟩
#align filter.mem_inf_of_left Filter.mem_inf_of_left

theorem mem_inf_of_right {f g : Filter α} {s : Set α} (h : s ∈ g) : s ∈ f ⊓ g :=
  ⟨univ, univ_mem, s, h, (univ_inter s).symm⟩
#align filter.mem_inf_of_right Filter.mem_inf_of_right

theorem inter_mem_inf {α : Type u} {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) :
    s ∩ t ∈ f ⊓ g :=
  ⟨s, hs, t, ht, rfl⟩
#align filter.inter_mem_inf Filter.inter_mem_inf

theorem mem_inf_of_inter {f g : Filter α} {s t u : Set α} (hs : s ∈ f) (ht : t ∈ g)
    (h : s ∩ t ⊆ u) : u ∈ f ⊓ g :=
  mem_of_superset (inter_mem_inf hs ht) h
#align filter.mem_inf_of_inter Filter.mem_inf_of_inter

theorem mem_inf_iff_superset {f g : Filter α} {s : Set α} :
    s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ∩ t₂ ⊆ s :=
  ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ Subset.rfl⟩, fun ⟨_, h₁, _, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩
#align filter.mem_inf_iff_superset Filter.mem_inf_iff_superset

instance : Top (Filter α) :=
  ⟨{  sets := { s | ∀ x, x ∈ s }
      univ_sets := fun x => mem_univ x
      sets_of_superset := fun hx hxy a => hxy (hx a)
      inter_sets := fun hx hy _ => mem_inter (hx _) (hy _) }⟩

theorem mem_top_iff_forall {s : Set α} : s ∈ (⊤ : Filter α) ↔ ∀ x, x ∈ s :=
  Iff.rfl
#align filter.mem_top_iff_forall Filter.mem_top_iff_forall

@[simp]
theorem mem_top {s : Set α} : s ∈ (⊤ : Filter α) ↔ s = univ := by
  rw [mem_top_iff_forall, eq_univ_iff_forall]
#align filter.mem_top Filter.mem_top

section CompleteLattice

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for some lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/
instance instCompleteLatticeFilter : CompleteLattice (Filter α) :=
  { @OrderDual.instCompleteLattice _ (giGenerate α).liftCompleteLattice with
    le := (· ≤ ·)
    top := ⊤
    le_top := fun _ _s hs => (mem_top.1 hs).symm ▸ univ_mem
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => mem_inf_of_left
    inf_le_right := fun _ _ _ => mem_inf_of_right
    le_inf := fun _ _ _ h₁ h₂ _s ⟨_a, ha, _b, hb, hs⟩ => hs.symm ▸ inter_mem (h₁ ha) (h₂ hb)
    sSup := join ∘ 𝓟
    le_sSup := fun _ _f hf _s hs => hs hf
    sSup_le := fun _ _f hf _s hs _g hg => hf _ hg hs }

instance : Inhabited (Filter α) := ⟨⊥⟩

end CompleteLattice

/-- A filter is `NeBot` if it is not equal to `⊥`, or equivalently the empty set does not belong to
the filter. Bourbaki include this assumption in the definition of a filter but we prefer to have a
`CompleteLattice` structure on `Filter _`, so we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥
#align filter.ne_bot Filter.NeBot

theorem neBot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align filter.ne_bot_iff Filter.neBot_iff

theorem NeBot.ne {f : Filter α} (hf : NeBot f) : f ≠ ⊥ := hf.ne'
#align filter.ne_bot.ne Filter.NeBot.ne

@[simp] theorem not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥ := neBot_iff.not_left
#align filter.not_ne_bot Filter.not_neBot

theorem NeBot.mono {f g : Filter α} (hf : NeBot f) (hg : f ≤ g) : NeBot g :=
  ⟨ne_bot_of_le_ne_bot hf.1 hg⟩
#align filter.ne_bot.mono Filter.NeBot.mono

theorem neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f ≤ g) : NeBot g :=
  hf.mono hg
#align filter.ne_bot_of_le Filter.neBot_of_le

@[simp] theorem sup_neBot {f g : Filter α} : NeBot (f ⊔ g) ↔ NeBot f ∨ NeBot g := by
  simp only [neBot_iff, not_and_or, Ne.def, sup_eq_bot_iff]
#align filter.sup_ne_bot Filter.sup_neBot

theorem not_disjoint_self_iff : ¬Disjoint f f ↔ f.NeBot := by rw [disjoint_self, neBot_iff]
#align filter.not_disjoint_self_iff Filter.not_disjoint_self_iff

theorem bot_sets_eq : (⊥ : Filter α).sets = univ := rfl
#align filter.bot_sets_eq Filter.bot_sets_eq

/-- Either `f = ⊥` or `Filter.NeBot f`. This is a version of `eq_or_ne` that uses `Filter.NeBot`
as the second alternative, to be used as an instance. -/
theorem eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f := (eq_or_ne f ⊥).imp_right NeBot.mk

theorem sup_sets_eq {f g : Filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
  (giGenerate α).gc.u_inf
#align filter.sup_sets_eq Filter.sup_sets_eq

theorem sSup_sets_eq {s : Set (Filter α)} : (sSup s).sets = ⋂ f ∈ s, (f : Filter α).sets :=
  (giGenerate α).gc.u_sInf
#align filter.Sup_sets_eq Filter.sSup_sets_eq

theorem iSup_sets_eq {f : ι → Filter α} : (iSup f).sets = ⋂ i, (f i).sets :=
  (giGenerate α).gc.u_iInf
#align filter.supr_sets_eq Filter.iSup_sets_eq

theorem generate_empty : Filter.generate ∅ = (⊤ : Filter α) :=
  (giGenerate α).gc.l_bot
#align filter.generate_empty Filter.generate_empty

theorem generate_univ : Filter.generate univ = (⊥ : Filter α) :=
  bot_unique fun _ _ => GenerateSets.basic (mem_univ _)
#align filter.generate_univ Filter.generate_univ

theorem generate_union {s t : Set (Set α)} :
    Filter.generate (s ∪ t) = Filter.generate s ⊓ Filter.generate t :=
  (giGenerate α).gc.l_sup
#align filter.generate_union Filter.generate_union

theorem generate_iUnion {s : ι → Set (Set α)} :
    Filter.generate (⋃ i, s i) = ⨅ i, Filter.generate (s i) :=
  (giGenerate α).gc.l_iSup
#align filter.generate_Union Filter.generate_iUnion

@[simp]
theorem mem_bot {s : Set α} : s ∈ (⊥ : Filter α) :=
  trivial
#align filter.mem_bot Filter.mem_bot

@[simp]
theorem mem_sup {f g : Filter α} {s : Set α} : s ∈ f ⊔ g ↔ s ∈ f ∧ s ∈ g :=
  Iff.rfl
#align filter.mem_sup Filter.mem_sup

theorem union_mem_sup {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∪ t ∈ f ⊔ g :=
  ⟨mem_of_superset hs (subset_union_left s t), mem_of_superset ht (subset_union_right s t)⟩
#align filter.union_mem_sup Filter.union_mem_sup

@[simp]
theorem mem_sSup {x : Set α} {s : Set (Filter α)} : x ∈ sSup s ↔ ∀ f ∈ s, x ∈ (f : Filter α) :=
  Iff.rfl
#align filter.mem_Sup Filter.mem_sSup

@[simp]
theorem mem_iSup {x : Set α} {f : ι → Filter α} : x ∈ iSup f ↔ ∀ i, x ∈ f i := by
  simp only [← Filter.mem_sets, iSup_sets_eq, iff_self_iff, mem_iInter]
#align filter.mem_supr Filter.mem_iSup

@[simp]
theorem iSup_neBot {f : ι → Filter α} : (⨆ i, f i).NeBot ↔ ∃ i, (f i).NeBot := by
  simp [neBot_iff]
#align filter.supr_ne_bot Filter.iSup_neBot

theorem iInf_eq_generate (s : ι → Filter α) : iInf s = generate (⋃ i, (s i).sets) :=
  show generate _ = generate _ from congr_arg _ <| congr_arg sSup <| (range_comp _ _).symm
#align filter.infi_eq_generate Filter.iInf_eq_generate

theorem mem_iInf_of_mem {f : ι → Filter α} (i : ι) {s} (hs : s ∈ f i) : s ∈ ⨅ i, f i :=
  iInf_le f i hs
#align filter.mem_infi_of_mem Filter.mem_iInf_of_mem

theorem mem_iInf_of_iInter {ι} {s : ι → Filter α} {U : Set α} {I : Set ι} (I_fin : I.Finite)
    {V : I → Set α} (hV : ∀ i, V i ∈ s i) (hU : ⋂ i, V i ⊆ U) : U ∈ ⨅ i, s i := by
  haveI := I_fin.fintype
  refine' mem_of_superset (iInter_mem.2 fun i => _) hU
  exact mem_iInf_of_mem (i : ι) (hV _)
#align filter.mem_infi_of_Inter Filter.mem_iInf_of_iInter

theorem mem_iInf {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔ ∃ I : Set ι, I.Finite ∧ ∃ V : I → Set α, (∀ i, V i ∈ s i) ∧ U = ⋂ i, V i := by
  constructor
  · rw [iInf_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_iUnion_of_finite_subset_iUnion tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_iUnion] at tinter
    set V := fun i => U ∪ ⋂₀ σ i with hV
    have V_in : ∀ i, V i ∈ s i := by
      rintro i
      have : ⋂₀ σ i ∈ s i := by
        rw [sInter_mem (σfin _)]
        apply σsub
      exact mem_of_superset this (subset_union_right _ _)
    refine' ⟨I, Ifin, V, V_in, _⟩
    rwa [hV, ← union_iInter, union_eq_self_of_subset_right]
  · rintro ⟨I, Ifin, V, V_in, rfl⟩
    exact mem_iInf_of_iInter Ifin V_in Subset.rfl
#align filter.mem_infi Filter.mem_iInf

theorem mem_iInf' {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι, I.Finite ∧ ∃ V : ι → Set α, (∀ i, V i ∈ s i) ∧
        (∀ i ∉ I, V i = univ) ∧ (U = ⋂ i ∈ I, V i) ∧ U = ⋂ i, V i := by
  simp only [mem_iInf, SetCoe.forall', biInter_eq_iInter]
  refine' ⟨_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine' ⟨I, If, fun i => if hi : i ∈ I then V ⟨i, hi⟩ else univ, fun i => _, fun i hi => _, _⟩
  · dsimp only
    split_ifs
    exacts [hV _, univ_mem]
  · exact dif_neg hi
  · simp only [iInter_dite, biInter_eq_iInter, dif_pos (Subtype.coe_prop _), Subtype.coe_eta,
      iInter_univ, inter_univ, eq_self_iff_true, true_and_iff]
#align filter.mem_infi' Filter.mem_iInf'

theorem exists_iInter_of_mem_iInf {ι : Type*} {α : Type*} {f : ι → Filter α} {s}
    (hs : s ∈ ⨅ i, f i) : ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i :=
  let ⟨_, _, V, hVs, _, _, hVU'⟩ := mem_iInf'.1 hs; ⟨V, hVs, hVU'⟩
#align filter.exists_Inter_of_mem_infi Filter.exists_iInter_of_mem_iInf

theorem mem_iInf_of_finite {ι : Type*} [Finite ι] {α : Type*} {f : ι → Filter α} (s) :
    (s ∈ ⨅ i, f i) ↔ ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i := by
  refine' ⟨exists_iInter_of_mem_iInf, _⟩
  rintro ⟨t, ht, rfl⟩
  exact iInter_mem.2 fun i => mem_iInf_of_mem i (ht i)
#align filter.mem_infi_of_finite Filter.mem_iInf_of_finite

@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩
#align filter.le_principal_iff Filter.le_principal_iff

theorem Iic_principal (s : Set α) : Iic (𝓟 s) = { l | s ∈ l } :=
  Set.ext fun _ => le_principal_iff
#align filter.Iic_principal Filter.Iic_principal

theorem principal_mono {s t : Set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  simp only [le_principal_iff, iff_self_iff, mem_principal]
#align filter.principal_mono Filter.principal_mono

@[mono]
theorem monotone_principal : Monotone (𝓟 : Set α → Filter α) := fun _ _ => principal_mono.2
#align filter.monotone_principal Filter.monotone_principal

@[simp] theorem principal_eq_iff_eq {s t : Set α} : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal]; rfl
#align filter.principal_eq_iff_eq Filter.principal_eq_iff_eq

@[simp] theorem join_principal_eq_sSup {s : Set (Filter α)} : join (𝓟 s) = sSup s := rfl
#align filter.join_principal_eq_Sup Filter.join_principal_eq_sSup

@[simp] theorem principal_univ : 𝓟 (univ : Set α) = ⊤ :=
  top_unique <| by simp only [le_principal_iff, mem_top, eq_self_iff_true]
#align filter.principal_univ Filter.principal_univ

@[simp]
theorem principal_empty : 𝓟 (∅ : Set α) = ⊥ :=
  bot_unique fun _ _ => empty_subset _
#align filter.principal_empty Filter.principal_empty

theorem generate_eq_biInf (S : Set (Set α)) : generate S = ⨅ s ∈ S, 𝓟 s :=
  eq_of_forall_le_iff fun f => by simp [le_generate_iff, le_principal_iff, subset_def]
#align filter.generate_eq_binfi Filter.generate_eq_biInf

/-! ### Lattice equations -/

theorem empty_mem_iff_bot {f : Filter α} : ∅ ∈ f ↔ f = ⊥ :=
  ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩
#align filter.empty_mem_iff_bot Filter.empty_mem_iff_bot

theorem nonempty_of_mem {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id
#align filter.nonempty_of_mem Filter.nonempty_of_mem

theorem NeBot.nonempty_of_mem {f : Filter α} (hf : NeBot f) {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  @Filter.nonempty_of_mem α f hf s hs
#align filter.ne_bot.nonempty_of_mem Filter.NeBot.nonempty_of_mem

@[simp]
theorem empty_not_mem (f : Filter α) [NeBot f] : ¬∅ ∈ f := fun h => (nonempty_of_mem h).ne_empty rfl
#align filter.empty_not_mem Filter.empty_not_mem

theorem nonempty_of_neBot (f : Filter α) [NeBot f] : Nonempty α :=
  nonempty_of_exists <| nonempty_of_mem (univ_mem : univ ∈ f)
#align filter.nonempty_of_ne_bot Filter.nonempty_of_neBot

theorem compl_not_mem {f : Filter α} {s : Set α} [NeBot f] (h : s ∈ f) : sᶜ ∉ f := fun hsc =>
  (nonempty_of_mem (inter_mem h hsc)).ne_empty <| inter_compl_self s
#align filter.compl_not_mem Filter.compl_not_mem

theorem filter_eq_bot_of_isEmpty [IsEmpty α] (f : Filter α) : f = ⊥ :=
  empty_mem_iff_bot.mp <| univ_mem' isEmptyElim
#align filter.filter_eq_bot_of_is_empty Filter.filter_eq_bot_of_isEmpty

protected lemma disjoint_iff {f g : Filter α} : Disjoint f g ↔ ∃ s ∈ f, ∃ t ∈ g, Disjoint s t := by
  simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff, inf_eq_inter, bot_eq_empty,
    @eq_comm _ ∅]
#align filter.disjoint_iff Filter.disjoint_iff

theorem disjoint_of_disjoint_of_mem {f g : Filter α} {s t : Set α} (h : Disjoint s t) (hs : s ∈ f)
    (ht : t ∈ g) : Disjoint f g :=
  Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩
#align filter.disjoint_of_disjoint_of_mem Filter.disjoint_of_disjoint_of_mem

theorem NeBot.not_disjoint (hf : f.NeBot) (hs : s ∈ f) (ht : t ∈ f) : ¬Disjoint s t := fun h =>
  not_disjoint_self_iff.2 hf <| Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩
#align filter.ne_bot.not_disjoint Filter.NeBot.not_disjoint

theorem inf_eq_bot_iff {f g : Filter α} : f ⊓ g = ⊥ ↔ ∃ U ∈ f, ∃ V ∈ g, U ∩ V = ∅ := by
  simp only [← disjoint_iff, Filter.disjoint_iff, Set.disjoint_iff_inter_eq_empty]
#align filter.inf_eq_bot_iff Filter.inf_eq_bot_iff

theorem _root_.Pairwise.exists_mem_filter_of_disjoint {ι : Type*} [Finite ι] {l : ι → Filter α}
    (hd : Pairwise (Disjoint on l)) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ Pairwise (Disjoint on s) := by
  have : Pairwise fun i j => ∃ (s : {s // s ∈ l i}) (t : {t // t ∈ l j}), Disjoint s.1 t.1 := by
    simpa only [Pairwise, Function.onFun, Filter.disjoint_iff, exists_prop, Subtype.exists] using hd
  choose! s t hst using this
  refine' ⟨fun i => ⋂ j, @s i j ∩ @t j i, fun i => _, fun i j hij => _⟩
  exacts [iInter_mem.2 fun j => inter_mem (@s i j).2 (@t j i).2,
    (hst hij).mono ((iInter_subset _ j).trans (inter_subset_left _ _))
      ((iInter_subset _ i).trans (inter_subset_right _ _))]
#align pairwise.exists_mem_filter_of_disjoint Pairwise.exists_mem_filter_of_disjoint

theorem _root_.Set.PairwiseDisjoint.exists_mem_filter {ι : Type*} {l : ι → Filter α} {t : Set ι}
    (hd : t.PairwiseDisjoint l) (ht : t.Finite) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ t.PairwiseDisjoint s := by
  haveI := ht.to_subtype
  rcases (hd.subtype _ _).exists_mem_filter_of_disjoint with ⟨s, hsl, hsd⟩
  lift s to (i : t) → {s // s ∈ l i} using hsl
  -- TODO: Lean fails to find `CanLift` instance
  rcases @Subtype.exists_pi_extension ι (fun i => { s // s ∈ l i }) _ _ s with ⟨s, rfl⟩
  exact ⟨fun i => s i, fun i => (s i).2, hsd.set_of_subtype _ _⟩
#align set.pairwise_disjoint.exists_mem_filter Set.PairwiseDisjoint.exists_mem_filter

/-- There is exactly one filter on an empty type. -/
instance unique [IsEmpty α] : Unique (Filter α) where
  default := ⊥
  uniq := filter_eq_bot_of_isEmpty
#align filter.unique Filter.unique

theorem NeBot.nonempty (f : Filter α) [hf : f.NeBot] : Nonempty α :=
  not_isEmpty_iff.mp fun _ ↦ hf.ne (Subsingleton.elim _ _)

/-- There are only two filters on a `subsingleton`: `⊥` and `⊤`. If the type is empty, then they are
equal. -/
theorem eq_top_of_neBot [Subsingleton α] (l : Filter α) [NeBot l] : l = ⊤ := by
  refine' top_unique fun s hs => _
  obtain rfl : s = univ; exact Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem
#align filter.eq_top_of_ne_bot Filter.eq_top_of_neBot

theorem forall_mem_nonempty_iff_neBot {f : Filter α} :
    (∀ s : Set α, s ∈ f → s.Nonempty) ↔ NeBot f :=
  ⟨fun h => ⟨fun hf => not_nonempty_empty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩
#align filter.forall_mem_nonempty_iff_ne_bot Filter.forall_mem_nonempty_iff_neBot

instance instNontrivialFilter [Nonempty α] : Nontrivial (Filter α) :=
  ⟨⟨⊤, ⊥, NeBot.ne <| forall_mem_nonempty_iff_neBot.1
    fun s hs => by rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]⟩⟩

theorem nontrivial_iff_nonempty : Nontrivial (Filter α) ↔ Nonempty α :=
  ⟨fun _ =>
    by_contra fun h' =>
      haveI := not_nonempty_iff.1 h'
      not_subsingleton (Filter α) inferInstance,
    @Filter.instNontrivialFilter α⟩
#align filter.nontrivial_iff_nonempty Filter.nontrivial_iff_nonempty

theorem eq_sInf_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = sInf S :=
  le_antisymm (le_sInf fun f hf _ hs => h.2 ⟨f, hf, hs⟩)
    fun _ hs => let ⟨_, hf, hs⟩ := h.1 hs; (sInf_le hf) hs
#align filter.eq_Inf_of_mem_iff_exists_mem Filter.eq_sInf_of_mem_iff_exists_mem

theorem eq_iInf_of_mem_iff_exists_mem {f : ι → Filter α} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) : l = iInf f :=
  eq_sInf_of_mem_iff_exists_mem <| h.trans exists_range_iff.symm
#align filter.eq_infi_of_mem_iff_exists_mem Filter.eq_iInf_of_mem_iff_exists_mem

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem eq_biInf_of_mem_iff_exists_mem {f : ι → Filter α} {p : ι → Prop} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ i, p i ∧ s ∈ f i) : l = ⨅ (i) (_ : p i), f i := by
  rw [iInf_subtype']
  exact eq_iInf_of_mem_iff_exists_mem fun {_} => by simp only [Subtype.exists, h, exists_prop]
#align filter.eq_binfi_of_mem_iff_exists_mem Filter.eq_biInf_of_mem_iff_exists_memₓ

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
  (congr_arg Filter.sets this.symm).trans <| by simp only
#align filter.infi_sets_eq Filter.iInf_sets_eq

theorem mem_iInf_of_directed {f : ι → Filter α} (h : Directed (· ≥ ·) f) [Nonempty ι] (s) :
    s ∈ iInf f ↔ ∃ i, s ∈ f i := by
  simp only [← Filter.mem_sets, iInf_sets_eq h, mem_iUnion]
#align filter.mem_infi_of_directed Filter.mem_iInf_of_directed

theorem mem_biInf_of_directed {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) {t : Set α} : (t ∈ ⨅ i ∈ s, f i) ↔ ∃ i ∈ s, t ∈ f i := by
  haveI := ne.to_subtype
  simp_rw [iInf_subtype', mem_iInf_of_directed h.directed_val, Subtype.exists, exists_prop]
#align filter.mem_binfi_of_directed Filter.mem_biInf_of_directed

theorem biInf_sets_eq {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s)
    (ne : s.Nonempty) : (⨅ i ∈ s, f i).sets = ⋃ i ∈ s, (f i).sets :=
  ext fun t => by simp [mem_biInf_of_directed h ne]
#align filter.binfi_sets_eq Filter.biInf_sets_eq

theorem iInf_sets_eq_finite {ι : Type*} (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset ι, (⨅ i ∈ t, f i).sets := by
  rw [iInf_eq_iInf_finset, iInf_sets_eq]
  exact directed_of_isDirected_le fun _ _ => biInf_mono
#align filter.infi_sets_eq_finite Filter.iInf_sets_eq_finite

theorem iInf_sets_eq_finite' (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset (PLift ι), (⨅ i ∈ t, f (PLift.down i)).sets := by
  rw [← iInf_sets_eq_finite, ← Equiv.plift.surjective.iInf_comp]
  rfl
#align filter.infi_sets_eq_finite' Filter.iInf_sets_eq_finite'

theorem mem_iInf_finite {ι : Type*} {f : ι → Filter α} (s) :
    s ∈ iInf f ↔ ∃ t : Finset ι, s ∈ ⨅ i ∈ t, f i :=
  (Set.ext_iff.1 (iInf_sets_eq_finite f) s).trans mem_iUnion
#align filter.mem_infi_finite Filter.mem_iInf_finite

theorem mem_iInf_finite' {f : ι → Filter α} (s) :
    s ∈ iInf f ↔ ∃ t : Finset (PLift ι), s ∈ ⨅ i ∈ t, f (PLift.down i) :=
  (Set.ext_iff.1 (iInf_sets_eq_finite' f) s).trans mem_iUnion
#align filter.mem_infi_finite' Filter.mem_iInf_finite'

@[simp]
theorem sup_join {f₁ f₂ : Filter (Filter α)} : join f₁ ⊔ join f₂ = join (f₁ ⊔ f₂) :=
  Filter.ext fun x => by simp only [mem_sup, mem_join]
#align filter.sup_join Filter.sup_join

@[simp]
theorem iSup_join {ι : Sort w} {f : ι → Filter (Filter α)} : ⨆ x, join (f x) = join (⨆ x, f x) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_join]
#align filter.supr_join Filter.iSup_join

instance : DistribLattice (Filter α) :=
  { Filter.instCompleteLatticeFilter with
    le_sup_inf := by
      intro x y z s
      simp only [and_assoc, mem_inf_iff, mem_sup, exists_prop, exists_imp, and_imp]
      rintro hs t₁ ht₁ t₂ ht₂ rfl
      exact
        ⟨t₁, x.sets_of_superset hs (inter_subset_left t₁ t₂), ht₁, t₂,
          x.sets_of_superset hs (inter_subset_right t₁ t₂), ht₂, rfl⟩ }

-- The dual version does not hold! `Filter α` is not a `CompleteDistribLattice`. -/
instance : Coframe (Filter α) :=
  { Filter.instCompleteLatticeFilter with
    iInf_sup_le_sup_sInf := fun f s t ⟨h₁, h₂⟩ => by
      rw [iInf_subtype']
      rw [sInf_eq_iInf', iInf_sets_eq_finite, mem_iUnion] at h₂
      obtain ⟨u, hu⟩ := h₂
      rw [← Finset.inf_eq_iInf] at hu
      suffices ⨅ i : s, f ⊔ ↑i ≤ f ⊔ u.inf fun i => ↑i from this ⟨h₁, hu⟩
      refine' Finset.induction_on u (le_sup_of_le_right le_top) _
      rintro ⟨i⟩ u _ ih
      rw [Finset.inf_insert, sup_inf_left]
      exact le_inf (iInf_le _ _) ih }

theorem mem_iInf_finset {s : Finset α} {f : α → Filter β} {t : Set β} :
    (t ∈ ⨅ a ∈ s, f a) ↔ ∃ p : α → Set β, (∀ a ∈ s, p a ∈ f a) ∧ t = ⋂ a ∈ s, p a := by
  simp only [← Finset.set_biInter_coe, biInter_eq_iInter, iInf_subtype']
  refine' ⟨fun h => _, _⟩
  · rcases (mem_iInf_of_finite _).1 h with ⟨p, hp, rfl⟩
    refine'
      ⟨fun a => if h : a ∈ s then p ⟨a, h⟩ else univ, fun a ha => by simpa [ha] using hp ⟨a, ha⟩, _⟩
    refine' iInter_congr_of_surjective id surjective_id _
    rintro ⟨a, ha⟩
    simp [ha]
  · rintro ⟨p, hpf, rfl⟩
    exact iInter_mem.2 fun a => mem_iInf_of_mem a (hpf a a.2)
#align filter.mem_infi_finset Filter.mem_iInf_finset

/-- If `f : ι → Filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `iInf f ≠ ⊥`.
See also `iInf_neBot_of_directed` for a version assuming `Nonempty α` instead of `Nonempty ι`. -/
theorem iInf_neBot_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    (∀ i, NeBot (f i)) → NeBot (iInf f) :=
  not_imp_not.1 <| by simpa only [not_forall, not_neBot, ← empty_mem_iff_bot,
    mem_iInf_of_directed hd] using id
#align filter.infi_ne_bot_of_directed' Filter.iInf_neBot_of_directed'

/-- If `f : ι → Filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `iInf f ≠ ⊥`.
See also `iInf_neBot_of_directed'` for a version assuming `Nonempty ι` instead of `Nonempty α`. -/
theorem iInf_neBot_of_directed {f : ι → Filter α} [hn : Nonempty α] (hd : Directed (· ≥ ·) f)
    (hb : ∀ i, NeBot (f i)) : NeBot (iInf f) := by
  cases isEmpty_or_nonempty ι
  · constructor
    simp [iInf_of_empty f, top_ne_bot]
  · exact iInf_neBot_of_directed' hd hb
#align filter.infi_ne_bot_of_directed Filter.iInf_neBot_of_directed

theorem sInf_neBot_of_directed' {s : Set (Filter α)} (hne : s.Nonempty) (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    @iInf_neBot_of_directed' _ _ _ hne.to_subtype hd.directed_val fun ⟨_, hf⟩ =>
      ⟨ne_of_mem_of_not_mem hf hbot⟩
#align filter.Inf_ne_bot_of_directed' Filter.sInf_neBot_of_directed'

theorem sInf_neBot_of_directed [Nonempty α] {s : Set (Filter α)} (hd : DirectedOn (· ≥ ·) s)
    (hbot : ⊥ ∉ s) : NeBot (sInf s) :=
  (sInf_eq_iInf' s).symm ▸
    iInf_neBot_of_directed hd.directed_val fun ⟨_, hf⟩ => ⟨ne_of_mem_of_not_mem hf hbot⟩
#align filter.Inf_ne_bot_of_directed Filter.sInf_neBot_of_directed

theorem iInf_neBot_iff_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    NeBot (iInf f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed' hd⟩
#align filter.infi_ne_bot_iff_of_directed' Filter.iInf_neBot_iff_of_directed'

theorem iInf_neBot_iff_of_directed {f : ι → Filter α} [Nonempty α] (hd : Directed (· ≥ ·) f) :
    NeBot (iInf f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (iInf_le _ i), iInf_neBot_of_directed hd⟩
#align filter.infi_ne_bot_iff_of_directed Filter.iInf_neBot_iff_of_directed

@[elab_as_elim]
theorem iInf_sets_induct {f : ι → Filter α} {s : Set α} (hs : s ∈ iInf f) {p : Set α → Prop}
    (uni : p univ) (ins : ∀ {i s₁ s₂}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂)) : p s := by
  rw [mem_iInf_finite'] at hs
  simp only [← Finset.inf_eq_iInf] at hs
  rcases hs with ⟨is, his⟩
  induction is using Finset.induction_on generalizing s with
  | empty => rwa [mem_top.1 his]
  | insert _ ih =>
    rw [Finset.inf_insert, mem_inf_iff] at his
    rcases his with ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    exact ins hs₁ (ih hs₂)
#align filter.infi_sets_induct Filter.iInf_sets_induct

/-! #### `principal` equations -/

@[simp]
theorem inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) :=
  le_antisymm
    (by simp only [le_principal_iff, mem_inf_iff]; exact ⟨s, Subset.rfl, t, Subset.rfl, rfl⟩)
    (by simp [le_inf_iff, inter_subset_left, inter_subset_right])
#align filter.inf_principal Filter.inf_principal

@[simp]
theorem sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) :=
  Filter.ext fun u => by simp only [union_subset_iff, mem_sup, mem_principal]
#align filter.sup_principal Filter.sup_principal

@[simp]
theorem iSup_principal {ι : Sort w} {s : ι → Set α} : ⨆ x, 𝓟 (s x) = 𝓟 (⋃ i, s i) :=
  Filter.ext fun x => by simp only [mem_iSup, mem_principal, iUnion_subset_iff]
#align filter.supr_principal Filter.iSup_principal

@[simp]
theorem principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ ↔ s = ∅ :=
  empty_mem_iff_bot.symm.trans <| mem_principal.trans subset_empty_iff
#align filter.principal_eq_bot_iff Filter.principal_eq_bot_iff

@[simp]
theorem principal_neBot_iff {s : Set α} : NeBot (𝓟 s) ↔ s.Nonempty :=
  neBot_iff.trans <| (not_congr principal_eq_bot_iff).trans nonempty_iff_ne_empty.symm
#align filter.principal_ne_bot_iff Filter.principal_neBot_iff

alias ⟨_, _root_.Set.Nonempty.principal_neBot⟩ := principal_neBot_iff
#align set.nonempty.principal_ne_bot Set.Nonempty.principal_neBot

theorem isCompl_principal (s : Set α) : IsCompl (𝓟 s) (𝓟 sᶜ) :=
  IsCompl.of_eq (by rw [inf_principal, inter_compl_self, principal_empty]) <| by
    rw [sup_principal, union_compl_self, principal_univ]
#align filter.is_compl_principal Filter.isCompl_principal

theorem mem_inf_principal' {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ tᶜ ∪ s ∈ f := by
  simp only [← le_principal_iff, (isCompl_principal s).le_left_iff, disjoint_assoc, inf_principal,
    ← (isCompl_principal (t ∩ sᶜ)).le_right_iff, compl_inter, compl_compl]
#align filter.mem_inf_principal' Filter.mem_inf_principal'

lemma mem_inf_principal {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ { x | x ∈ t → x ∈ s } ∈ f := by
  simp only [mem_inf_principal', imp_iff_not_or]
  rfl
#align filter.mem_inf_principal Filter.mem_inf_principal

lemma iSup_inf_principal (f : ι → Filter α) (s : Set α) : ⨆ i, f i ⊓ 𝓟 s = (⨆ i, f i) ⊓ 𝓟 s := by
  ext
  simp only [mem_iSup, mem_inf_principal]
#align filter.supr_inf_principal Filter.iSup_inf_principal

theorem inf_principal_eq_bot {f : Filter α} {s : Set α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ ∈ f := by
  rw [← empty_mem_iff_bot, mem_inf_principal]
  rfl
#align filter.inf_principal_eq_bot Filter.inf_principal_eq_bot

theorem mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 𝓟 sᶜ = ⊥) : s ∈ f := by
  rwa [inf_principal_eq_bot, compl_compl] at h
#align filter.mem_of_eq_bot Filter.mem_of_eq_bot

theorem diff_mem_inf_principal_compl {f : Filter α} {s : Set α} (hs : s ∈ f) (t : Set α) :
    s \ t ∈ f ⊓ 𝓟 tᶜ :=
  inter_mem_inf hs <| mem_principal_self tᶜ
#align filter.diff_mem_inf_principal_compl Filter.diff_mem_inf_principal_compl

theorem principal_le_iff {s : Set α} {f : Filter α} : 𝓟 s ≤ f ↔ ∀ V ∈ f, s ⊆ V := by
  change (∀ V, V ∈ f → V ∈ _) ↔ _
  simp_rw [mem_principal]
#align filter.principal_le_iff Filter.principal_le_iff

@[simp]
theorem iInf_principal_finset {ι : Type w} (s : Finset ι) (f : ι → Set α) :
    ⨅ i ∈ s, 𝓟 (f i) = 𝓟 (⋂ i ∈ s, f i) := by
  induction' s using Finset.induction_on with i s _ hs
  · simp
  · rw [Finset.iInf_insert, Finset.set_biInter_insert, hs, inf_principal]
#align filter.infi_principal_finset Filter.iInf_principal_finset

@[simp]
theorem iInf_principal {ι : Type w} [Finite ι] (f : ι → Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i) := by
  cases nonempty_fintype ι
  simpa using iInf_principal_finset Finset.univ f
#align filter.infi_principal Filter.iInf_principal

theorem iInf_principal_finite {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι → Set α) :
    ⨅ i ∈ s, 𝓟 (f i) = 𝓟 (⋂ i ∈ s, f i) := by
  lift s to Finset ι using hs
  exact mod_cast iInf_principal_finset s f
#align filter.infi_principal_finite Filter.iInf_principal_finite

end Lattice

@[mono]
theorem join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ ≤ f₂) : join f₁ ≤ join f₂ := fun _ hs => h hs
#align filter.join_mono Filter.join_mono

/-! ### Eventually -/

/-- `f.Eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in atTop, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
#align filter.eventually Filter.Eventually

@[inherit_doc Filter.Eventually]
notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

theorem eventually_iff {f : Filter α} {P : α → Prop} : (∀ᶠ x in f, P x) ↔ { x | P x } ∈ f :=
  Iff.rfl
#align filter.eventually_iff Filter.eventually_iff

@[simp]
theorem eventually_mem_set {s : Set α} {l : Filter α} : (∀ᶠ x in l, x ∈ s) ↔ s ∈ l :=
  Iff.rfl
#align filter.eventually_mem_set Filter.eventually_mem_set

protected theorem ext' {f₁ f₂ : Filter α}
    (h : ∀ p : α → Prop, (∀ᶠ x in f₁, p x) ↔ ∀ᶠ x in f₂, p x) : f₁ = f₂ :=
  Filter.ext h
#align filter.ext' Filter.ext'

theorem Eventually.filter_mono {f₁ f₂ : Filter α} (h : f₁ ≤ f₂) {p : α → Prop}
    (hp : ∀ᶠ x in f₂, p x) : ∀ᶠ x in f₁, p x :=
  h hp
#align filter.eventually.filter_mono Filter.Eventually.filter_mono

theorem eventually_of_mem {f : Filter α} {P : α → Prop} {U : Set α} (hU : U ∈ f)
    (h : ∀ x ∈ U, P x) : ∀ᶠ x in f, P x :=
  mem_of_superset hU h
#align filter.eventually_of_mem Filter.eventually_of_mem

protected theorem Eventually.and {p q : α → Prop} {f : Filter α} :
    f.Eventually p → f.Eventually q → ∀ᶠ x in f, p x ∧ q x :=
  inter_mem
#align filter.eventually.and Filter.Eventually.and

@[simp] theorem eventually_true (f : Filter α) : ∀ᶠ _ in f, True := univ_mem
#align filter.eventually_true Filter.eventually_true

theorem eventually_of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp
#align filter.eventually_of_forall Filter.eventually_of_forall

@[simp]
theorem eventually_false_iff_eq_bot {f : Filter α} : (∀ᶠ _ in f, False) ↔ f = ⊥ :=
  empty_mem_iff_bot
#align filter.eventually_false_iff_eq_bot Filter.eventually_false_iff_eq_bot

@[simp]
theorem eventually_const {f : Filter α} [t : NeBot f] {p : Prop} : (∀ᶠ _ in f, p) ↔ p :=
  by_cases (fun h : p => by simp [h]) fun h => by simpa [h] using t.ne
#align filter.eventually_const Filter.eventually_const

theorem eventually_iff_exists_mem {p : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x) ↔ ∃ v ∈ f, ∀ y ∈ v, p y :=
  exists_mem_subset_iff.symm
#align filter.eventually_iff_exists_mem Filter.eventually_iff_exists_mem

theorem Eventually.exists_mem {p : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) :
    ∃ v ∈ f, ∀ y ∈ v, p y :=
  eventually_iff_exists_mem.1 hp
#align filter.eventually.exists_mem Filter.Eventually.exists_mem

theorem Eventually.mp {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, p x → q x) : ∀ᶠ x in f, q x :=
  mp_mem hp hq
#align filter.eventually.mp Filter.Eventually.mp

theorem Eventually.mono {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∀ x, p x → q x) : ∀ᶠ x in f, q x :=
  hp.mp (eventually_of_forall hq)
#align filter.eventually.mono Filter.Eventually.mono

theorem forall_eventually_of_eventually_forall {f : Filter α} {p : α → β → Prop}
    (h : ∀ᶠ x in f, ∀ y, p x y) : ∀ y, ∀ᶠ x in f, p x y :=
  fun y => h.mono fun _ h => h y
#align filter.forall_eventually_of_eventually_forall Filter.forall_eventually_of_eventually_forall

@[simp]
theorem eventually_and {p q : α → Prop} {f : Filter α} :
    (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in f, q x :=
  inter_mem_iff
#align filter.eventually_and Filter.eventually_and

theorem Eventually.congr {f : Filter α} {p q : α → Prop} (h' : ∀ᶠ x in f, p x)
    (h : ∀ᶠ x in f, p x ↔ q x) : ∀ᶠ x in f, q x :=
  h'.mp (h.mono fun _ hx => hx.mp)
#align filter.eventually.congr Filter.Eventually.congr

theorem eventually_congr {f : Filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
    (∀ᶠ x in f, p x) ↔ ∀ᶠ x in f, q x :=
  ⟨fun hp => hp.congr h, fun hq => hq.congr <| by simpa only [Iff.comm] using h⟩
#align filter.eventually_congr Filter.eventually_congr

@[simp]
theorem eventually_all {ι : Sort*} [Finite ι] {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, setOf_forall] using iInter_mem
#align filter.eventually_all Filter.eventually_all

@[simp]
theorem eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, setOf_forall] using biInter_mem hI
#align filter.eventually_all_finite Filter.eventually_all_finite

alias _root_.Set.Finite.eventually_all := eventually_all_finite
#align set.finite.eventually_all Set.Finite.eventually_all

-- attribute [protected] Set.Finite.eventually_all

@[simp] theorem eventually_all_finset {ι} (I : Finset ι) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x :=
  I.finite_toSet.eventually_all
#align filter.eventually_all_finset Filter.eventually_all_finset

alias _root_.Finset.eventually_all := eventually_all_finset
#align finset.eventually_all Finset.eventually_all

-- attribute [protected] Finset.eventually_all

@[simp]
theorem eventually_or_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p ∨ q x) ↔ p ∨ ∀ᶠ x in f, q x :=
  by_cases (fun h : p => by simp [h]) fun h => by simp [h]
#align filter.eventually_or_distrib_left Filter.eventually_or_distrib_left

@[simp]
theorem eventually_or_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x ∨ q) ↔ (∀ᶠ x in f, p x) ∨ q := by
  simp only [@or_comm _ q, eventually_or_distrib_left]
#align filter.eventually_or_distrib_right Filter.eventually_or_distrib_right

theorem eventually_imp_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p → q x) ↔ p → ∀ᶠ x in f, q x :=
  eventually_all
#align filter.eventually_imp_distrib_left Filter.eventually_imp_distrib_left

@[simp]
theorem eventually_bot {p : α → Prop} : ∀ᶠ x in ⊥, p x :=
  ⟨⟩
#align filter.eventually_bot Filter.eventually_bot

@[simp]
theorem eventually_top {p : α → Prop} : (∀ᶠ x in ⊤, p x) ↔ ∀ x, p x :=
  Iff.rfl
#align filter.eventually_top Filter.eventually_top

@[simp]
theorem eventually_sup {p : α → Prop} {f g : Filter α} :
    (∀ᶠ x in f ⊔ g, p x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in g, p x :=
  Iff.rfl
#align filter.eventually_sup Filter.eventually_sup

@[simp]
theorem eventually_sSup {p : α → Prop} {fs : Set (Filter α)} :
    (∀ᶠ x in sSup fs, p x) ↔ ∀ f ∈ fs, ∀ᶠ x in f, p x :=
  Iff.rfl
#align filter.eventually_Sup Filter.eventually_sSup

@[simp]
theorem eventually_iSup {p : α → Prop} {fs : ι → Filter α} :
    (∀ᶠ x in ⨆ b, fs b, p x) ↔ ∀ b, ∀ᶠ x in fs b, p x :=
  mem_iSup
#align filter.eventually_supr Filter.eventually_iSup

@[simp]
theorem eventually_principal {a : Set α} {p : α → Prop} : (∀ᶠ x in 𝓟 a, p x) ↔ ∀ x ∈ a, p x :=
  Iff.rfl
#align filter.eventually_principal Filter.eventually_principal

theorem Eventually.forall_mem {α : Type*} {f : Filter α} {s : Set α} {P : α → Prop}
    (hP : ∀ᶠ x in f, P x) (hf : 𝓟 s ≤ f) : ∀ x ∈ s, P x :=
  Filter.eventually_principal.mp (hP.filter_mono hf)

theorem eventually_inf {f g : Filter α} {p : α → Prop} :
    (∀ᶠ x in f ⊓ g, p x) ↔ ∃ s ∈ f, ∃ t ∈ g, ∀ x ∈ s ∩ t, p x :=
  mem_inf_iff_superset
#align filter.eventually_inf Filter.eventually_inf

theorem eventually_inf_principal {f : Filter α} {p : α → Prop} {s : Set α} :
    (∀ᶠ x in f ⊓ 𝓟 s, p x) ↔ ∀ᶠ x in f, x ∈ s → p x :=
  mem_inf_principal
#align filter.eventually_inf_principal Filter.eventually_inf_principal

/-! ### Frequently -/

/-- `f.Frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in atTop, p x`
means that there exist arbitrarily large `x` for which `p` holds true. -/
protected def Frequently (p : α → Prop) (f : Filter α) : Prop :=
  ¬∀ᶠ x in f, ¬p x
#align filter.frequently Filter.Frequently

@[inherit_doc Filter.Frequently]
notation3 "∃ᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

theorem Eventually.frequently {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ᶠ x in f, p x) :
    ∃ᶠ x in f, p x :=
  compl_not_mem h
#align filter.eventually.frequently Filter.Eventually.frequently

theorem frequently_of_forall {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ x, p x) :
    ∃ᶠ x in f, p x :=
  Eventually.frequently (eventually_of_forall h)
#align filter.frequently_of_forall Filter.frequently_of_forall

theorem Frequently.mp {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ᶠ x in f, p x → q x) : ∃ᶠ x in f, q x :=
  mt (fun hq => hq.mp <| hpq.mono fun _ => mt) h
#align filter.frequently.mp Filter.Frequently.mp

theorem Frequently.filter_mono {p : α → Prop} {f g : Filter α} (h : ∃ᶠ x in f, p x) (hle : f ≤ g) :
    ∃ᶠ x in g, p x :=
  mt (fun h' => h'.filter_mono hle) h
#align filter.frequently.filter_mono Filter.Frequently.filter_mono

theorem Frequently.mono {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
    (hpq : ∀ x, p x → q x) : ∃ᶠ x in f, q x :=
  h.mp (eventually_of_forall hpq)
#align filter.frequently.mono Filter.Frequently.mono

theorem Frequently.and_eventually {p q : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x)
    (hq : ∀ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x := by
  refine' mt (fun h => hq.mp <| h.mono _) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩
#align filter.frequently.and_eventually Filter.Frequently.and_eventually

theorem Eventually.and_frequently {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
    (hq : ∃ᶠ x in f, q x) : ∃ᶠ x in f, p x ∧ q x := by
  simpa only [and_comm] using hq.and_eventually hp
#align filter.eventually.and_frequently Filter.Eventually.and_frequently

theorem Frequently.exists {p : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x) : ∃ x, p x := by
  by_contra H
  replace H : ∀ᶠ x in f, ¬p x := eventually_of_forall (not_exists.1 H)
  exact hp H
#align filter.frequently.exists Filter.Frequently.exists

theorem Eventually.exists {p : α → Prop} {f : Filter α} [NeBot f] (hp : ∀ᶠ x in f, p x) :
    ∃ x, p x :=
  hp.frequently.exists
#align filter.eventually.exists Filter.Eventually.exists

lemma frequently_iff_neBot {p : α → Prop} : (∃ᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x}) := by
  rw [neBot_iff, Ne.def, inf_principal_eq_bot]; rfl

lemma frequently_mem_iff_neBot {s : Set α} : (∃ᶠ x in l, x ∈ s) ↔ NeBot (l ⊓ 𝓟 s) :=
  frequently_iff_neBot

theorem frequently_iff_forall_eventually_exists_and {p : α → Prop} {f : Filter α} :
    (∃ᶠ x in f, p x) ↔ ∀ {q : α → Prop}, (∀ᶠ x in f, q x) → ∃ x, p x ∧ q x :=
  ⟨fun hp q hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [and_not_self_iff, exists_false] using H hp⟩
#align filter.frequently_iff_forall_eventually_exists_and Filter.frequently_iff_forall_eventually_exists_and

theorem frequently_iff {f : Filter α} {P : α → Prop} :
    (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x := by
  simp only [frequently_iff_forall_eventually_exists_and, @and_comm (P _)]
  rfl
#align filter.frequently_iff Filter.frequently_iff

@[simp]
theorem not_eventually {p : α → Prop} {f : Filter α} : (¬∀ᶠ x in f, p x) ↔ ∃ᶠ x in f, ¬p x := by
  simp [Filter.Frequently]
#align filter.not_eventually Filter.not_eventually

@[simp]
theorem not_frequently {p : α → Prop} {f : Filter α} : (¬∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, ¬p x := by
  simp only [Filter.Frequently, not_not]
#align filter.not_frequently Filter.not_frequently

@[simp]
theorem frequently_true_iff_neBot (f : Filter α) : (∃ᶠ _ in f, True) ↔ NeBot f := by
  simp [frequently_iff_neBot]
#align filter.frequently_true_iff_ne_bot Filter.frequently_true_iff_neBot

@[simp]
theorem frequently_false (f : Filter α) : ¬∃ᶠ _ in f, False := by simp
#align filter.frequently_false Filter.frequently_false

@[simp]
theorem frequently_const {f : Filter α} [NeBot f] {p : Prop} : (∃ᶠ _ in f, p) ↔ p :=
  by_cases (fun h : p => by simpa [h] ) fun h => by simp [h]
#align filter.frequently_const Filter.frequently_const

@[simp]
theorem frequently_or_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x ∨ q x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, ← not_and_or, not_or, eventually_and]
#align filter.frequently_or_distrib Filter.frequently_or_distrib

theorem frequently_or_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∨ q x) ↔ p ∨ ∃ᶠ x in f, q x := by simp
#align filter.frequently_or_distrib_left Filter.frequently_or_distrib_left

theorem frequently_or_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∨ q) ↔ (∃ᶠ x in f, p x) ∨ q := by simp
#align filter.frequently_or_distrib_right Filter.frequently_or_distrib_right

theorem frequently_imp_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∃ᶠ x in f, q x := by
  simp [imp_iff_not_or]
#align filter.frequently_imp_distrib Filter.frequently_imp_distrib

theorem frequently_imp_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p → q x) ↔ p → ∃ᶠ x in f, q x := by simp [frequently_imp_distrib]
#align filter.frequently_imp_distrib_left Filter.frequently_imp_distrib_left

theorem frequently_imp_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x → q) ↔ (∀ᶠ x in f, p x) → q := by
  set_option tactic.skipAssignedInstances false in simp [frequently_imp_distrib]
#align filter.frequently_imp_distrib_right Filter.frequently_imp_distrib_right

theorem eventually_imp_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x → q) ↔ (∃ᶠ x in f, p x) → q := by
  simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]
#align filter.eventually_imp_distrib_right Filter.eventually_imp_distrib_right

@[simp]
theorem frequently_and_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∧ q x) ↔ p ∧ ∃ᶠ x in f, q x := by
  simp only [Filter.Frequently, not_and, eventually_imp_distrib_left, not_imp]
#align filter.frequently_and_distrib_left Filter.frequently_and_distrib_left

@[simp]
theorem frequently_and_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∧ q) ↔ (∃ᶠ x in f, p x) ∧ q := by
  simp only [@and_comm _ q, frequently_and_distrib_left]
#align filter.frequently_and_distrib_right Filter.frequently_and_distrib_right

@[simp]
theorem frequently_bot {p : α → Prop} : ¬∃ᶠ x in ⊥, p x := by simp
#align filter.frequently_bot Filter.frequently_bot

@[simp]
theorem frequently_top {p : α → Prop} : (∃ᶠ x in ⊤, p x) ↔ ∃ x, p x := by simp [Filter.Frequently]
#align filter.frequently_top Filter.frequently_top

@[simp]
theorem frequently_principal {a : Set α} {p : α → Prop} : (∃ᶠ x in 𝓟 a, p x) ↔ ∃ x ∈ a, p x := by
  simp [Filter.Frequently, not_forall]
#align filter.frequently_principal Filter.frequently_principal

theorem frequently_sup {p : α → Prop} {f g : Filter α} :
    (∃ᶠ x in f ⊔ g, p x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in g, p x := by
  simp only [Filter.Frequently, eventually_sup, not_and_or]
#align filter.frequently_sup Filter.frequently_sup

@[simp]
theorem frequently_sSup {p : α → Prop} {fs : Set (Filter α)} :
    (∃ᶠ x in sSup fs, p x) ↔ ∃ f ∈ fs, ∃ᶠ x in f, p x := by
  simp only [Filter.Frequently, not_forall, eventually_sSup, exists_prop]
#align filter.frequently_Sup Filter.frequently_sSup

@[simp]
theorem frequently_iSup {p : α → Prop} {fs : β → Filter α} :
    (∃ᶠ x in ⨆ b, fs b, p x) ↔ ∃ b, ∃ᶠ x in fs b, p x := by
  simp only [Filter.Frequently, eventually_iSup, not_forall]
#align filter.frequently_supr Filter.frequently_iSup

theorem Eventually.choice {r : α → β → Prop} {l : Filter α} [l.NeBot] (h : ∀ᶠ x in l, ∃ y, r x y) :
    ∃ f : α → β, ∀ᶠ x in l, r x (f x) := by
  haveI : Nonempty β := let ⟨_, hx⟩ := h.exists; hx.nonempty
  choose! f hf using fun x (hx : ∃ y, r x y) => hx
  exact ⟨f, h.mono hf⟩
#align filter.eventually.choice Filter.Eventually.choice

/-!
### Relation “eventually equal”
-/

/-- Two functions `f` and `g` are *eventually equal* along a filter `l` if the set of `x` such that
`f x = g x` belongs to `l`. -/
def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x
#align filter.eventually_eq Filter.EventuallyEq

@[inherit_doc]
notation:50 f " =ᶠ[" l:50 "] " g:50 => EventuallyEq l f g

theorem EventuallyEq.eventually {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) :
    ∀ᶠ x in l, f x = g x :=
  h
#align filter.eventually_eq.eventually Filter.EventuallyEq.eventually

theorem EventuallyEq.rw {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (p : α → β → Prop)
    (hf : ∀ᶠ x in l, p x (f x)) : ∀ᶠ x in l, p x (g x) :=
  hf.congr <| h.mono fun _ hx => hx ▸ Iff.rfl
#align filter.eventually_eq.rw Filter.EventuallyEq.rw

theorem eventuallyEq_set {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ s ↔ x ∈ t :=
  eventually_congr <| eventually_of_forall fun _ ↦ eq_iff_iff
#align filter.eventually_eq_set Filter.eventuallyEq_set

alias ⟨EventuallyEq.mem_iff, Eventually.set_eq⟩ := eventuallyEq_set
#align filter.eventually_eq.mem_iff Filter.EventuallyEq.mem_iff
#align filter.eventually.set_eq Filter.Eventually.set_eq

@[simp]
theorem eventuallyEq_univ {s : Set α} {l : Filter α} : s =ᶠ[l] univ ↔ s ∈ l := by
  simp [eventuallyEq_set]
#align filter.eventually_eq_univ Filter.eventuallyEq_univ

theorem EventuallyEq.exists_mem {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) :
    ∃ s ∈ l, EqOn f g s :=
  Eventually.exists_mem h
#align filter.eventually_eq.exists_mem Filter.EventuallyEq.exists_mem

theorem eventuallyEq_of_mem {l : Filter α} {f g : α → β} {s : Set α} (hs : s ∈ l) (h : EqOn f g s) :
    f =ᶠ[l] g :=
  eventually_of_mem hs h
#align filter.eventually_eq_of_mem Filter.eventuallyEq_of_mem

theorem eventuallyEq_iff_exists_mem {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ ∃ s ∈ l, EqOn f g s :=
  eventually_iff_exists_mem
#align filter.eventually_eq_iff_exists_mem Filter.eventuallyEq_iff_exists_mem

theorem EventuallyEq.filter_mono {l l' : Filter α} {f g : α → β} (h₁ : f =ᶠ[l] g) (h₂ : l' ≤ l) :
    f =ᶠ[l'] g :=
  h₂ h₁
#align filter.eventually_eq.filter_mono Filter.EventuallyEq.filter_mono

@[refl]
theorem EventuallyEq.refl (l : Filter α) (f : α → β) : f =ᶠ[l] f :=
  eventually_of_forall fun _ => rfl
#align filter.eventually_eq.refl Filter.EventuallyEq.refl

protected theorem EventuallyEq.rfl {l : Filter α} {f : α → β} : f =ᶠ[l] f :=
  EventuallyEq.refl l f
#align filter.eventually_eq.rfl Filter.EventuallyEq.rfl

@[symm]
theorem EventuallyEq.symm {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) : g =ᶠ[l] f :=
  H.mono fun _ => Eq.symm
#align filter.eventually_eq.symm Filter.EventuallyEq.symm

@[trans]
theorem EventuallyEq.trans {l : Filter α} {f g h : α → β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) :
    f =ᶠ[l] h :=
  H₂.rw (fun x y => f x = y) H₁
#align filter.eventually_eq.trans Filter.EventuallyEq.trans

-- porting note (#10754): new instance
instance : Trans ((· =ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· =ᶠ[l] ·) (· =ᶠ[l] ·) where
  trans := EventuallyEq.trans

theorem EventuallyEq.prod_mk {l} {f f' : α → β} (hf : f =ᶠ[l] f') {g g' : α → γ} (hg : g =ᶠ[l] g') :
    (fun x => (f x, g x)) =ᶠ[l] fun x => (f' x, g' x) :=
  hf.mp <|
    hg.mono <| by
      intros
      simp only [*]
#align filter.eventually_eq.prod_mk Filter.EventuallyEq.prod_mk

-- See `EventuallyEq.comp_tendsto` further below for a similar statement w.r.t.
-- composition on the right.
theorem EventuallyEq.fun_comp {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) (h : β → γ) :
    h ∘ f =ᶠ[l] h ∘ g :=
  H.mono fun _ hx => congr_arg h hx
#align filter.eventually_eq.fun_comp Filter.EventuallyEq.fun_comp

theorem EventuallyEq.comp₂ {δ} {f f' : α → β} {g g' : α → γ} {l} (Hf : f =ᶠ[l] f') (h : β → γ → δ)
    (Hg : g =ᶠ[l] g') : (fun x => h (f x) (g x)) =ᶠ[l] fun x => h (f' x) (g' x) :=
  (Hf.prod_mk Hg).fun_comp (uncurry h)
#align filter.eventually_eq.comp₂ Filter.EventuallyEq.comp₂

@[to_additive]
theorem EventuallyEq.mul [Mul β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : (fun x => f x * f' x) =ᶠ[l] fun x => g x * g' x :=
  h.comp₂ (· * ·) h'
#align filter.eventually_eq.mul Filter.EventuallyEq.mul
#align filter.eventually_eq.add Filter.EventuallyEq.add

@[to_additive const_smul]
theorem EventuallyEq.pow_const {γ} [Pow β γ] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) (c : γ):
    (fun x => f x ^ c) =ᶠ[l] fun x => g x ^ c :=
  h.fun_comp (· ^ c)
#align filter.eventually_eq.const_smul Filter.EventuallyEq.const_smul

@[to_additive]
theorem EventuallyEq.inv [Inv β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    (fun x => (f x)⁻¹) =ᶠ[l] fun x => (g x)⁻¹ :=
  h.fun_comp Inv.inv
#align filter.eventually_eq.inv Filter.EventuallyEq.inv
#align filter.eventually_eq.neg Filter.EventuallyEq.neg

@[to_additive]
theorem EventuallyEq.div [Div β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
    (h' : f' =ᶠ[l] g') : (fun x => f x / f' x) =ᶠ[l] fun x => g x / g' x :=
  h.comp₂ (· / ·) h'
#align filter.eventually_eq.div Filter.EventuallyEq.div
#align filter.eventually_eq.sub Filter.EventuallyEq.sub

attribute [to_additive] EventuallyEq.const_smul
#align filter.eventually_eq.const_vadd Filter.EventuallyEq.const_vadd

@[to_additive]
theorem EventuallyEq.smul {𝕜} [SMul 𝕜 β] {l : Filter α} {f f' : α → 𝕜} {g g' : α → β}
    (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : (fun x => f x • g x) =ᶠ[l] fun x => f' x • g' x :=
  hf.comp₂ (· • ·) hg
#align filter.eventually_eq.smul Filter.EventuallyEq.smul
#align filter.eventually_eq.vadd Filter.EventuallyEq.vadd

theorem EventuallyEq.sup [Sup β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : (fun x => f x ⊔ g x) =ᶠ[l] fun x => f' x ⊔ g' x :=
  hf.comp₂ (· ⊔ ·) hg
#align filter.eventually_eq.sup Filter.EventuallyEq.sup

theorem EventuallyEq.inf [Inf β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : (fun x => f x ⊓ g x) =ᶠ[l] fun x => f' x ⊓ g' x :=
  hf.comp₂ (· ⊓ ·) hg
#align filter.eventually_eq.inf Filter.EventuallyEq.inf

theorem EventuallyEq.preimage {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (s : Set β) :
    f ⁻¹' s =ᶠ[l] g ⁻¹' s :=
  h.fun_comp s
#align filter.eventually_eq.preimage Filter.EventuallyEq.preimage

theorem EventuallyEq.inter {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∩ s' : Set α) =ᶠ[l] (t ∩ t' : Set α) :=
  h.comp₂ (· ∧ ·) h'
#align filter.eventually_eq.inter Filter.EventuallyEq.inter

theorem EventuallyEq.union {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∪ s' : Set α) =ᶠ[l] (t ∪ t' : Set α) :=
  h.comp₂ (· ∨ ·) h'
#align filter.eventually_eq.union Filter.EventuallyEq.union

theorem EventuallyEq.compl {s t : Set α} {l : Filter α} (h : s =ᶠ[l] t) :
    (sᶜ : Set α) =ᶠ[l] (tᶜ : Set α) :=
  h.fun_comp Not
#align filter.eventually_eq.compl Filter.EventuallyEq.compl

theorem EventuallyEq.diff {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s \ s' : Set α) =ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl
#align filter.eventually_eq.diff Filter.EventuallyEq.diff

theorem eventuallyEq_empty {s : Set α} {l : Filter α} : s =ᶠ[l] (∅ : Set α) ↔ ∀ᶠ x in l, x ∉ s :=
  eventuallyEq_set.trans <| by simp
#align filter.eventually_eq_empty Filter.eventuallyEq_empty

theorem inter_eventuallyEq_left {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] s ↔ ∀ᶠ x in l, x ∈ s → x ∈ t := by
  simp only [eventuallyEq_set, mem_inter_iff, and_iff_left_iff_imp]
#align filter.inter_eventually_eq_left Filter.inter_eventuallyEq_left

theorem inter_eventuallyEq_right {s t : Set α} {l : Filter α} :
    (s ∩ t : Set α) =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ t → x ∈ s := by
  rw [inter_comm, inter_eventuallyEq_left]
#align filter.inter_eventually_eq_right Filter.inter_eventuallyEq_right

@[simp]
theorem eventuallyEq_principal {s : Set α} {f g : α → β} : f =ᶠ[𝓟 s] g ↔ EqOn f g s :=
  Iff.rfl
#align filter.eventually_eq_principal Filter.eventuallyEq_principal

theorem eventuallyEq_inf_principal_iff {F : Filter α} {s : Set α} {f g : α → β} :
    f =ᶠ[F ⊓ 𝓟 s] g ↔ ∀ᶠ x in F, x ∈ s → f x = g x :=
  eventually_inf_principal
#align filter.eventually_eq_inf_principal_iff Filter.eventuallyEq_inf_principal_iff

theorem EventuallyEq.sub_eq [AddGroup β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    f - g =ᶠ[l] 0 := by simpa using ((EventuallyEq.refl l f).sub h).symm
#align filter.eventually_eq.sub_eq Filter.EventuallyEq.sub_eq

theorem eventuallyEq_iff_sub [AddGroup β] {f g : α → β} {l : Filter α} :
    f =ᶠ[l] g ↔ f - g =ᶠ[l] 0 :=
  ⟨fun h => h.sub_eq, fun h => by simpa using h.add (EventuallyEq.refl l g)⟩
#align filter.eventually_eq_iff_sub Filter.eventuallyEq_iff_sub

section LE

variable [LE β] {l : Filter α}

/-- A function `f` is eventually less than or equal to a function `g` at a filter `l`. -/
def EventuallyLE (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x ≤ g x
#align filter.eventually_le Filter.EventuallyLE

@[inherit_doc]
notation:50 f " ≤ᶠ[" l:50 "] " g:50 => EventuallyLE l f g

theorem EventuallyLE.congr {f f' g g' : α → β} (H : f ≤ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f' ≤ᶠ[l] g' :=
  H.mp <| hg.mp <| hf.mono fun x hf hg H => by rwa [hf, hg] at H
#align filter.eventually_le.congr Filter.EventuallyLE.congr

theorem eventuallyLE_congr {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    f ≤ᶠ[l] g ↔ f' ≤ᶠ[l] g' :=
  ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩
#align filter.eventually_le_congr Filter.eventuallyLE_congr

end LE

section Preorder

variable [Preorder β] {l : Filter α} {f g h : α → β}

theorem EventuallyEq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g :=
  h.mono fun _ => le_of_eq
#align filter.eventually_eq.le Filter.EventuallyEq.le

@[refl]
theorem EventuallyLE.refl (l : Filter α) (f : α → β) : f ≤ᶠ[l] f :=
  EventuallyEq.rfl.le
#align filter.eventually_le.refl Filter.EventuallyLE.refl

theorem EventuallyLE.rfl : f ≤ᶠ[l] f :=
  EventuallyLE.refl l f
#align filter.eventually_le.rfl Filter.EventuallyLE.rfl

@[trans]
theorem EventuallyLE.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₂.mp <| H₁.mono fun _ => le_trans
#align filter.eventually_le.trans Filter.EventuallyLE.trans

-- porting note (#10754): new instance
instance : Trans ((· ≤ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· ≤ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyLE.trans

@[trans]
theorem EventuallyEq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.le.trans H₂
#align filter.eventually_eq.trans_le Filter.EventuallyEq.trans_le

-- porting note (#10754): new instance
instance : Trans ((· =ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· ≤ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyEq.trans_le

@[trans]
theorem EventuallyLE.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.trans H₂.le
#align filter.eventually_le.trans_eq Filter.EventuallyLE.trans_eq

-- porting note (#10754): new instance
instance : Trans ((· ≤ᶠ[l] ·) : (α → β) → (α → β) → Prop) (· =ᶠ[l] ·) (· ≤ᶠ[l] ·) where
  trans := EventuallyLE.trans_eq

end Preorder

theorem EventuallyLE.antisymm [PartialOrder β] {l : Filter α} {f g : α → β} (h₁ : f ≤ᶠ[l] g)
    (h₂ : g ≤ᶠ[l] f) : f =ᶠ[l] g :=
  h₂.mp <| h₁.mono fun _ => le_antisymm
#align filter.eventually_le.antisymm Filter.EventuallyLE.antisymm

theorem eventuallyLE_antisymm_iff [PartialOrder β] {l : Filter α} {f g : α → β} :
    f =ᶠ[l] g ↔ f ≤ᶠ[l] g ∧ g ≤ᶠ[l] f := by
  simp only [EventuallyEq, EventuallyLE, le_antisymm_iff, eventually_and]
#align filter.eventually_le_antisymm_iff Filter.eventuallyLE_antisymm_iff

theorem EventuallyLE.le_iff_eq [PartialOrder β] {l : Filter α} {f g : α → β} (h : f ≤ᶠ[l] g) :
    g ≤ᶠ[l] f ↔ g =ᶠ[l] f :=
  ⟨fun h' => h'.antisymm h, EventuallyEq.le⟩
#align filter.eventually_le.le_iff_eq Filter.EventuallyLE.le_iff_eq

theorem Eventually.ne_of_lt [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ᶠ x in l, f x < g x) :
    ∀ᶠ x in l, f x ≠ g x :=
  h.mono fun _ hx => hx.ne
#align filter.eventually.ne_of_lt Filter.Eventually.ne_of_lt

theorem Eventually.ne_top_of_lt [PartialOrder β] [OrderTop β] {l : Filter α} {f g : α → β}
    (h : ∀ᶠ x in l, f x < g x) : ∀ᶠ x in l, f x ≠ ⊤ :=
  h.mono fun _ hx => hx.ne_top
#align filter.eventually.ne_top_of_lt Filter.Eventually.ne_top_of_lt

theorem Eventually.lt_top_of_ne [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β}
    (h : ∀ᶠ x in l, f x ≠ ⊤) : ∀ᶠ x in l, f x < ⊤ :=
  h.mono fun _ hx => hx.lt_top
#align filter.eventually.lt_top_of_ne Filter.Eventually.lt_top_of_ne

theorem Eventually.lt_top_iff_ne_top [PartialOrder β] [OrderTop β] {l : Filter α} {f : α → β} :
    (∀ᶠ x in l, f x < ⊤) ↔ ∀ᶠ x in l, f x ≠ ⊤ :=
  ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩
#align filter.eventually.lt_top_iff_ne_top Filter.Eventually.lt_top_iff_ne_top

@[mono]
theorem EventuallyLE.inter {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∩ s' : Set α) ≤ᶠ[l] (t ∩ t' : Set α) :=
  h'.mp <| h.mono fun _ => And.imp
#align filter.eventually_le.inter Filter.EventuallyLE.inter

@[mono]
theorem EventuallyLE.union {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∪ s' : Set α) ≤ᶠ[l] (t ∪ t' : Set α) :=
  h'.mp <| h.mono fun _ => Or.imp
#align filter.eventually_le.union Filter.EventuallyLE.union

protected lemma EventuallyLE.iUnion [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i ≤ᶠ[l] t i) : (⋃ i, s i) ≤ᶠ[l] ⋃ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' ↦
    let ⟨i, hi⟩ := mem_iUnion.1 hx'; mem_iUnion.2 ⟨i, hx i hi⟩

protected lemma EventuallyEq.iUnion [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i =ᶠ[l] t i) : (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.iUnion fun i ↦ (h i).le).antisymm <| .iUnion fun i ↦ (h i).symm.le

protected lemma EventuallyLE.iInter [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i ≤ᶠ[l] t i) : (⋂ i, s i) ≤ᶠ[l] ⋂ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' ↦ mem_iInter.2 fun i ↦ hx i (mem_iInter.1 hx' i)

protected lemma EventuallyEq.iInter [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i =ᶠ[l] t i) : (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.iInter fun i ↦ (h i).le).antisymm <| .iInter fun i ↦ (h i).symm.le

lemma _root_.Set.Finite.eventuallyLE_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋃ i ∈ s, f i) ≤ᶠ[l] (⋃ i ∈ s, g i) := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion, biUnion_eq_iUnion]
  exact .iUnion fun i ↦ hle i.1 i.2

alias EventuallyLE.biUnion := Set.Finite.eventuallyLE_iUnion

lemma _root_.Set.Finite.eventuallyEq_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋃ i ∈ s, f i) =ᶠ[l] (⋃ i ∈ s, g i) :=
  (EventuallyLE.biUnion hs fun i hi ↦ (heq i hi).le).antisymm <|
    .biUnion hs fun i hi ↦ (heq i hi).symm.le

alias EventuallyEq.biUnion := Set.Finite.eventuallyEq_iUnion

lemma _root_.Set.Finite.eventuallyLE_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋂ i ∈ s, f i) ≤ᶠ[l] (⋂ i ∈ s, g i) := by
  have := hs.to_subtype
  rw [biInter_eq_iInter, biInter_eq_iInter]
  exact .iInter fun i ↦ hle i.1 i.2

alias EventuallyLE.biInter := Set.Finite.eventuallyLE_iInter

lemma _root_.Set.Finite.eventuallyEq_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋂ i ∈ s, f i) =ᶠ[l] (⋂ i ∈ s, g i) :=
  (EventuallyLE.biInter hs fun i hi ↦ (heq i hi).le).antisymm <|
    .biInter hs fun i hi ↦ (heq i hi).symm.le

alias EventuallyEq.biInter := Set.Finite.eventuallyEq_iInter

lemma _root_.Finset.eventuallyLE_iUnion {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋃ i ∈ s, f i) ≤ᶠ[l] (⋃ i ∈ s, g i) :=
  .biUnion s.finite_toSet hle

lemma _root_.Finset.eventuallyEq_iUnion {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋃ i ∈ s, f i) =ᶠ[l] (⋃ i ∈ s, g i) :=
  .biUnion s.finite_toSet heq

lemma _root_.Finset.eventuallyLE_iInter {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋂ i ∈ s, f i) ≤ᶠ[l] (⋂ i ∈ s, g i) :=
  .biInter s.finite_toSet hle

lemma _root_.Finset.eventuallyEq_iInter {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋂ i ∈ s, f i) =ᶠ[l] (⋂ i ∈ s, g i) :=
  .biInter s.finite_toSet heq

@[mono]
theorem EventuallyLE.compl {s t : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) :
    (tᶜ : Set α) ≤ᶠ[l] (sᶜ : Set α) :=
  h.mono fun _ => mt
#align filter.eventually_le.compl Filter.EventuallyLE.compl

@[mono]
theorem EventuallyLE.diff {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : t' ≤ᶠ[l] s') :
    (s \ s' : Set α) ≤ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl
#align filter.eventually_le.diff Filter.EventuallyLE.diff

theorem set_eventuallyLE_iff_mem_inf_principal {s t : Set α} {l : Filter α} :
    s ≤ᶠ[l] t ↔ t ∈ l ⊓ 𝓟 s :=
  eventually_inf_principal.symm
#align filter.set_eventually_le_iff_mem_inf_principal Filter.set_eventuallyLE_iff_mem_inf_principal

theorem set_eventuallyLE_iff_inf_principal_le {s t : Set α} {l : Filter α} :
    s ≤ᶠ[l] t ↔ l ⊓ 𝓟 s ≤ l ⊓ 𝓟 t :=
  set_eventuallyLE_iff_mem_inf_principal.trans <| by
    simp only [le_inf_iff, inf_le_left, true_and_iff, le_principal_iff]
#align filter.set_eventually_le_iff_inf_principal_le Filter.set_eventuallyLE_iff_inf_principal_le

theorem set_eventuallyEq_iff_inf_principal {s t : Set α} {l : Filter α} :
    s =ᶠ[l] t ↔ l ⊓ 𝓟 s = l ⊓ 𝓟 t := by
  simp only [eventuallyLE_antisymm_iff, le_antisymm_iff, set_eventuallyLE_iff_inf_principal_le]
#align filter.set_eventually_eq_iff_inf_principal Filter.set_eventuallyEq_iff_inf_principal

theorem EventuallyLE.mul_le_mul [MulZeroClass β] [PartialOrder β] [PosMulMono β] [MulPosMono β]
    {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) (hg₀ : 0 ≤ᶠ[l] g₁)
    (hf₀ : 0 ≤ᶠ[l] f₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul
#align filter.eventually_le.mul_le_mul Filter.EventuallyLE.mul_le_mul

@[to_additive EventuallyLE.add_le_add]
theorem EventuallyLE.mul_le_mul' [Mul β] [Preorder β] [CovariantClass β β (· * ·) (· ≤ ·)]
    [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β}
    (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.mul_le_mul' hfx hgx
#align filter.eventually_le.mul_le_mul' Filter.EventuallyLE.mul_le_mul'
#align filter.eventually_le.add_le_add Filter.EventuallyLE.add_le_add

theorem EventuallyLE.mul_nonneg [OrderedSemiring β] {l : Filter α} {f g : α → β} (hf : 0 ≤ᶠ[l] f)
    (hg : 0 ≤ᶠ[l] g) : 0 ≤ᶠ[l] f * g := by filter_upwards [hf, hg] with x using _root_.mul_nonneg
#align filter.eventually_le.mul_nonneg Filter.EventuallyLE.mul_nonneg

theorem eventually_sub_nonneg [OrderedRing β] {l : Filter α} {f g : α → β} :
    0 ≤ᶠ[l] g - f ↔ f ≤ᶠ[l] g :=
  eventually_congr <| eventually_of_forall fun _ => sub_nonneg
#align filter.eventually_sub_nonneg Filter.eventually_sub_nonneg

theorem EventuallyLE.sup [SemilatticeSup β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂)
    (hg : g₁ ≤ᶠ[l] g₂) : f₁ ⊔ g₁ ≤ᶠ[l] f₂ ⊔ g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using sup_le_sup hfx hgx
#align filter.eventually_le.sup Filter.EventuallyLE.sup

theorem EventuallyLE.sup_le [SemilatticeSup β] {l : Filter α} {f g h : α → β} (hf : f ≤ᶠ[l] h)
    (hg : g ≤ᶠ[l] h) : f ⊔ g ≤ᶠ[l] h := by
  filter_upwards [hf, hg] with x hfx hgx using _root_.sup_le hfx hgx
#align filter.eventually_le.sup_le Filter.EventuallyLE.sup_le

theorem EventuallyLE.le_sup_of_le_left [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hf : h ≤ᶠ[l] f) : h ≤ᶠ[l] f ⊔ g :=
  hf.mono fun _ => _root_.le_sup_of_le_left
#align filter.eventually_le.le_sup_of_le_left Filter.EventuallyLE.le_sup_of_le_left

theorem EventuallyLE.le_sup_of_le_right [SemilatticeSup β] {l : Filter α} {f g h : α → β}
    (hg : h ≤ᶠ[l] g) : h ≤ᶠ[l] f ⊔ g :=
  hg.mono fun _ => _root_.le_sup_of_le_right
#align filter.eventually_le.le_sup_of_le_right Filter.EventuallyLE.le_sup_of_le_right

theorem join_le {f : Filter (Filter α)} {l : Filter α} (h : ∀ᶠ m in f, m ≤ l) : join f ≤ l :=
  fun _ hs => h.mono fun _ hm => hm hs
#align filter.join_le Filter.join_le

/-! ### Push-forwards, pull-backs, and the monad structure -/

section Map

/-- The forward map of a filter -/
def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs <| preimage_mono st
  inter_sets hs ht := inter_mem hs ht
#align filter.map Filter.map

@[simp]
theorem map_principal {s : Set α} {f : α → β} : map f (𝓟 s) = 𝓟 (Set.image f s) :=
  Filter.ext fun _ => image_subset_iff.symm
#align filter.map_principal Filter.map_principal

variable {f : Filter α} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

@[simp]
theorem eventually_map {P : β → Prop} : (∀ᶠ b in map m f, P b) ↔ ∀ᶠ a in f, P (m a) :=
  Iff.rfl
#align filter.eventually_map Filter.eventually_map

@[simp]
theorem frequently_map {P : β → Prop} : (∃ᶠ b in map m f, P b) ↔ ∃ᶠ a in f, P (m a) :=
  Iff.rfl
#align filter.frequently_map Filter.frequently_map

@[simp]
theorem mem_map : t ∈ map m f ↔ m ⁻¹' t ∈ f :=
  Iff.rfl
#align filter.mem_map Filter.mem_map

theorem mem_map' : t ∈ map m f ↔ { x | m x ∈ t } ∈ f :=
  Iff.rfl
#align filter.mem_map' Filter.mem_map'

theorem image_mem_map (hs : s ∈ f) : m '' s ∈ map m f :=
  f.sets_of_superset hs <| subset_preimage_image m s
#align filter.image_mem_map Filter.image_mem_map

-- The simpNF linter says that the LHS can be simplified via `Filter.mem_map`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem image_mem_map_iff (hf : Injective m) : m '' s ∈ map m f ↔ s ∈ f :=
  ⟨fun h => by rwa [← preimage_image_eq s hf], image_mem_map⟩
#align filter.image_mem_map_iff Filter.image_mem_map_iff

theorem range_mem_map : range m ∈ map m f := by
  rw [← image_univ]
  exact image_mem_map univ_mem
#align filter.range_mem_map Filter.range_mem_map

theorem mem_map_iff_exists_image : t ∈ map m f ↔ ∃ s ∈ f, m '' s ⊆ t :=
  ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨_, hs, ht⟩ =>
    mem_of_superset (image_mem_map hs) ht⟩
#align filter.mem_map_iff_exists_image Filter.mem_map_iff_exists_image

@[simp]
theorem map_id : Filter.map id f = f :=
  filter_eq <| rfl
#align filter.map_id Filter.map_id

@[simp]
theorem map_id' : Filter.map (fun x => x) f = f :=
  map_id
#align filter.map_id' Filter.map_id'

@[simp]
theorem map_compose : Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m) :=
  funext fun _ => filter_eq <| rfl
#align filter.map_compose Filter.map_compose

@[simp]
theorem map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f :=
  congr_fun Filter.map_compose f
#align filter.map_map Filter.map_map

/-- If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter. -/
theorem map_congr {m₁ m₂ : α → β} {f : Filter α} (h : m₁ =ᶠ[f] m₂) : map m₁ f = map m₂ f :=
  Filter.ext' fun _ => eventually_congr (h.mono fun _ hx => hx ▸ Iff.rfl)
#align filter.map_congr Filter.map_congr

end Map

section Comap

/-- The inverse map of a filter. A set `s` belongs to `Filter.comap m f` if either of the following
equivalent conditions hold.

1. There exists a set `t ∈ f` such that `m ⁻¹' t ⊆ s`. This is used as a definition.
2. The set `kernImage m s = {y | ∀ x, m x = y → x ∈ s}` belongs to `f`, see `Filter.mem_comap'`.
3. The set `(m '' sᶜ)ᶜ` belongs to `f`, see `Filter.mem_comap_iff_compl` and
`Filter.compl_mem_comap`. -/
def comap (m : α → β) (f : Filter β) : Filter α
    where
  sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets := ⟨univ, univ_mem, by simp only [subset_univ, preimage_univ]⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩
#align filter.comap Filter.comap

variable {f : α → β} {l : Filter β} {p : α → Prop} {s : Set α}

theorem mem_comap' : s ∈ comap f l ↔ { y | ∀ ⦃x⦄, f x = y → x ∈ s } ∈ l :=
  ⟨fun ⟨t, ht, hts⟩ => mem_of_superset ht fun y hy x hx => hts <| mem_preimage.2 <| by rwa [hx],
    fun h => ⟨_, h, fun x hx => hx rfl⟩⟩
#align filter.mem_comap' Filter.mem_comap'

-- TODO: it would be nice to use `kernImage` much more to take advantage of common name and API,
-- and then this would become `mem_comap'`
theorem mem_comap'' : s ∈ comap f l ↔ kernImage f s ∈ l :=
  mem_comap'

/-- RHS form is used, e.g., in the definition of `UniformSpace`. -/
lemma mem_comap_prod_mk {x : α} {s : Set β} {F : Filter (α × β)} :
    s ∈ comap (Prod.mk x) F ↔ {p : α × β | p.fst = x → p.snd ∈ s} ∈ F := by
  simp_rw [mem_comap', Prod.ext_iff, and_imp, @forall_swap β (_ = _), forall_eq, eq_comm]
#align filter.mem_comap_prod_mk Filter.mem_comap_prod_mk

@[simp]
theorem eventually_comap : (∀ᶠ a in comap f l, p a) ↔ ∀ᶠ b in l, ∀ a, f a = b → p a :=
  mem_comap'
#align filter.eventually_comap Filter.eventually_comap

@[simp]
theorem frequently_comap : (∃ᶠ a in comap f l, p a) ↔ ∃ᶠ b in l, ∃ a, f a = b ∧ p a := by
  simp only [Filter.Frequently, eventually_comap, not_exists, _root_.not_and]
#align filter.frequently_comap Filter.frequently_comap

theorem mem_comap_iff_compl : s ∈ comap f l ↔ (f '' sᶜ)ᶜ ∈ l := by
  simp only [mem_comap'', kernImage_eq_compl]
#align filter.mem_comap_iff_compl Filter.mem_comap_iff_compl

theorem compl_mem_comap : sᶜ ∈ comap f l ↔ (f '' s)ᶜ ∈ l := by rw [mem_comap_iff_compl, compl_compl]
#align filter.compl_mem_comap Filter.compl_mem_comap

end Comap

section KernMap

/-- The analog of `kernImage` for filters. A set `s` belongs to `Filter.kernMap m f` if either of
the following equivalent conditions hold.

1. There exists a set `t ∈ f` such that `s = kernImage m t`. This is used as a definition.
2. There exists a set `t` such that `tᶜ ∈ f` and `sᶜ = m '' t`, see `Filter.mem_kernMap_iff_compl`
and `Filter.compl_mem_kernMap`.

This definition because it gives a right adjoint to `Filter.comap`, and because it has a nice
interpretation when working with `co-` filters (`Filter.cocompact`, `Filter.cofinite`, ...).
For example, `kernMap m (cocompact α)` is the filter generated by the complements of the sets
`m '' K` where `K` is a compact subset of `α`. -/
def kernMap (m : α → β) (f : Filter α) : Filter β where
  sets := (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨s ∪ m ⁻¹' t, mem_of_superset hs (subset_union_left s _), ?_⟩
    rw [kernImage_union_preimage, union_eq_right.mpr hst]
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    exact ⟨s₁ ∩ s₂, f.inter_sets h₁ h₂, Set.preimage_kernImage.u_inf⟩

variable {m : α → β} {f : Filter α}

theorem mem_kernMap {s : Set β} : s ∈ kernMap m f ↔ ∃ t ∈ f, kernImage m t = s :=
  Iff.rfl

theorem mem_kernMap_iff_compl {s : Set β} : s ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = sᶜ := by
  rw [mem_kernMap, compl_surjective.exists]
  refine exists_congr (fun x ↦ and_congr_right fun _ ↦ ?_)
  rw [kernImage_compl, compl_eq_comm, eq_comm]

theorem compl_mem_kernMap {s : Set β} : sᶜ ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = s := by
  simp_rw [mem_kernMap_iff_compl, compl_compl]

end KernMap

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `Filter.seq` for the
applicative instance. -/
def bind (f : Filter α) (m : α → Filter β) : Filter β :=
  join (map m f)
#align filter.bind Filter.bind

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : Filter (α → β)) (g : Filter α) : Filter β where
  sets := { s | ∃ u ∈ f, ∃ t ∈ g, ∀ m ∈ u, ∀ x ∈ t, (m : α → β) x ∈ s }
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, fun _ _ _ _ => trivial⟩
  sets_of_superset := fun ⟨t₀, t₁, h₀, h₁, h⟩ hst =>
    ⟨t₀, t₁, h₀, h₁, fun _ hx _ hy => hst <| h _ hx _ hy⟩
  inter_sets := fun ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩ =>
    ⟨t₀ ∩ u₀, inter_mem ht₀ hu₀, t₁ ∩ u₁, inter_mem ht₁ hu₁, fun _ ⟨hx₀, hx₁⟩ _ ⟨hy₀, hy₁⟩ =>
      ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩
#align filter.seq Filter.seq

/-- `pure x` is the set of sets that contain `x`. It is equal to `𝓟 {x}` but
with this definition we have `s ∈ pure a` defeq `a ∈ s`. -/
instance : Pure Filter :=
  ⟨fun x =>
    { sets := { s | x ∈ s }
      inter_sets := And.intro
      sets_of_superset := fun hs hst => hst hs
      univ_sets := trivial }⟩

instance : Bind Filter :=
  ⟨@Filter.bind⟩

instance : Functor Filter where map := @Filter.map

instance : LawfulFunctor (Filter : Type u → Type u) where
  id_map _ := map_id
  comp_map _ _ _ := map_map.symm
  map_const := rfl

theorem pure_sets (a : α) : (pure a : Filter α).sets = { s | a ∈ s } :=
  rfl
#align filter.pure_sets Filter.pure_sets

@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Filter α) ↔ a ∈ s :=
  Iff.rfl
#align filter.mem_pure Filter.mem_pure

@[simp]
theorem eventually_pure {a : α} {p : α → Prop} : (∀ᶠ x in pure a, p x) ↔ p a :=
  Iff.rfl
#align filter.eventually_pure Filter.eventually_pure

@[simp]
theorem principal_singleton (a : α) : 𝓟 {a} = pure a :=
  Filter.ext fun s => by simp only [mem_pure, mem_principal, singleton_subset_iff]
#align filter.principal_singleton Filter.principal_singleton

@[simp]
theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
  rfl
#align filter.map_pure Filter.map_pure

@[simp] theorem join_pure (f : Filter α) : join (pure f) = f := rfl
#align filter.join_pure Filter.join_pure

@[simp]
theorem pure_bind (a : α) (m : α → Filter β) : bind (pure a) m = m a := by
  simp only [Bind.bind, bind, map_pure, join_pure]
#align filter.pure_bind Filter.pure_bind

/-!
### `Filter` as a `Monad`

In this section we define `Filter.monad`, a `Monad` structure on `Filter`s. This definition is not
an instance because its `Seq` projection is not equal to the `Filter.seq` function we use in the
`Applicative` instance on `Filter`.
-/

section

/-- The monad structure on filters. -/
protected def monad : Monad Filter where map := @Filter.map
#align filter.monad Filter.monad

attribute [local instance] Filter.monad

protected theorem lawfulMonad : LawfulMonad Filter where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl
#align filter.is_lawful_monad Filter.lawfulMonad

end

instance : Alternative Filter where
  seq := fun x y => x.seq (y ())
  failure := ⊥
  orElse x y := x ⊔ y ()

@[simp]
theorem map_def {α β} (m : α → β) (f : Filter α) : m <$> f = map m f :=
  rfl
#align filter.map_def Filter.map_def

@[simp]
theorem bind_def {α β} (f : Filter α) (m : α → Filter β) : f >>= m = bind f m :=
  rfl
#align filter.bind_def Filter.bind_def

/-! #### `map` and `comap` equations -/

section Map

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Filter β} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

@[simp] theorem mem_comap : s ∈ comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s := Iff.rfl
#align filter.mem_comap Filter.mem_comap

theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
  ⟨t, ht, Subset.rfl⟩
#align filter.preimage_mem_comap Filter.preimage_mem_comap

theorem Eventually.comap {p : β → Prop} (hf : ∀ᶠ b in g, p b) (f : α → β) :
    ∀ᶠ a in comap f g, p (f a) :=
  preimage_mem_comap hf
#align filter.eventually.comap Filter.Eventually.comap

theorem comap_id : comap id f = f :=
  le_antisymm (fun _ => preimage_mem_comap) fun _ ⟨_, ht, hst⟩ => mem_of_superset ht hst
#align filter.comap_id Filter.comap_id

theorem comap_id' : comap (fun x => x) f = f := comap_id
#align filter.comap_id' Filter.comap_id'

theorem comap_const_of_not_mem {x : β} (ht : t ∈ g) (hx : x ∉ t) : comap (fun _ : α => x) g = ⊥ :=
  empty_mem_iff_bot.1 <| mem_comap'.2 <| mem_of_superset ht fun _ hx' _ h => hx <| h.symm ▸ hx'
#align filter.comap_const_of_not_mem Filter.comap_const_of_not_mem

theorem comap_const_of_mem {x : β} (h : ∀ t ∈ g, x ∈ t) : comap (fun _ : α => x) g = ⊤ :=
  top_unique fun _ hs => univ_mem' fun _ => h _ (mem_comap'.1 hs) rfl
#align filter.comap_const_of_mem Filter.comap_const_of_mem

theorem map_const [NeBot f] {c : β} : (f.map fun _ => c) = pure c := by
  ext s
  by_cases h : c ∈ s <;> simp [h]
#align filter.map_const Filter.map_const

theorem comap_comap {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
  Filter.coext fun s => by simp only [compl_mem_comap, image_image, (· ∘ ·)]
#align filter.comap_comap Filter.comap_comap

section comm

/-!
The variables in the following lemmas are used as in this diagram:
```
    φ
  α → β
θ ↓   ↓ ψ
  γ → δ
    ρ
```
-/


variable {φ : α → β} {θ : α → γ} {ψ : β → δ} {ρ : γ → δ} (H : ψ ∘ φ = ρ ∘ θ)

theorem map_comm (F : Filter α) : map ψ (map φ F) = map ρ (map θ F) := by
  rw [Filter.map_map, H, ← Filter.map_map]
#align filter.map_comm Filter.map_comm

theorem comap_comm (G : Filter δ) : comap φ (comap ψ G) = comap θ (comap ρ G) := by
  rw [Filter.comap_comap, H, ← Filter.comap_comap]
#align filter.comap_comm Filter.comap_comm

end comm

theorem _root_.Function.Semiconj.filter_map {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) :=
  map_comm h.comp_eq
#align function.semiconj.filter_map Function.Semiconj.filter_map

theorem _root_.Function.Commute.filter_map {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.semiconj.filter_map
#align function.commute.filter_map Function.Commute.filter_map

theorem _root_.Function.Semiconj.filter_comap {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (comap f) (comap gb) (comap ga) :=
  comap_comm h.comp_eq.symm
#align function.semiconj.filter_comap Function.Semiconj.filter_comap

theorem _root_.Function.Commute.filter_comap {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (comap f) (comap g) :=
  h.semiconj.filter_comap
#align function.commute.filter_comap Function.Commute.filter_comap

@[simp]
theorem comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t) :=
  Filter.ext fun _ => ⟨fun ⟨_u, hu, b⟩ => (preimage_mono hu).trans b,
    fun h => ⟨t, Subset.rfl, h⟩⟩
#align filter.comap_principal Filter.comap_principal

@[simp]
theorem comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b}) := by
  rw [← principal_singleton, comap_principal]
#align filter.comap_pure Filter.comap_pure

theorem map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
  ⟨fun h _ ⟨_, ht, hts⟩ => mem_of_superset (h ht) hts, fun h _ ht => h ⟨_, ht, Subset.rfl⟩⟩
#align filter.map_le_iff_le_comap Filter.map_le_iff_le_comap

theorem gc_map_comap (m : α → β) : GaloisConnection (map m) (comap m) :=
  fun _ _ => map_le_iff_le_comap
#align filter.gc_map_comap Filter.gc_map_comap

theorem comap_le_iff_le_kernMap : comap m g ≤ f ↔ g ≤ kernMap m f := by
  simp [Filter.le_def, mem_comap'', mem_kernMap, -mem_comap]

theorem gc_comap_kernMap (m : α → β) : GaloisConnection (comap m) (kernMap m) :=
  fun _ _ ↦ comap_le_iff_le_kernMap

theorem kernMap_principal {s : Set α} : kernMap m (𝓟 s) = 𝓟 (kernImage m s) := by
  refine eq_of_forall_le_iff (fun g ↦ ?_)
  rw [← comap_le_iff_le_kernMap, le_principal_iff, le_principal_iff, mem_comap'']

@[mono]
theorem map_mono : Monotone (map m) :=
  (gc_map_comap m).monotone_l
#align filter.map_mono Filter.map_mono

@[mono]
theorem comap_mono : Monotone (comap m) :=
  (gc_map_comap m).monotone_u
#align filter.comap_mono Filter.comap_mono

/-- Temporary lemma that we can tag with `gcongr` -/
@[gcongr, deprecated] theorem map_le_map (h : F ≤ G) : map m F ≤ map m G := map_mono h

/-- Temporary lemma that we can tag with `gcongr` -/
@[gcongr, deprecated] theorem comap_le_comap (h : F ≤ G) : comap m F ≤ comap m G := comap_mono h

@[simp] theorem map_bot : map m ⊥ = ⊥ := (gc_map_comap m).l_bot
#align filter.map_bot Filter.map_bot

@[simp] theorem map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_comap m).l_sup
#align filter.map_sup Filter.map_sup

@[simp]
theorem map_iSup {f : ι → Filter α} : map m (⨆ i, f i) = ⨆ i, map m (f i) :=
  (gc_map_comap m).l_iSup
#align filter.map_supr Filter.map_iSup

@[simp]
theorem map_top (f : α → β) : map f ⊤ = 𝓟 (range f) := by
  rw [← principal_univ, map_principal, image_univ]
#align filter.map_top Filter.map_top

@[simp] theorem comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top
#align filter.comap_top Filter.comap_top

@[simp] theorem comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf
#align filter.comap_inf Filter.comap_inf

@[simp]
theorem comap_iInf {f : ι → Filter β} : comap m (⨅ i, f i) = ⨅ i, comap m (f i) :=
  (gc_map_comap m).u_iInf
#align filter.comap_infi Filter.comap_iInf

theorem le_comap_top (f : α → β) (l : Filter α) : l ≤ comap f ⊤ := by
  rw [comap_top]
  exact le_top
#align filter.le_comap_top Filter.le_comap_top

theorem map_comap_le : map m (comap m g) ≤ g :=
  (gc_map_comap m).l_u_le _
#align filter.map_comap_le Filter.map_comap_le

theorem le_comap_map : f ≤ comap m (map m f) :=
  (gc_map_comap m).le_u_l _
#align filter.le_comap_map Filter.le_comap_map

@[simp]
theorem comap_bot : comap m ⊥ = ⊥ :=
  bot_unique fun s _ => ⟨∅, mem_bot, by simp only [empty_subset, preimage_empty]⟩
#align filter.comap_bot Filter.comap_bot

theorem neBot_of_comap (h : (comap m g).NeBot) : g.NeBot := by
  rw [neBot_iff] at *
  contrapose! h
  rw [h]
  exact comap_bot
#align filter.ne_bot_of_comap Filter.neBot_of_comap

-- Porting note: the proof was `by simp`. Lean 4 fails to use `le_top`
theorem comap_inf_principal_range : comap m (g ⊓ 𝓟 (range m)) = comap m g := by
  simpa only [le_principal_iff, comap_inf, comap_principal, preimage_range, principal_univ,
    inf_eq_left] using le_top
#align filter.comap_inf_principal_range Filter.comap_inf_principal_range

theorem disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (comap m g₁) (comap m g₂) := by
  simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]
#align filter.disjoint_comap Filter.disjoint_comap

theorem comap_iSup {ι} {f : ι → Filter β} {m : α → β} : comap m (iSup f) = ⨆ i, comap m (f i) :=
  (gc_comap_kernMap m).l_iSup
#align filter.comap_supr Filter.comap_iSup

theorem comap_sSup {s : Set (Filter β)} {m : α → β} : comap m (sSup s) = ⨆ f ∈ s, comap m f := by
  simp only [sSup_eq_iSup, comap_iSup, eq_self_iff_true]
#align filter.comap_Sup Filter.comap_sSup

theorem comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ := by
  rw [sup_eq_iSup, comap_iSup, iSup_bool_eq, Bool.cond_true, Bool.cond_false]
#align filter.comap_sup Filter.comap_sup

theorem map_comap (f : Filter β) (m : α → β) : (f.comap m).map m = f ⊓ 𝓟 (range m) := by
  refine' le_antisymm (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) _
  rintro t' ⟨t, ht, sub⟩
  refine' mem_inf_principal.2 (mem_of_superset ht _)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt
#align filter.map_comap Filter.map_comap

theorem map_comap_setCoe_val (f : Filter β) (s : Set β) :
    (f.comap ((↑) : s → β)).map (↑) = f ⊓ 𝓟 s := by
  rw [map_comap, Subtype.range_val]

theorem map_comap_of_mem {f : Filter β} {m : α → β} (hf : range m ∈ f) : (f.comap m).map m = f := by
  rw [map_comap, inf_eq_left.2 (le_principal_iff.2 hf)]
#align filter.map_comap_of_mem Filter.map_comap_of_mem

instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Filter α) (Filter β) (map c) fun f => ∀ᶠ x : α in f, p x where
  prf f hf := ⟨comap c f, map_comap_of_mem <| hf.mono CanLift.prf⟩
#align filter.can_lift Filter.canLift

theorem comap_le_comap_iff {f g : Filter β} {m : α → β} (hf : range m ∈ f) :
    comap m f ≤ comap m g ↔ f ≤ g :=
  ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩
#align filter.comap_le_comap_iff Filter.comap_le_comap_iff

theorem map_comap_of_surjective {f : α → β} (hf : Surjective f) (l : Filter β) :
    map f (comap f l) = l :=
  map_comap_of_mem <| by simp only [hf.range_eq, univ_mem]
#align filter.map_comap_of_surjective Filter.map_comap_of_surjective

theorem comap_injective {f : α → β} (hf : Surjective f) : Injective (comap f) :=
  LeftInverse.injective <| map_comap_of_surjective hf

theorem _root_.Function.Surjective.filter_map_top {f : α → β} (hf : Surjective f) : map f ⊤ = ⊤ :=
  (congr_arg _ comap_top).symm.trans <| map_comap_of_surjective hf ⊤
#align function.surjective.filter_map_top Function.Surjective.filter_map_top

theorem subtype_coe_map_comap (s : Set α) (f : Filter α) :
    map ((↑) : s → α) (comap ((↑) : s → α) f) = f ⊓ 𝓟 s := by rw [map_comap, Subtype.range_coe]
#align filter.subtype_coe_map_comap Filter.subtype_coe_map_comap

theorem image_mem_of_mem_comap {f : Filter α} {c : β → α} (h : range c ∈ f) {W : Set β}
    (W_in : W ∈ comap c f) : c '' W ∈ f := by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in
#align filter.image_mem_of_mem_comap Filter.image_mem_of_mem_comap

theorem image_coe_mem_of_mem_comap {f : Filter α} {U : Set α} (h : U ∈ f) {W : Set U}
    (W_in : W ∈ comap ((↑) : U → α) f) : (↑) '' W ∈ f :=
  image_mem_of_mem_comap (by simp [h]) W_in
#align filter.image_coe_mem_of_mem_comap Filter.image_coe_mem_of_mem_comap

theorem comap_map {f : Filter α} {m : α → β} (h : Injective m) : comap m (map m f) = f :=
  le_antisymm
    (fun s hs =>
      mem_of_superset (preimage_mem_comap <| image_mem_map hs) <| by
        simp only [preimage_image_eq s h, Subset.rfl])
    le_comap_map
#align filter.comap_map Filter.comap_map

theorem mem_comap_iff {f : Filter β} {m : α → β} (inj : Injective m) (large : Set.range m ∈ f)
    {S : Set α} : S ∈ comap m f ↔ m '' S ∈ f := by
  rw [← image_mem_map_iff inj, map_comap_of_mem large]
#align filter.mem_comap_iff Filter.mem_comap_iff

theorem map_le_map_iff_of_injOn {l₁ l₂ : Filter α} {f : α → β} {s : Set α} (h₁ : s ∈ l₁)
    (h₂ : s ∈ l₂) (hinj : InjOn f s) : map f l₁ ≤ map f l₂ ↔ l₁ ≤ l₂ :=
  ⟨fun h _t ht =>
    mp_mem h₁ <|
      mem_of_superset (h <| image_mem_map (inter_mem h₂ ht)) fun _y ⟨_x, ⟨hxs, hxt⟩, hxy⟩ hys =>
        hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩
#align filter.map_le_map_iff_of_inj_on Filter.map_le_map_iff_of_injOn

theorem map_le_map_iff {f g : Filter α} {m : α → β} (hm : Injective m) :
    map m f ≤ map m g ↔ f ≤ g := by rw [map_le_iff_le_comap, comap_map hm]
#align filter.map_le_map_iff Filter.map_le_map_iff

theorem map_eq_map_iff_of_injOn {f g : Filter α} {m : α → β} {s : Set α} (hsf : s ∈ f) (hsg : s ∈ g)
    (hm : InjOn m s) : map m f = map m g ↔ f = g := by
  simp only [le_antisymm_iff, map_le_map_iff_of_injOn hsf hsg hm,
    map_le_map_iff_of_injOn hsg hsf hm]
#align filter.map_eq_map_iff_of_inj_on Filter.map_eq_map_iff_of_injOn

theorem map_inj {f g : Filter α} {m : α → β} (hm : Injective m) : map m f = map m g ↔ f = g :=
  map_eq_map_iff_of_injOn univ_mem univ_mem (hm.injOn _)
#align filter.map_inj Filter.map_inj

theorem map_injective {m : α → β} (hm : Injective m) : Injective (map m) := fun _ _ =>
  (map_inj hm).1
#align filter.map_injective Filter.map_injective

theorem comap_neBot_iff {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ ∀ t ∈ f, ∃ a, m a ∈ t := by
  simp only [← forall_mem_nonempty_iff_neBot, mem_comap, forall_exists_index, and_imp]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in Subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩
#align filter.comap_ne_bot_iff Filter.comap_neBot_iff

theorem comap_neBot {f : Filter β} {m : α → β} (hm : ∀ t ∈ f, ∃ a, m a ∈ t) : NeBot (comap m f) :=
  comap_neBot_iff.mpr hm
#align filter.comap_ne_bot Filter.comap_neBot

theorem comap_neBot_iff_frequently {f : Filter β} {m : α → β} :
    NeBot (comap m f) ↔ ∃ᶠ y in f, y ∈ range m := by
  simp only [comap_neBot_iff, frequently_iff, mem_range, @and_comm (_ ∈ _), exists_exists_eq_and]
#align filter.comap_ne_bot_iff_frequently Filter.comap_neBot_iff_frequently

theorem comap_neBot_iff_compl_range {f : Filter β} {m : α → β} :
    NeBot (comap m f) ↔ (range m)ᶜ ∉ f :=
  comap_neBot_iff_frequently
#align filter.comap_ne_bot_iff_compl_range Filter.comap_neBot_iff_compl_range

theorem comap_eq_bot_iff_compl_range {f : Filter β} {m : α → β} : comap m f = ⊥ ↔ (range m)ᶜ ∈ f :=
  not_iff_not.mp <| neBot_iff.symm.trans comap_neBot_iff_compl_range
#align filter.comap_eq_bot_iff_compl_range Filter.comap_eq_bot_iff_compl_range

theorem comap_surjective_eq_bot {f : Filter β} {m : α → β} (hm : Surjective m) :
    comap m f = ⊥ ↔ f = ⊥ := by
  rw [comap_eq_bot_iff_compl_range, hm.range_eq, compl_univ, empty_mem_iff_bot]
#align filter.comap_surjective_eq_bot Filter.comap_surjective_eq_bot

theorem disjoint_comap_iff (h : Surjective m) :
    Disjoint (comap m g₁) (comap m g₂) ↔ Disjoint g₁ g₂ := by
  rw [disjoint_iff, disjoint_iff, ← comap_inf, comap_surjective_eq_bot h]
#align filter.disjoint_comap_iff Filter.disjoint_comap_iff

theorem NeBot.comap_of_range_mem {f : Filter β} {m : α → β} (_ : NeBot f) (hm : range m ∈ f) :
    NeBot (comap m f) :=
  comap_neBot_iff_frequently.2 <| Eventually.frequently hm
#align filter.ne_bot.comap_of_range_mem Filter.NeBot.comap_of_range_mem

@[simp]
theorem comap_fst_neBot_iff {f : Filter α} :
    (f.comap (Prod.fst : α × β → α)).NeBot ↔ f.NeBot ∧ Nonempty β := by
  cases isEmpty_or_nonempty β
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp [*]
  · simp [comap_neBot_iff_frequently, *]
#align filter.comap_fst_ne_bot_iff Filter.comap_fst_neBot_iff

@[instance]
theorem comap_fst_neBot [Nonempty β] {f : Filter α} [NeBot f] :
    (f.comap (Prod.fst : α × β → α)).NeBot :=
  comap_fst_neBot_iff.2 ⟨‹_›, ‹_›⟩
#align filter.comap_fst_ne_bot Filter.comap_fst_neBot

@[simp]
theorem comap_snd_neBot_iff {f : Filter β} :
    (f.comap (Prod.snd : α × β → β)).NeBot ↔ Nonempty α ∧ f.NeBot := by
  cases' isEmpty_or_nonempty α with hα hα
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp
  · simp [comap_neBot_iff_frequently, hα]
#align filter.comap_snd_ne_bot_iff Filter.comap_snd_neBot_iff

@[instance]
theorem comap_snd_neBot [Nonempty α] {f : Filter β} [NeBot f] :
    (f.comap (Prod.snd : α × β → β)).NeBot :=
  comap_snd_neBot_iff.2 ⟨‹_›, ‹_›⟩
#align filter.comap_snd_ne_bot Filter.comap_snd_neBot

theorem comap_eval_neBot_iff' {ι : Type*} {α : ι → Type*} {i : ι} {f : Filter (α i)} :
    (comap (eval i) f).NeBot ↔ (∀ j, Nonempty (α j)) ∧ NeBot f := by
  cases' isEmpty_or_nonempty (∀ j, α j) with H H
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]
    simp [← Classical.nonempty_pi]
  · have : ∀ j, Nonempty (α j) := Classical.nonempty_pi.1 H
    simp [comap_neBot_iff_frequently, *]
#align filter.comap_eval_ne_bot_iff' Filter.comap_eval_neBot_iff'

@[simp]
theorem comap_eval_neBot_iff {ι : Type*} {α : ι → Type*} [∀ j, Nonempty (α j)] {i : ι}
    {f : Filter (α i)} : (comap (eval i) f).NeBot ↔ NeBot f := by simp [comap_eval_neBot_iff', *]
#align filter.comap_eval_ne_bot_iff Filter.comap_eval_neBot_iff

@[instance]
theorem comap_eval_neBot {ι : Type*} {α : ι → Type*} [∀ j, Nonempty (α j)] (i : ι)
    (f : Filter (α i)) [NeBot f] : (comap (eval i) f).NeBot :=
  comap_eval_neBot_iff.2 ‹_›
#align filter.comap_eval_ne_bot Filter.comap_eval_neBot

theorem comap_inf_principal_neBot_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f ⊓ 𝓟 s) := by
  refine' ⟨compl_compl s ▸ mt mem_of_eq_bot _⟩
  rintro ⟨t, ht, hts⟩
  rcases hf.nonempty_of_mem (inter_mem hs ht) with ⟨_, ⟨x, hxs, rfl⟩, hxt⟩
  exact absurd hxs (hts hxt)
#align filter.comap_inf_principal_ne_bot_of_image_mem Filter.comap_inf_principal_neBot_of_image_mem

theorem comap_coe_neBot_of_le_principal {s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l ≤ 𝓟 s) :
    NeBot (comap ((↑) : s → γ) l) :=
  h.comap_of_range_mem <| (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)
#align filter.comap_coe_ne_bot_of_le_principal Filter.comap_coe_neBot_of_le_principal

theorem NeBot.comap_of_surj {f : Filter β} {m : α → β} (hf : NeBot f) (hm : Surjective m) :
    NeBot (comap m f) :=
  hf.comap_of_range_mem <| univ_mem' hm
#align filter.ne_bot.comap_of_surj Filter.NeBot.comap_of_surj

theorem NeBot.comap_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f) :=
  hf.comap_of_range_mem <| mem_of_superset hs (image_subset_range _ _)
#align filter.ne_bot.comap_of_image_mem Filter.NeBot.comap_of_image_mem

@[simp]
theorem map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
  ⟨by
    rw [← empty_mem_iff_bot, ← empty_mem_iff_bot]
    exact id, fun h => by simp only [h, map_bot]⟩
#align filter.map_eq_bot_iff Filter.map_eq_bot_iff

theorem map_neBot_iff (f : α → β) {F : Filter α} : NeBot (map f F) ↔ NeBot F := by
  simp only [neBot_iff, Ne, map_eq_bot_iff]
#align filter.map_ne_bot_iff Filter.map_neBot_iff

theorem NeBot.map (hf : NeBot f) (m : α → β) : NeBot (map m f) :=
  (map_neBot_iff m).2 hf
#align filter.ne_bot.map Filter.NeBot.map

theorem NeBot.of_map : NeBot (f.map m) → NeBot f :=
  (map_neBot_iff m).1
#align filter.ne_bot.of_map Filter.NeBot.of_map

instance map_neBot [hf : NeBot f] : NeBot (f.map m) :=
  hf.map m
#align filter.map_ne_bot Filter.map_neBot

theorem sInter_comap_sets (f : α → β) (F : Filter β) : ⋂₀ (comap f F).sets = ⋂ U ∈ F, f ⁻¹' U := by
  ext x
  suffices (∀ (A : Set α) (B : Set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔
      ∀ B : Set β, B ∈ F → f x ∈ B by
    simp only [mem_sInter, mem_iInter, Filter.mem_sets, mem_comap, this, and_imp, exists_prop,
      mem_preimage, exists_imp]
  constructor
  · intro h U U_in
    simpa only [Subset.rfl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)
#align filter.sInter_comap_sets Filter.sInter_comap_sets

end Map

-- this is a generic rule for monotone functions:
theorem map_iInf_le {f : ι → Filter α} {m : α → β} : map m (iInf f) ≤ ⨅ i, map m (f i) :=
  le_iInf fun _ => map_mono <| iInf_le _ _
#align filter.map_infi_le Filter.map_iInf_le

theorem map_iInf_eq {f : ι → Filter α} {m : α → β} (hf : Directed (· ≥ ·) f) [Nonempty ι] :
    map m (iInf f) = ⨅ i, map m (f i) :=
  map_iInf_le.antisymm fun s (hs : m ⁻¹' s ∈ iInf f) =>
    let ⟨i, hi⟩ := (mem_iInf_of_directed hf _).1 hs
    have : ⨅ i, map m (f i) ≤ 𝓟 s :=
      iInf_le_of_le i <| by
        simp only [le_principal_iff, mem_map]
        assumption
    Filter.le_principal_iff.1 this
#align filter.map_infi_eq Filter.map_iInf_eq

theorem map_biInf_eq {ι : Type w} {f : ι → Filter α} {m : α → β} {p : ι → Prop}
    (h : DirectedOn (f ⁻¹'o (· ≥ ·)) { x | p x }) (ne : ∃ i, p i) :
    map m (⨅ (i) (_ : p i), f i) = ⨅ (i) (_ : p i), map m (f i) := by
  haveI := nonempty_subtype.2 ne
  simp only [iInf_subtype']
  exact map_iInf_eq h.directed_val
#align filter.map_binfi_eq Filter.map_biInf_eq

theorem map_inf_le {f g : Filter α} {m : α → β} : map m (f ⊓ g) ≤ map m f ⊓ map m g :=
  (@map_mono _ _ m).map_inf_le f g
#align filter.map_inf_le Filter.map_inf_le

theorem map_inf {f g : Filter α} {m : α → β} (h : Injective m) :
    map m (f ⊓ g) = map m f ⊓ map m g := by
  refine' map_inf_le.antisymm _
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ ∩ s₂⟩
  refine' mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) _
  rw [← image_inter h, image_subset_iff, ht]
#align filter.map_inf Filter.map_inf

theorem map_inf' {f g : Filter α} {m : α → β} {t : Set α} (htf : t ∈ f) (htg : t ∈ g)
    (h : InjOn m t) : map m (f ⊓ g) = map m f ⊓ map m g := by
  lift f to Filter t using htf; lift g to Filter t using htg
  replace h : Injective (m ∘ ((↑) : t → α)) := h.injective
  simp only [map_map, ← map_inf Subtype.coe_injective, map_inf h]
#align filter.map_inf' Filter.map_inf'

lemma disjoint_of_map {α β : Type*} {F G : Filter α} {f : α → β}
    (h : Disjoint (map f F) (map f G)) : Disjoint F G :=
  disjoint_iff.mpr <| map_eq_bot_iff.mp <| le_bot_iff.mp <| trans map_inf_le (disjoint_iff.mp h)

theorem disjoint_map {m : α → β} (hm : Injective m) {f₁ f₂ : Filter α} :
    Disjoint (map m f₁) (map m f₂) ↔ Disjoint f₁ f₂ := by
  simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]
#align filter.disjoint_map Filter.disjoint_map

theorem map_equiv_symm (e : α ≃ β) (f : Filter β) : map e.symm f = comap e f :=
  map_injective e.injective <| by
    rw [map_map, e.self_comp_symm, map_id, map_comap_of_surjective e.surjective]
#align filter.map_equiv_symm Filter.map_equiv_symm

theorem map_eq_comap_of_inverse {f : Filter α} {m : α → β} {n : β → α} (h₁ : m ∘ n = id)
    (h₂ : n ∘ m = id) : map m f = comap n f :=
  map_equiv_symm ⟨n, m, congr_fun h₁, congr_fun h₂⟩ f
#align filter.map_eq_comap_of_inverse Filter.map_eq_comap_of_inverse

theorem comap_equiv_symm (e : α ≃ β) (f : Filter α) : comap e.symm f = map e f :=
  (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm
#align filter.comap_equiv_symm Filter.comap_equiv_symm

theorem map_swap_eq_comap_swap {f : Filter (α × β)} : Prod.swap <$> f = comap Prod.swap f :=
  map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq
#align filter.map_swap_eq_comap_swap Filter.map_swap_eq_comap_swap

/-- A useful lemma when dealing with uniformities. -/
theorem map_swap4_eq_comap {f : Filter ((α × β) × γ × δ)} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f =
      comap (fun p : (α × γ) × β × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f :=
  map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)
#align filter.map_swap4_eq_comap Filter.map_swap4_eq_comap

theorem le_map {f : Filter α} {m : α → β} {g : Filter β} (h : ∀ s ∈ f, m '' s ∈ g) : g ≤ f.map m :=
  fun _ hs => mem_of_superset (h _ hs) <| image_preimage_subset _ _
#align filter.le_map Filter.le_map

theorem le_map_iff {f : Filter α} {m : α → β} {g : Filter β} : g ≤ f.map m ↔ ∀ s ∈ f, m '' s ∈ g :=
  ⟨fun h _ hs => h (image_mem_map hs), le_map⟩
#align filter.le_map_iff Filter.le_map_iff

protected theorem push_pull (f : α → β) (F : Filter α) (G : Filter β) :
    map f (F ⊓ comap f G) = map f F ⊓ G := by
  apply le_antisymm
  · calc
      map f (F ⊓ comap f G) ≤ map f F ⊓ (map f <| comap f G) := map_inf_le
      _ ≤ map f F ⊓ G := inf_le_inf_left (map f F) map_comap_le

  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc
      f '' V ∩ Z = f '' (V ∩ f ⁻¹' Z) := by rw [image_inter_preimage]
      _ ⊆ f '' (V ∩ W) := image_subset _ (inter_subset_inter_right _ ‹_›)
      _ = f '' (f ⁻¹' U) := by rw [h]
      _ ⊆ U := image_preimage_subset f U
#align filter.push_pull Filter.push_pull

protected theorem push_pull' (f : α → β) (F : Filter α) (G : Filter β) :
    map f (comap f G ⊓ F) = G ⊓ map f F := by simp only [Filter.push_pull, inf_comm]
#align filter.push_pull' Filter.push_pull'

theorem principal_eq_map_coe_top (s : Set α) : 𝓟 s = map ((↑) : s → α) ⊤ := by simp
#align filter.principal_eq_map_coe_top Filter.principal_eq_map_coe_top

theorem inf_principal_eq_bot_iff_comap {F : Filter α} {s : Set α} :
    F ⊓ 𝓟 s = ⊥ ↔ comap ((↑) : s → α) F = ⊥ := by
  rw [principal_eq_map_coe_top s, ← Filter.push_pull', inf_top_eq, map_eq_bot_iff]
#align filter.inf_principal_eq_bot_iff_comap Filter.inf_principal_eq_bot_iff_comap

section Applicative

theorem singleton_mem_pure {a : α} : {a} ∈ (pure a : Filter α) :=
  mem_singleton a
#align filter.singleton_mem_pure Filter.singleton_mem_pure

theorem pure_injective : Injective (pure : α → Filter α) := fun a _ hab =>
  (Filter.ext_iff.1 hab { x | a = x }).1 rfl
#align filter.pure_injective Filter.pure_injective

instance pure_neBot {α : Type u} {a : α} : NeBot (pure a) :=
  ⟨mt empty_mem_iff_bot.2 <| not_mem_empty a⟩
#align filter.pure_ne_bot Filter.pure_neBot

@[simp]
theorem le_pure_iff {f : Filter α} {a : α} : f ≤ pure a ↔ {a} ∈ f := by
  rw [← principal_singleton, le_principal_iff]
#align filter.le_pure_iff Filter.le_pure_iff

theorem mem_seq_def {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, ∀ x ∈ u, ∀ y ∈ t, (x : α → β) y ∈ s :=
  Iff.rfl
#align filter.mem_seq_def Filter.mem_seq_def

theorem mem_seq_iff {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, Set.seq u t ⊆ s := by
  simp only [mem_seq_def, seq_subset, exists_prop, iff_self_iff]
#align filter.mem_seq_iff Filter.mem_seq_iff

theorem mem_map_seq_iff {f : Filter α} {g : Filter β} {m : α → β → γ} {s : Set γ} :
    s ∈ (f.map m).seq g ↔ ∃ t u, t ∈ g ∧ u ∈ f ∧ ∀ x ∈ u, ∀ y ∈ t, m x y ∈ s :=
  Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun _ => hts _⟩)
    fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun _ ⟨_, has, Eq⟩ => Eq ▸ hts _ has⟩
#align filter.mem_map_seq_iff Filter.mem_map_seq_iff

theorem seq_mem_seq {f : Filter (α → β)} {g : Filter α} {s : Set (α → β)} {t : Set α} (hs : s ∈ f)
    (ht : t ∈ g) : s.seq t ∈ f.seq g :=
  ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩
#align filter.seq_mem_seq Filter.seq_mem_seq

theorem le_seq {f : Filter (α → β)} {g : Filter α} {h : Filter β}
    (hh : ∀ t ∈ f, ∀ u ∈ g, Set.seq t u ∈ h) : h ≤ seq f g := fun _ ⟨_, ht, _, hu, hs⟩ =>
  mem_of_superset (hh _ ht _ hu) fun _ ⟨_, hm, _, ha, eq⟩ => eq ▸ hs _ hm _ ha
#align filter.le_seq Filter.le_seq

@[mono]
theorem seq_mono {f₁ f₂ : Filter (α → β)} {g₁ g₂ : Filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.seq g₁ ≤ f₂.seq g₂ :=
  le_seq fun _ hs _ ht => seq_mem_seq (hf hs) (hg ht)
#align filter.seq_mono Filter.seq_mono

@[simp]
theorem pure_seq_eq_map (g : α → β) (f : Filter α) : seq (pure g) f = f.map g := by
  refine' le_antisymm (le_map fun s hs => _) (le_seq fun s hs t ht => _)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
  · refine' sets_of_superset (map g f) (image_mem_map ht) _
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩
#align filter.pure_seq_eq_map Filter.pure_seq_eq_map

@[simp]
theorem seq_pure (f : Filter (α → β)) (a : α) : seq f (pure a) = map (fun g : α → β => g a) f := by
  refine' le_antisymm (le_map fun s hs => _) (le_seq fun s hs t ht => _)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
  · refine' sets_of_superset (map (fun g : α → β => g a) f) (image_mem_map hs) _
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩
#align filter.seq_pure Filter.seq_pure

@[simp]
theorem seq_assoc (x : Filter α) (g : Filter (α → β)) (h : Filter (β → γ)) :
    seq h (seq g x) = seq (seq (map (· ∘ ·) h) g) x := by
  refine' le_antisymm (le_seq fun s hs t ht => _) (le_seq fun s hs t ht => _)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    refine' mem_of_superset _ (Set.seq_mono ((Set.seq_mono hu Subset.rfl).trans hs) Subset.rfl)
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    refine' mem_of_superset _ (Set.seq_mono Subset.rfl ht)
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv
#align filter.seq_assoc Filter.seq_assoc

theorem prod_map_seq_comm (f : Filter α) (g : Filter β) :
    (map Prod.mk f).seq g = seq (map (fun b a => (a, b)) g) f := by
  refine' le_antisymm (le_seq fun s hs t ht => _) (le_seq fun s hs t ht => _)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine' mem_of_superset _ (Set.seq_mono hs Subset.rfl)
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine' mem_of_superset _ (Set.seq_mono hs Subset.rfl)
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
#align filter.prod_map_seq_comm Filter.prod_map_seq_comm

theorem seq_eq_filter_seq {α β : Type u} (f : Filter (α → β)) (g : Filter α) :
    f <*> g = seq f g :=
  rfl
#align filter.seq_eq_filter_seq Filter.seq_eq_filter_seq

instance : LawfulApplicative (Filter : Type u → Type u) where
  map_pure := map_pure
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  seq_pure := seq_pure
  pure_seq := pure_seq_eq_map
  seq_assoc := seq_assoc

instance : CommApplicative (Filter : Type u → Type u) :=
  ⟨fun f g => prod_map_seq_comm f g⟩

end Applicative

/-! #### `bind` equations -/


section Bind

@[simp]
theorem eventually_bind {f : Filter α} {m : α → Filter β} {p : β → Prop} :
    (∀ᶠ y in bind f m, p y) ↔ ∀ᶠ x in f, ∀ᶠ y in m x, p y :=
  Iff.rfl
#align filter.eventually_bind Filter.eventually_bind

@[simp]
theorem eventuallyEq_bind {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ =ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ =ᶠ[m x] g₂ :=
  Iff.rfl
#align filter.eventually_eq_bind Filter.eventuallyEq_bind

@[simp]
theorem eventuallyLE_bind [LE γ] {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ ≤ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ ≤ᶠ[m x] g₂ :=
  Iff.rfl
#align filter.eventually_le_bind Filter.eventuallyLE_bind

theorem mem_bind' {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f :=
  Iff.rfl
#align filter.mem_bind' Filter.mem_bind'

@[simp]
theorem mem_bind {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x :=
  calc
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f := Iff.rfl
    _ ↔ ∃ t ∈ f, t ⊆ { a | s ∈ m a } := exists_mem_subset_iff.symm
    _ ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x := Iff.rfl
#align filter.mem_bind Filter.mem_bind

theorem bind_le {f : Filter α} {g : α → Filter β} {l : Filter β} (h : ∀ᶠ x in f, g x ≤ l) :
    f.bind g ≤ l :=
  join_le <| eventually_map.2 h
#align filter.bind_le Filter.bind_le

@[mono]
theorem bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α → Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ᶠ[f₁] g₂) :
    bind f₁ g₁ ≤ bind f₂ g₂ := by
  refine' le_trans (fun s hs => _) (join_mono <| map_mono hf)
  simp only [mem_join, mem_bind', mem_map] at hs ⊢
  filter_upwards [hg, hs] with _ hx hs using hx hs
#align filter.bind_mono Filter.bind_mono

theorem bind_inf_principal {f : Filter α} {g : α → Filter β} {s : Set β} :
    (f.bind fun x => g x ⊓ 𝓟 s) = f.bind g ⊓ 𝓟 s :=
  Filter.ext fun s => by simp only [mem_bind, mem_inf_principal]
#align filter.bind_inf_principal Filter.bind_inf_principal

theorem sup_bind {f g : Filter α} {h : α → Filter β} : bind (f ⊔ g) h = bind f h ⊔ bind g h := rfl
#align filter.sup_bind Filter.sup_bind

theorem principal_bind {s : Set α} {f : α → Filter β} : bind (𝓟 s) f = ⨆ x ∈ s, f x :=
  show join (map f (𝓟 s)) = ⨆ x ∈ s, f x by
    simp only [sSup_image, join_principal_eq_sSup, map_principal, eq_self_iff_true]
#align filter.principal_bind Filter.principal_bind

end Bind

/-! ### Limits -/

/-- `Filter.Tendsto` is the generic "limit of a function" predicate.
  `Tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂
#align filter.tendsto Filter.Tendsto

theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl
#align filter.tendsto_def Filter.tendsto_def

theorem tendsto_iff_eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ ⦃p : β → Prop⦄, (∀ᶠ y in l₂, p y) → ∀ᶠ x in l₁, p (f x) :=
  Iff.rfl
#align filter.tendsto_iff_eventually Filter.tendsto_iff_eventually

theorem tendsto_iff_forall_eventually_mem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, ∀ᶠ x in l₁, f x ∈ s :=
  Iff.rfl
#align filter.tendsto_iff_forall_eventually_mem Filter.tendsto_iff_forall_eventually_mem

lemma Tendsto.eventually_mem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β}
    (hf : Tendsto f l₁ l₂) (h : s ∈ l₂) : ∀ᶠ x in l₁, f x ∈ s :=
  hf h

theorem Tendsto.eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, p (f x) :=
  hf h
#align filter.tendsto.eventually Filter.Tendsto.eventually

theorem not_tendsto_iff_exists_frequently_nmem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    ¬Tendsto f l₁ l₂ ↔ ∃ s ∈ l₂, ∃ᶠ x in l₁, f x ∉ s := by
  simp only [tendsto_iff_forall_eventually_mem, not_forall, exists_prop, not_eventually]
#align filter.not_tendsto_iff_exists_frequently_nmem Filter.not_tendsto_iff_exists_frequently_nmem

theorem Tendsto.frequently {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∃ᶠ x in l₁, p (f x)) : ∃ᶠ y in l₂, p y :=
  mt hf.eventually h
#align filter.tendsto.frequently Filter.Tendsto.frequently

theorem Tendsto.frequently_map {l₁ : Filter α} {l₂ : Filter β} {p : α → Prop} {q : β → Prop}
    (f : α → β) (c : Filter.Tendsto f l₁ l₂) (w : ∀ x, p x → q (f x)) (h : ∃ᶠ x in l₁, p x) :
    ∃ᶠ y in l₂, q y :=
  c.frequently (h.mono w)
#align filter.tendsto.frequently_map Filter.Tendsto.frequently_map

@[simp]
theorem tendsto_bot {f : α → β} {l : Filter β} : Tendsto f ⊥ l := by simp [Tendsto]
#align filter.tendsto_bot Filter.tendsto_bot

@[simp] theorem tendsto_top {f : α → β} {l : Filter α} : Tendsto f l ⊤ := le_top
#align filter.tendsto_top Filter.tendsto_top

theorem le_map_of_right_inverse {mab : α → β} {mba : β → α} {f : Filter α} {g : Filter β}
    (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tendsto mba g f) : g ≤ map mab f := by
  rw [← @map_id _ g, ← map_congr h₁, ← map_map]
  exact map_mono h₂
#align filter.le_map_of_right_inverse Filter.le_map_of_right_inverse

theorem tendsto_of_isEmpty [IsEmpty α] {f : α → β} {la : Filter α} {lb : Filter β} :
    Tendsto f la lb := by simp only [filter_eq_bot_of_isEmpty la, tendsto_bot]
#align filter.tendsto_of_is_empty Filter.tendsto_of_isEmpty

theorem eventuallyEq_of_left_inv_of_right_inv {f : α → β} {g₁ g₂ : β → α} {fa : Filter α}
    {fb : Filter β} (hleft : ∀ᶠ x in fa, g₁ (f x) = x) (hright : ∀ᶠ y in fb, f (g₂ y) = y)
    (htendsto : Tendsto g₂ fb fa) : g₁ =ᶠ[fb] g₂ :=
  (htendsto.eventually hleft).mp <| hright.mono fun _ hr hl => (congr_arg g₁ hr.symm).trans hl
#align filter.eventually_eq_of_left_inv_of_right_inv Filter.eventuallyEq_of_left_inv_of_right_inv

theorem tendsto_iff_comap {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
  map_le_iff_le_comap
#align filter.tendsto_iff_comap Filter.tendsto_iff_comap

alias ⟨Tendsto.le_comap, _⟩ := tendsto_iff_comap
#align filter.tendsto.le_comap Filter.Tendsto.le_comap

protected theorem Tendsto.disjoint {f : α → β} {la₁ la₂ : Filter α} {lb₁ lb₂ : Filter β}
    (h₁ : Tendsto f la₁ lb₁) (hd : Disjoint lb₁ lb₂) (h₂ : Tendsto f la₂ lb₂) : Disjoint la₁ la₂ :=
  (disjoint_comap hd).mono h₁.le_comap h₂.le_comap
#align filter.tendsto.disjoint Filter.Tendsto.disjoint

theorem tendsto_congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ := by rw [Tendsto, Tendsto, map_congr hl]
#align filter.tendsto_congr' Filter.tendsto_congr'

theorem Tendsto.congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
    (h : Tendsto f₁ l₁ l₂) : Tendsto f₂ l₁ l₂ :=
  (tendsto_congr' hl).1 h
#align filter.tendsto.congr' Filter.Tendsto.congr'

theorem tendsto_congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ :=
  tendsto_congr' (univ_mem' h)
#align filter.tendsto_congr Filter.tendsto_congr

theorem Tendsto.congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂ :=
  (tendsto_congr h).1
#align filter.tendsto.congr Filter.Tendsto.congr

theorem tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x ≤ y :=
  Iff.rfl
#align filter.tendsto_id' Filter.tendsto_id'

theorem tendsto_id {x : Filter α} : Tendsto id x x :=
  le_refl x
#align filter.tendsto_id Filter.tendsto_id

theorem Tendsto.comp {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ}
    (hg : Tendsto g y z) (hf : Tendsto f x y) : Tendsto (g ∘ f) x z := fun _ hs => hf (hg hs)
#align filter.tendsto.comp Filter.Tendsto.comp

protected theorem Tendsto.iterate {f : α → α} {l : Filter α} (h : Tendsto f l l) :
    ∀ n, Tendsto (f^[n]) l l
  | 0 => tendsto_id
  | (n + 1) => (h.iterate n).comp h

theorem Tendsto.mono_left {f : α → β} {x y : Filter α} {z : Filter β} (hx : Tendsto f x z)
    (h : y ≤ x) : Tendsto f y z :=
  (map_mono h).trans hx
#align filter.tendsto.mono_left Filter.Tendsto.mono_left

theorem Tendsto.mono_right {f : α → β} {x : Filter α} {y z : Filter β} (hy : Tendsto f x y)
    (hz : y ≤ z) : Tendsto f x z :=
  le_trans hy hz
#align filter.tendsto.mono_right Filter.Tendsto.mono_right

theorem Tendsto.neBot {f : α → β} {x : Filter α} {y : Filter β} (h : Tendsto f x y) [hx : NeBot x] :
    NeBot y :=
  (hx.map _).mono h
#align filter.tendsto.ne_bot Filter.Tendsto.neBot

theorem tendsto_map {f : α → β} {x : Filter α} : Tendsto f x (map f x) :=
  le_refl (map f x)
#align filter.tendsto_map Filter.tendsto_map

@[simp]
theorem tendsto_map'_iff {f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ} :
    Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y := by
  rw [Tendsto, Tendsto, map_map]
#align filter.tendsto_map'_iff Filter.tendsto_map'_iff

alias ⟨_, tendsto_map'⟩ := tendsto_map'_iff
#align filter.tendsto_map' Filter.tendsto_map'

theorem tendsto_comap {f : α → β} {x : Filter β} : Tendsto f (comap f x) x :=
  map_comap_le
#align filter.tendsto_comap Filter.tendsto_comap

@[simp]
theorem tendsto_comap_iff {f : α → β} {g : β → γ} {a : Filter α} {c : Filter γ} :
    Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c :=
  ⟨fun h => tendsto_comap.comp h, fun h => map_le_iff_le_comap.mp <| by rwa [map_map]⟩
#align filter.tendsto_comap_iff Filter.tendsto_comap_iff

theorem tendsto_comap'_iff {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α} (h : range i ∈ f) :
    Tendsto (m ∘ i) (comap i f) g ↔ Tendsto m f g := by
  rw [Tendsto, ← map_compose]
  simp only [(· ∘ ·), map_comap_of_mem h, Tendsto]
#align filter.tendsto_comap'_iff Filter.tendsto_comap'_iff

theorem Tendsto.of_tendsto_comp {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ}
    (hfg : Tendsto (g ∘ f) a c) (hg : comap g c ≤ b) : Tendsto f a b := by
  rw [tendsto_iff_comap] at hfg ⊢
  calc
    a ≤ comap (g ∘ f) c := hfg
    _ ≤ comap f b := by simpa [comap_comap] using comap_mono hg
#align filter.tendsto.of_tendsto_comp Filter.Tendsto.of_tendsto_comp

theorem comap_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : ψ ∘ φ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : comap φ g = f := by
  refine' ((comap_mono <| map_le_iff_le_comap.1 hψ).trans _).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap, eq, comap_id]
#align filter.comap_eq_of_inverse Filter.comap_eq_of_inverse

theorem map_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : φ ∘ ψ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : map φ f = g := by
  refine' le_antisymm hφ (le_trans _ (map_mono hψ))
  rw [map_map, eq, map_id]
#align filter.map_eq_of_inverse Filter.map_eq_of_inverse

theorem tendsto_inf {f : α → β} {x : Filter α} {y₁ y₂ : Filter β} :
    Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂ := by
  simp only [Tendsto, le_inf_iff, iff_self_iff]
#align filter.tendsto_inf Filter.tendsto_inf

theorem tendsto_inf_left {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₁ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_left) h
#align filter.tendsto_inf_left Filter.tendsto_inf_left

theorem tendsto_inf_right {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₂ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_right) h
#align filter.tendsto_inf_right Filter.tendsto_inf_right

theorem Tendsto.inf {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β} (h₁ : Tendsto f x₁ y₁)
    (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
  tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩
#align filter.tendsto.inf Filter.Tendsto.inf

@[simp]
theorem tendsto_iInf {f : α → β} {x : Filter α} {y : ι → Filter β} :
    Tendsto f x (⨅ i, y i) ↔ ∀ i, Tendsto f x (y i) := by
  simp only [Tendsto, iff_self_iff, le_iInf_iff]
#align filter.tendsto_infi Filter.tendsto_iInf

theorem tendsto_iInf' {f : α → β} {x : ι → Filter α} {y : Filter β} (i : ι)
    (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y :=
  hi.mono_left <| iInf_le _ _
#align filter.tendsto_infi' Filter.tendsto_iInf'

theorem tendsto_iInf_iInf {f : α → β} {x : ι → Filter α} {y : ι → Filter β}
    (h : ∀ i, Tendsto f (x i) (y i)) : Tendsto f (iInf x) (iInf y) :=
  tendsto_iInf.2 fun i => tendsto_iInf' i (h i)
#align filter.tendsto_infi_infi Filter.tendsto_iInf_iInf

@[simp]
theorem tendsto_sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y := by
  simp only [Tendsto, map_sup, sup_le_iff]
#align filter.tendsto_sup Filter.tendsto_sup

theorem Tendsto.sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f x₁ y → Tendsto f x₂ y → Tendsto f (x₁ ⊔ x₂) y := fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩
#align filter.tendsto.sup Filter.Tendsto.sup

@[simp]
theorem tendsto_iSup {f : α → β} {x : ι → Filter α} {y : Filter β} :
    Tendsto f (⨆ i, x i) y ↔ ∀ i, Tendsto f (x i) y := by simp only [Tendsto, map_iSup, iSup_le_iff]
#align filter.tendsto_supr Filter.tendsto_iSup

theorem tendsto_iSup_iSup {f : α → β} {x : ι → Filter α} {y : ι → Filter β}
    (h : ∀ i, Tendsto f (x i) (y i)) : Tendsto f (iSup x) (iSup y) :=
  tendsto_iSup.2 fun i => (h i).mono_right <| le_iSup _ _
#align filter.tendsto_supr_supr Filter.tendsto_iSup_iSup

@[simp] theorem tendsto_principal {f : α → β} {l : Filter α} {s : Set β} :
    Tendsto f l (𝓟 s) ↔ ∀ᶠ a in l, f a ∈ s := by
  simp only [Tendsto, le_principal_iff, mem_map', Filter.Eventually]
#align filter.tendsto_principal Filter.tendsto_principal

-- Porting note: was a `simp` lemma
theorem tendsto_principal_principal {f : α → β} {s : Set α} {t : Set β} :
    Tendsto f (𝓟 s) (𝓟 t) ↔ ∀ a ∈ s, f a ∈ t := by
  simp only [tendsto_principal, eventually_principal]
#align filter.tendsto_principal_principal Filter.tendsto_principal_principal

@[simp] theorem tendsto_pure {f : α → β} {a : Filter α} {b : β} :
    Tendsto f a (pure b) ↔ ∀ᶠ x in a, f x = b := by
  simp only [Tendsto, le_pure_iff, mem_map', mem_singleton_iff, Filter.Eventually]
#align filter.tendsto_pure Filter.tendsto_pure

theorem tendsto_pure_pure (f : α → β) (a : α) : Tendsto f (pure a) (pure (f a)) :=
  tendsto_pure.2 rfl
#align filter.tendsto_pure_pure Filter.tendsto_pure_pure

theorem tendsto_const_pure {a : Filter α} {b : β} : Tendsto (fun _ => b) a (pure b) :=
  tendsto_pure.2 <| univ_mem' fun _ => rfl
#align filter.tendsto_const_pure Filter.tendsto_const_pure

theorem pure_le_iff {a : α} {l : Filter α} : pure a ≤ l ↔ ∀ s ∈ l, a ∈ s :=
  Iff.rfl
#align filter.pure_le_iff Filter.pure_le_iff

theorem tendsto_pure_left {f : α → β} {a : α} {l : Filter β} :
    Tendsto f (pure a) l ↔ ∀ s ∈ l, f a ∈ s :=
  Iff.rfl
#align filter.tendsto_pure_left Filter.tendsto_pure_left

@[simp]
theorem map_inf_principal_preimage {f : α → β} {s : Set β} {l : Filter α} :
    map f (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s :=
  Filter.ext fun t => by simp only [mem_map', mem_inf_principal, mem_setOf_eq, mem_preimage]
#align filter.map_inf_principal_preimage Filter.map_inf_principal_preimage

/-- If two filters are disjoint, then a function cannot tend to both of them along a non-trivial
filter. -/
theorem Tendsto.not_tendsto {f : α → β} {a : Filter α} {b₁ b₂ : Filter β} (hf : Tendsto f a b₁)
    [NeBot a] (hb : Disjoint b₁ b₂) : ¬Tendsto f a b₂ := fun hf' =>
  (tendsto_inf.2 ⟨hf, hf'⟩).neBot.ne hb.eq_bot
#align filter.tendsto.not_tendsto Filter.Tendsto.not_tendsto

protected theorem Tendsto.if {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {p : α → Prop}
    [∀ x, Decidable (p x)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 { x | p x }) l₂)
    (h₁ : Tendsto g (l₁ ⊓ 𝓟 { x | ¬p x }) l₂) :
    Tendsto (fun x => if p x then f x else g x) l₁ l₂ := by
  simp only [tendsto_def, mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs] with x hp₀ hp₁
  rw [mem_preimage]
  split_ifs with h
  exacts [hp₀ h, hp₁ h]
#align filter.tendsto.if Filter.Tendsto.if

protected theorem Tendsto.if' {α β : Type*} {l₁ : Filter α} {l₂ : Filter β} {f g : α → β}
    {p : α → Prop} [DecidablePred p] (hf : Tendsto f l₁ l₂) (hg : Tendsto g l₁ l₂) :
    Tendsto (fun a => if p a then f a else g a) l₁ l₂ :=
  (tendsto_inf_left hf).if (tendsto_inf_left hg)
#align filter.tendsto.if' Filter.Tendsto.if'

protected theorem Tendsto.piecewise {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {s : Set α}
    [∀ x, Decidable (x ∈ s)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 s) l₂) (h₁ : Tendsto g (l₁ ⊓ 𝓟 sᶜ) l₂) :
    Tendsto (piecewise s f g) l₁ l₂ :=
  Tendsto.if h₀ h₁
#align filter.tendsto.piecewise Filter.Tendsto.piecewise

end Filter

open Filter

theorem Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α → β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g :=
  h
#align set.eq_on.eventually_eq Set.EqOn.eventuallyEq

theorem Set.EqOn.eventuallyEq_of_mem {α β} {s : Set α} {l : Filter α} {f g : α → β} (h : EqOn f g s)
    (hl : s ∈ l) : f =ᶠ[l] g :=
  h.eventuallyEq.filter_mono <| Filter.le_principal_iff.2 hl
#align set.eq_on.eventually_eq_of_mem Set.EqOn.eventuallyEq_of_mem

theorem HasSubset.Subset.eventuallyLE {α} {l : Filter α} {s t : Set α} (h : s ⊆ t) : s ≤ᶠ[l] t :=
  Filter.eventually_of_forall h
#align has_subset.subset.eventually_le HasSubset.Subset.eventuallyLE

theorem Set.MapsTo.tendsto {α β} {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t) :
    Filter.Tendsto f (𝓟 s) (𝓟 t) :=
  Filter.tendsto_principal_principal.2 h
#align set.maps_to.tendsto Set.MapsTo.tendsto

theorem Filter.EventuallyEq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ}
    (hg : Tendsto g lc l) : f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.eventually H
#align filter.eventually_eq.comp_tendsto Filter.EventuallyEq.comp_tendsto

namespace Filter

/-- Construct a filter from a property that is stable under finite unions.
A set `s` belongs to `Filter.comk p _ _ _` iff its complement satisfies the predicate `p`.
This constructor is useful to define filters like `Filter.cofinite`. -/
def comk (p : Set α → Prop) (he : p ∅) (hmono : ∀ t, p t → ∀ s ⊆ t, p s)
    (hunion : ∀ s, p s → ∀ t, p t → p (s ∪ t)) : Filter α where
  sets := {t | p tᶜ}
  univ_sets := by simpa
  sets_of_superset := fun ht₁ ht => hmono _ ht₁ _ (compl_subset_compl.2 ht)
  inter_sets := fun ht₁ ht₂ => by simp [compl_inter, hunion _ ht₁ _ ht₂]

@[simp]
lemma mem_comk {p : Set α → Prop} {he hmono hunion s} :
    s ∈ comk p he hmono hunion ↔ p sᶜ :=
  .rfl

lemma compl_mem_comk {p : Set α → Prop} {he hmono hunion s} :
    sᶜ ∈ comk p he hmono hunion ↔ p s := by
  simp

end Filter
