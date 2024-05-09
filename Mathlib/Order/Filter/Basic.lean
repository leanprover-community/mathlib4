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
-- TODO: get rid of the special case
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

@[english_param const.Finset] def param_Finset : EnglishParam
-- TODO: get rid of the special case
| fvarid, _deps, type@(.app _ (.app (.const `Set _) X)), _used => do
  trace[English] "Using the english_param handler for Finset"
  addNoun' fvarid #[type]
    { kind := `Set
      article := .a
      text := nt!"finite set{.s} of sets in {X}"
      inlineText := nt!"finite set{.s} {fvarid} of sets in {X}" }
| fvarid, _deps, type@(.app _ X), _used => do
  trace[English] "Using the english_param handler for Finset"
  addNoun' fvarid #[type]
    { kind := `Finset
      article := .a
      text := nt!"finite set{.s} in {X}"
      inlineText := nt!"finite set{.s} {fvarid} in {X}" }
| _, _, _, _ => failure

@[english_param const.Set.Finite] def param_setFinite : EnglishParam
| fvarid, deps, type@(mkAppN _ #[_, .fvar fvaridE]), false => do
  let e ← getEntityFor fvaridE deps
  addEntity <| e.pushAdjective fvarid
    { kind := `Set.Finite,
      expr := type,
      article := .a,
      text := "finite" }
| _, _, _, _ => failure

@[english_param const.Finite] def param_Finite : EnglishParam
| fvarid, deps, type@(mkAppN _ #[.fvar fvaridE]), false => do
  let e ← getEntityFor fvaridE deps
  addEntity <| e.pushAdjective fvarid
    { kind := `Finite,
      expr := type,
      article := .a,
      text := "finite" }
| _, _, _, _ => failure

@[english_param const.Monotone] def param_Monotone : EnglishParam
| fvarid, deps, type@(mkAppN _ #[_, _, _, _, .fvar fvaridE]), false => do
  let e ← getEntityFor fvaridE deps
  addEntity <| e.pushAdjective fvarid
    { kind := `Monotone,
      expr := type,
      article := .a,
      text := "monotone" }
| _, _, _, _ => failure

@[english_param const.Antitone] def param_Antitone : EnglishParam
| fvarid, deps, type@(mkAppN _ #[_, _, _, _, .fvar fvaridE]), false => do
  let e ← getEntityFor fvaridE deps
  addEntity <| e.pushAdjective fvarid
    { kind := `Antitone,
      expr := type,
      article := .a,
      text := "antitone" }
| _, _, _, _ => failure

@[english_param const.Membership] def param_Membership : EnglishParam
| fvarid, _deps, type@(mkAppN _ #[X, Y]), _used => do
  addNoun' fvarid #[type]
    { kind := `Membership
      article := .a
      text := nt!"the membership relation{.s} between {X} and {Y}"
      inlineText := nt!"the membership relation{.s} {fvarid} between {X} and {Y}" }
| _, _, _, _ => failure

latex_pp_app_rules (const := Membership.mk)
  | _, #[α, β, mem] => do
    withBindingBodyUnusedName' mem `x fun x b => do
    withBindingBodyUnusedName' b `y fun y z => do
      let pz ← latexPP z
      return LatexData.atomString s!"{x.toLatex} \\in {y.toLatex} \\text\{ if }" ++ pz

@[english_param const.Membership.mk] def param_Membership_mk : EnglishParam
| fvarid, _deps, type@(mkAppN _ #[X, Y, mem]), _used => do
  addNoun' fvarid #[type]
    { kind := `Set
      article := .a
      text := nt!"toto {X} and {Y}"
      inlineText := nt!"toto {fvarid} between {X} and {Y}" }
| _, _, _, _ => failure
variable (f : Nat → Nat)

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

open Lean in
latex_pp_app_rules (const := setOf)
  | _, #[X, p] => do
    let X ← latexPP X
    let some v ← p.getBinderName | throwError "This shouldn't happen"
    let b ← Lean.Meta.lambdaTelescope p (λ _ => latexPP)
    (LatexData.atomString $ "\\left\\{" ++ v.toLatex ++ " \\mid " ++ b.latex.1 ++ "\\right\\}").maybeWithTooltip s!"inside \\({X.latex.1}\\)"

latex_pp_app_rules (const := Set.sInter)
  | _, #[_α, s] => do
    withBindingBodyUnusedName' s `i fun name _ => do
      let ps ← latexPP s
      let pinter := (← (LatexData.atomString "\\bigcap" |>.bigger 1).sub
        (s!"{name.toLatex} \\in " ++ ps) |>.maybeWithTooltip "Set.sInter") ++
        name.toLatex
      return pinter |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 65)

latex_pp_app_rules (const := Set.iInter)
  | _, #[_α, ι, s] => do
    let i ← withExtraSmallness 2 <| latexPP ι
    withBindingBodyUnusedName' s `i fun name body => do
      match body with -- Detect bounded intersections
      | (mkAppN (.const `Set.iInter _) #[_α, h, s']) => 
        withBindingBodyUnusedName' s' `i fun _name body => do
          let cond ← withExtraSmallness 2 <| latexPP h
          let pbody ← latexPP body
          let pbody := pbody.protectLeft 66
          let pinter := (← (LatexData.atomString "\\bigcap" |>.bigger 1).sub
            cond |>.maybeWithTooltip "Set.iInter") ++ pbody
          return pinter |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 65)
      | _ =>
      let pbody ← latexPP body
      let pbody := pbody.protectLeft 66
      let pinter := (← (LatexData.atomString "\\bigcap" |>.bigger 1).sub
        (s!"{name.toLatex} : " ++ i) |>.maybeWithTooltip "Set.iInter") ++ pbody
      return pinter |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 65)

latex_pp_app_rules (const := EmptyCollection.emptyCollection)
  | _, #[X, _] => do
      let X ← latexPP X
      (LatexData.atomString "\\varnothing").maybeWithTooltip s!"in \\({X.latex.1}\\)"

latex_pp_app_rules (const := HasCompl.compl)
  | _, #[_, _, A] => do
    let A ← latexPP A
    return A.sup (LatexData.atomString "c")

latex_pp_app_rules (const := Singleton.singleton)
  | _, #[_, X, _, A] => do
    let X ← latexPP X
    let A ← latexPP A
    LatexData.atomString "\\{" ++ A ++ "\\}" |>.maybeWithTooltip s!"in \\({X.latex.1}\\)"

@[latex_pp_app const.SDiff.sdiff] def pp_sdiff := basicBinOpPrinter " \\setminus " 70 .none 4

latex_pp_app_rules (const := Prod.fst)
  | _, #[_, _, p] => do
    let p ← latexPP p
    return LatexData.atomString <| "{" ++ p.latex.1 ++ "}_1"

latex_pp_app_rules (const := Prod.snd)
  | _, #[_, _, p] => do
    let p ← latexPP p
    return LatexData.atomString <| "{" ++ p.latex.1 ++ "}_2"

latex_pp_app_rules (const := Monotone)
  | _, #[_, _, _, _, f] => do
    let A ← latexPP f
    return A ++ (LatexData.atomString "\\text{ is monotone}")

latex_pp_app_rules (const := Antitone)
  | _, #[_, _, _, _, f] => do
    let A ← latexPP f
    return A ++ (LatexData.atomString "\\text{ is antitone}")

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


latex_pp_app_rules (const := Filter.principal)
  | _, #[_, s] => do
    let s ← latexPP s
    LatexData.atomString "\\mathcal{P}(" ++ s ++ ")" |>.maybeWithTooltip
      "Principal filter"

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

latex_pp_app_rules (const := Filter.join)
  | _, #[_, s] => do
    let s ← latexPP s
    LatexData.atomString "\\mathcal{FJ}(" ++ s ++ ")" |>.maybeWithTooltip
      "Filter join"

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

latex_pp_app_rules (const := Filter.generate)
  | _, #[_, s] => do
    let s ← latexPP s
    LatexData.atomString "\\langle " ++ s ++ "\\rangle" |>.maybeWithTooltip
      "Generated filter"

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
