/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Basic

#align_import combinatorics.hales_jewett from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# The Hales-Jewett theorem

We prove the Hales-Jewett theorem and deduce Van der Waerden's theorem as a corollary.

The Hales-Jewett theorem is a result in Ramsey theory dealing with *combinatorial lines*. Given
an 'alphabet' `α : Type*` and `a b : α`, an example of a combinatorial line in `α^5` is
`{ (a, x, x, b, x) | x : α }`. See `Combinatorics.Line` for a precise general definition. The
Hales-Jewett theorem states that for any fixed finite types `α` and `κ`, there exists a (potentially
huge) finite type `ι` such that whenever `ι → α` is `κ`-colored (i.e. for any coloring
`C : (ι → α) → κ`), there exists a monochromatic line. We prove the Hales-Jewett theorem using
the idea of *color focusing* and a *product argument*. See the proof of
`Combinatorics.Line.exists_mono_in_high_dimension'` for details.

The version of Van der Waerden's theorem in this file states that whenever a commutative monoid `M`
is finitely colored and `S` is a finite subset, there exists a monochromatic homothetic copy of `S`.
This follows from the Hales-Jewett theorem by considering the map `(ι → S) → M` sending `v`
to `∑ i : ι, v i`, which sends a combinatorial line to a homothetic copy of `S`.

## Main results

- `Combinatorics.Line.exists_mono_in_high_dimension`: the Hales-Jewett theorem.
- `Combinatorics.exists_mono_homothetic_copy`: a generalization of Van der Waerden's theorem.

## Implementation details

For convenience, we work directly with finite types instead of natural numbers. That is, we write
`α, ι, κ` for (finite) types where one might traditionally use natural numbers `n, H, c`. This
allows us to work directly with `α`, `Option α`, `(ι → α) → κ`, and `ι ⊕ ι'` instead of `Fin n`,
`Fin (n+1)`, `Fin (c^(n^H))`, and `Fin (H + H')`.

## Todo

- Prove a finitary version of Van der Waerden's theorem (either by compactness or by modifying the
current proof).

- One could reformulate the proof of Hales-Jewett to give explicit upper bounds on the number of
coordinates needed.

## Tags

combinatorial line, Ramsey theory, arithmetic progression

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

-/


open Classical

open BigOperators

universe u v

namespace Combinatorics

/-- The type of combinatorial lines. A line `l : Line α ι` in the hypercube `ι → α` defines a
function `α → ι → α` from `α` to the hypercube, such that for each coordinate `i : ι`, the function
`fun x ↦ l x i` is either `id` or constant. We require lines to be nontrivial in the sense that
`fun x ↦ l x i` is `id` for at least one `i`.

Formally, a line is represented by a word `l.idxFun : ι → Option α` which says whether
`fun x ↦ l x i` is `id` (corresponding to `l.idxFun i = none`) or constantly `y` (corresponding to
`l.idxFun i = some y`).

When `α` has size `1` there can be many elements of `Line α ι` defining the same function. -/
structure Line (α ι : Type*) where
  /-- The word representing a combinatorial line. `l.idxfun i = none` means that
  `l x i = x` for all `x` and `l.idxfun i = some y` means that `l x i = y`. -/
  idxFun : ι → Option α
  /-- We require combinatorial lines to be nontrivial in the sense that `fun x ↦ l x i` is `id` for
  at least one coordinate `i`. -/
  proper : ∃ i, idxFun i = none
#align combinatorics.line Combinatorics.Line

namespace Line

-- This lets us treat a line `l : Line α ι` as a function `α → ι → α`.
instance (α ι) : CoeFun (Line α ι) fun _ => α → ι → α :=
  ⟨fun l x i => (l.idxFun i).getD x⟩

/-- A line is monochromatic if all its points are the same color. -/
def IsMono {α ι κ} (C : (ι → α) → κ) (l : Line α ι) : Prop :=
  ∃ c, ∀ x, C (l x) = c
#align combinatorics.line.is_mono Combinatorics.Line.IsMono

/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal (α ι) [Nonempty ι] : Line α ι where
  idxFun _ := none
  proper := ⟨Classical.arbitrary ι, rfl⟩
#align combinatorics.line.diagonal Combinatorics.Line.diagonal

instance (α ι) [Nonempty ι] : Inhabited (Line α ι) :=
  ⟨diagonal α ι⟩

/-- The type of lines that are only one color except possibly at their endpoints. -/
structure AlmostMono {α ι κ : Type*} (C : (ι → Option α) → κ) where
  /-- The underlying line of an almost monochromatic line, where the coordinate dimension `α` is
  extended by an additional symbol `none`, thought to be marking the endpoint of the line. -/
  line : Line (Option α) ι
  /-- The main color of an almost monochromatic line. -/
  color : κ
  /-- The proposition that the underlying line of an almost monochromatic line assumes its main
  color except possibly at the endpoints. -/
  has_color : ∀ x : α, C (line (some x)) = color
#align combinatorics.line.almost_mono Combinatorics.Line.AlmostMono

instance {α ι κ : Type*} [Nonempty ι] [Inhabited κ] :
    Inhabited (AlmostMono fun _ : ι → Option α => (default : κ)) :=
  ⟨{  line := default
      color := default
      has_color := fun _ ↦ rfl}⟩

/-- The type of collections of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.
Used in the proof `exists_mono_in_high_dimension`. -/
structure ColorFocused {α ι κ : Type*} (C : (ι → Option α) → κ) where
  /-- The underlying multiset of almost monochromatic lines of a color-focused collection. -/
  lines : Multiset (AlmostMono C)
  /-- The common endpoint of the lines in the color-focused collection. -/
  focus : ι → Option α
  /-- The proposition that all lines in a color-focused collection have the same endpoint. -/
  is_focused : ∀ p ∈ lines, p.line none = focus
  /-- The proposition that all lines in a color-focused collection of lines have distinct colors. -/
  distinct_colors : (lines.map AlmostMono.color).Nodup
#align combinatorics.line.color_focused Combinatorics.Line.ColorFocused

instance {α ι κ} (C : (ι → Option α) → κ) : Inhabited (ColorFocused C) := by
  refine' ⟨⟨0, fun _ => none, fun h => _, Multiset.nodup_zero⟩⟩
  -- ⊢ h ∈ 0 → (fun x i => Option.getD (idxFun h.line i) x) none = fun x => none
  simp only [Multiset.not_mem_zero, IsEmpty.forall_iff]
  -- 🎉 no goals

/-- A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`,
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
def map {α α' ι} (f : α → α') (l : Line α ι) : Line α' ι where
  idxFun i := (l.idxFun i).map f
  proper := ⟨l.proper.choose, by simp only [l.proper.choose_spec, Option.map_none']⟩
                                 -- 🎉 no goals
#align combinatorics.line.map Combinatorics.Line.map

/-- A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def vertical {α ι ι'} (v : ι → α) (l : Line α ι') : Line α (Sum ι ι') where
  idxFun := Sum.elim (some ∘ v) l.idxFun
  proper := ⟨Sum.inr l.proper.choose, l.proper.choose_spec⟩
#align combinatorics.line.vertical Combinatorics.Line.vertical

/-- A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def horizontal {α ι ι'} (l : Line α ι) (v : ι' → α) : Line α (Sum ι ι') where
  idxFun := Sum.elim l.idxFun (some ∘ v)
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩
#align combinatorics.line.horizontal Combinatorics.Line.horizontal

/-- One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α`. -/
def prod {α ι ι'} (l : Line α ι) (l' : Line α ι') : Line α (Sum ι ι') where
  idxFun := Sum.elim l.idxFun l'.idxFun
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩
#align combinatorics.line.prod Combinatorics.Line.prod

theorem apply {α ι} (l : Line α ι) (x : α) : l x = fun i => (l.idxFun i).getD x :=
  rfl
#align combinatorics.line.apply Combinatorics.Line.apply

theorem apply_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i = none) : l x i = x := by
  simp only [Option.getD_none, h, l.apply]
  -- 🎉 no goals
#align combinatorics.line.apply_none Combinatorics.Line.apply_none

theorem apply_of_ne_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i ≠ none) :
    some (l x i) = l.idxFun i := by rw [l.apply, Option.getD_of_ne_none h]
                                    -- 🎉 no goals
#align combinatorics.line.apply_of_ne_none Combinatorics.Line.apply_of_ne_none

@[simp]
theorem map_apply {α α' ι} (f : α → α') (l : Line α ι) (x : α) : l.map f (f x) = f ∘ l x := by
  simp only [Line.apply, Line.map, Option.getD_map]
  -- ⊢ (fun i => f (Option.getD (idxFun l i) x)) = f ∘ fun i => Option.getD (idxFun …
  rfl
  -- 🎉 no goals
#align combinatorics.line.map_apply Combinatorics.Line.map_apply

@[simp]
theorem vertical_apply {α ι ι'} (v : ι → α) (l : Line α ι') (x : α) :
    l.vertical v x = Sum.elim v (l x) := by
  funext i
  -- ⊢ (fun x i => Option.getD (idxFun (vertical v l) i) x) x i = Sum.elim v ((fun  …
  cases i <;> rfl
  -- ⊢ (fun x i => Option.getD (idxFun (vertical v l) i) x) x (Sum.inl val✝) = Sum. …
              -- 🎉 no goals
              -- 🎉 no goals
#align combinatorics.line.vertical_apply Combinatorics.Line.vertical_apply

@[simp]
theorem horizontal_apply {α ι ι'} (l : Line α ι) (v : ι' → α) (x : α) :
    l.horizontal v x = Sum.elim (l x) v := by
  funext i
  -- ⊢ (fun x i => Option.getD (idxFun (horizontal l v) i) x) x i = Sum.elim ((fun  …
  cases i <;> rfl
  -- ⊢ (fun x i => Option.getD (idxFun (horizontal l v) i) x) x (Sum.inl val✝) = Su …
              -- 🎉 no goals
              -- 🎉 no goals
#align combinatorics.line.horizontal_apply Combinatorics.Line.horizontal_apply

@[simp]
theorem prod_apply {α ι ι'} (l : Line α ι) (l' : Line α ι') (x : α) :
    l.prod l' x = Sum.elim (l x) (l' x) := by
  funext i
  -- ⊢ (fun x i => Option.getD (idxFun (prod l l') i) x) x i = Sum.elim ((fun x i = …
  cases i <;> rfl
  -- ⊢ (fun x i => Option.getD (idxFun (prod l l') i) x) x (Sum.inl val✝) = Sum.eli …
              -- 🎉 no goals
              -- 🎉 no goals
#align combinatorics.line.prod_apply Combinatorics.Line.prod_apply

@[simp]
theorem diagonal_apply {α ι} [Nonempty ι] (x : α) : Line.diagonal α ι x = fun _ => x := by
  simp_rw [Line.diagonal, Option.getD_none]
  -- 🎉 no goals
#align combinatorics.line.diagonal_apply Combinatorics.Line.diagonal_apply

/-- The Hales-Jewett theorem. This version has a restriction on universe levels which is necessary
for the proof. See `exists_mono_in_high_dimension` for a fully universe-polymorphic version. -/
private theorem exists_mono_in_high_dimension' :
    ∀ (α : Type u) [Finite α] (κ : Type max v u) [Finite κ],
      ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
-- The proof proceeds by induction on `α`.
  Finite.induction_empty_option
  (-- We have to show that the theorem is invariant under `α ≃ α'` for the induction to work.
  fun {α α'} e =>
    forall_imp fun κ =>
      forall_imp fun _ =>
        Exists.imp fun ι =>
          Exists.imp fun _ h C =>
            let ⟨l, c, lc⟩ := h fun v => C (e ∘ v)
            ⟨l.map e, c, e.forall_congr_left.mp fun x => by rw [← lc x, Line.map_apply]⟩)
                                                            -- 🎉 no goals
  (by
    -- This deals with the degenerate case where `α` is empty.
    intro κ _
    -- ⊢ ∃ ι x, ∀ (C : (ι → PEmpty) → κ), ∃ l, IsMono C l
    by_cases h : Nonempty κ
    -- ⊢ ∃ ι x, ∀ (C : (ι → PEmpty) → κ), ∃ l, IsMono C l
    · refine' ⟨Unit, inferInstance, fun C => ⟨default, Classical.arbitrary _, PEmpty.rec⟩⟩
      -- 🎉 no goals
    · exact ⟨Empty, inferInstance, fun C => (h ⟨C (Empty.rec)⟩).elim⟩)
      -- 🎉 no goals
  (by
    -- Now we have to show that the theorem holds for `Option α` if it holds for `α`.
    intro α _ ihα κ _
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), ∃ l, IsMono C l
    cases nonempty_fintype κ
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), ∃ l, IsMono C l
    -- Later we'll need `α` to be nonempty. So we first deal with the trivial case where `α` is
    -- empty.
    -- Then `Option α` has only one element, so any line is monochromatic.
    by_cases h : Nonempty α
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), ∃ l, IsMono C l
    case neg =>
      refine' ⟨Unit, inferInstance, fun C => ⟨diagonal _ Unit, C fun _ => none, ?_⟩⟩
      rintro (_ | ⟨a⟩)
      · rfl
      · exact (h ⟨a⟩).elim
    -- The key idea is to show that for every `r`, in high dimension we can either find
    -- `r` color focused lines or a monochromatic line.
    suffices key :
      ∀ r : ℕ,
        ∃ (ι : Type) (_ : Fintype ι),
          ∀ C : (ι → Option α) → κ,
            (∃ s : ColorFocused C, Multiset.card s.lines = r) ∨ ∃ l, IsMono C l
    -- Given the key claim, we simply take `r = |κ| + 1`. We cannot have this many distinct colors
    -- so we must be in the second case, where there is a monochromatic line.
    · obtain ⟨ι, _inst, hι⟩ := key (Fintype.card κ + 1)
      -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), ∃ l, IsMono C l
      refine' ⟨ι, _inst, fun C => (hι C).resolve_left _⟩
      -- ⊢ ¬∃ s, ↑Multiset.card s.lines = Fintype.card κ + 1
      rintro ⟨s, sr⟩
      -- ⊢ False
      apply Nat.not_succ_le_self (Fintype.card κ)
      -- ⊢ Nat.succ (Fintype.card κ) ≤ Fintype.card κ
      rw [← Nat.add_one, ← sr, ← Multiset.card_map, ← Finset.card_mk]
      exact Finset.card_le_univ ⟨_, s.distinct_colors⟩
      -- 🎉 no goals
    -- We now prove the key claim, by induction on `r`.
    intro r
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), (∃ s, ↑Multiset.card s.lines = r) ∨ ∃ l,  …
    induction' r with r ihr
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), (∃ s, ↑Multiset.card s.lines = Nat.zero)  …
    -- The base case `r = 0` is trivial as the empty collection is color-focused.
    · exact ⟨Empty, inferInstance, fun C => Or.inl ⟨default, Multiset.card_zero⟩⟩
      -- 🎉 no goals
    -- Supposing the key claim holds for `r`, we need to show it for `r+1`. First pick a high
    -- enough dimension `ι` for `r`.
    obtain ⟨ι, _inst, hι⟩ := ihr
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), (∃ s, ↑Multiset.card s.lines = Nat.succ r …
    -- Then since the theorem holds for `α` with any number of colors, pick a dimension `ι'` such
    -- that `ι' → α` always has a monochromatic line whenever it is `(ι → Option α) → κ`-colored.
    specialize ihα ((ι → Option α) → κ)
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), (∃ s, ↑Multiset.card s.lines = Nat.succ r …
    obtain ⟨ι', _inst, hι'⟩ := ihα
    -- ⊢ ∃ ι x, ∀ (C : (ι → Option α) → κ), (∃ s, ↑Multiset.card s.lines = Nat.succ r …
    -- We claim that `ι ⊕ ι'` works for `Option α` and `κ`-coloring.
    refine' ⟨Sum ι ι', inferInstance, _⟩
    -- ⊢ ∀ (C : (ι ⊕ ι' → Option α) → κ), (∃ s, ↑Multiset.card s.lines = Nat.succ r)  …
    intro C
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    -- A `κ`-coloring of `ι ⊕ ι' → Option α` induces an `(ι → Option α) → κ`-coloring of `ι' → α`.
    specialize hι' fun v' v => C (Sum.elim v (some ∘ v'))
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    -- By choice of `ι'` this coloring has a monochromatic line `l'` with color class `C'`, where
    -- `C'` is a `κ`-coloring of `ι → α`.
    obtain ⟨l', C', hl'⟩ := hι'
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    -- If `C'` has a monochromatic line, then so does `C`. We use this in two places below.
    have mono_of_mono : (∃ l, IsMono C' l) → ∃ l, IsMono C l := by
      rintro ⟨l, c, hl⟩
      refine' ⟨l.horizontal (some ∘ l' (Classical.arbitrary α)), c, fun x => _⟩
      rw [Line.horizontal_apply, ← hl, ← hl']
    -- By choice of `ι`, `C'` either has `r` color-focused lines or a monochromatic line.
    specialize hι C'
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    rcases hι with (⟨s, sr⟩ | h)
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    on_goal 2 => exact Or.inr (mono_of_mono h)
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    -- Here we assume `C'` has `r` color focused lines. We split into cases depending on whether
    -- one of these `r` lines has the same color as the focus point.
    by_cases h : ∃ p ∈ s.lines, (p : AlmostMono _).color = C' s.focus
    -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
    -- If so then this is a `C'`-monochromatic line and we are done.
    · obtain ⟨p, p_mem, hp⟩ := h
      -- ⊢ (∃ s, ↑Multiset.card s.lines = Nat.succ r) ∨ ∃ l, IsMono C l
      refine' Or.inr (mono_of_mono ⟨p.line, p.color, _⟩)
      -- ⊢ ∀ (x : Option α), C' ((fun x i => Option.getD (idxFun p.line i) x) x) = p.co …
      rintro (_ | _)
      -- ⊢ C' ((fun x i => Option.getD (idxFun p.line i) x) none) = p.color
      rw [hp, s.is_focused p p_mem]
      -- ⊢ C' ((fun x i => Option.getD (idxFun p.line i) x) (some val✝)) = p.color
      apply p.has_color
      -- 🎉 no goals
    -- If not, we get `r+1` color focused lines by taking the product of the `r` lines with `l'`
    -- and adding to this the vertical line obtained by the focus point and `l`.
    refine' Or.inl ⟨⟨(s.lines.map _).cons ⟨(l'.map some).vertical s.focus, C' s.focus, fun x => _⟩,
            Sum.elim s.focus (l'.map some none), _, _⟩, _⟩
    -- Porting note: Needed to reorder the following two goals
    -- The product lines are almost monochromatic.
    · refine' fun p => ⟨p.line.prod (l'.map some), p.color, fun x => _⟩
      -- ⊢ C ((fun x i => Option.getD (idxFun (prod p.line (map some l')) i) x) (some x …
      rw [Line.prod_apply, Line.map_apply, ← p.has_color, ← congr_fun (hl' x)]
      -- 🎉 no goals
    -- The vertical line is almost monochromatic.
    · rw [vertical_apply, ← congr_fun (hl' x), Line.map_apply]
      -- 🎉 no goals
    -- Our `r+1` lines have the same endpoint.
    · simp_rw [Multiset.mem_cons, Multiset.mem_map]
      -- ⊢ ∀ (p : AlmostMono C), (p = { line := vertical s.focus (map some l'), color : …
      rintro _ (rfl | ⟨q, hq, rfl⟩)
      -- ⊢ (fun i => Option.getD (idxFun { line := vertical s.focus (map some l'), colo …
      · simp only [vertical_apply]
        -- 🎉 no goals
      · simp only [prod_apply, s.is_focused q hq]
        -- 🎉 no goals
    -- Our `r+1` lines have distinct colors (this is why we needed to split into cases above).
    · rw [Multiset.map_cons, Multiset.map_map, Multiset.nodup_cons, Multiset.mem_map]
      -- ⊢ (¬∃ a, a ∈ s.lines ∧ (AlmostMono.color ∘ fun p => { line := prod p.line (map …
      exact ⟨fun ⟨q, hq, he⟩ => h ⟨q, hq, he⟩, s.distinct_colors⟩
      -- 🎉 no goals
    -- Finally, we really do have `r+1` lines!
    · rw [Multiset.card_cons, Multiset.card_map, sr])
      -- 🎉 no goals
-- Porting note: Remove align on private declas
#noalign combinatorics.line.exists_mono_in_high_dimension'

/-- The Hales-Jewett theorem: for any finite types `α` and `κ`, there exists a finite type `ι` such
that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromatic combinatorial line. -/
theorem exists_mono_in_high_dimension (α : Type u) [Finite α] (κ : Type v) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension'.{u,v} α (ULift.{u,v} κ)
  ⟨ι, ιfin, fun C =>
    let ⟨l, c, hc⟩ := hι (ULift.up ∘ C)
    ⟨l, c.down, fun x => by rw [← hc x, Function.comp_apply]⟩⟩
                            -- 🎉 no goals
#align combinatorics.line.exists_mono_in_high_dimension Combinatorics.Line.exists_mono_in_high_dimension

end Line

/-- A generalization of Van der Waerden's theorem: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`. -/
theorem exists_mono_homothetic_copy {M κ : Type*} [AddCommMonoid M] (S : Finset M) [Finite κ]
    (C : M → κ) : ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c := by
  obtain ⟨ι, _inst, hι⟩ := Line.exists_mono_in_high_dimension S κ
  -- ⊢ ∃ a, a > 0 ∧ ∃ b c, ∀ (s : M), s ∈ S → C (a • s + b) = c
  specialize hι fun v => C <| ∑ i, v i
  -- ⊢ ∃ a, a > 0 ∧ ∃ b c, ∀ (s : M), s ∈ S → C (a • s + b) = c
  obtain ⟨l, c, hl⟩ := hι
  -- ⊢ ∃ a, a > 0 ∧ ∃ b c, ∀ (s : M), s ∈ S → C (a • s + b) = c
  set s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none ) with hs
  -- ⊢ ∃ a, a > 0 ∧ ∃ b c, ∀ (s : M), s ∈ S → C (a • s + b) = c
  refine'
    ⟨s.card, Finset.card_pos.mpr ⟨l.proper.choose, _⟩, ∑ i in sᶜ, ((l.idxFun i).map _).getD 0,
      c, _⟩
  · rw [hs, Finset.mem_filter]
    -- ⊢ Exists.choose (_ : ∃ i, Line.idxFun l i = none) ∈ Finset.univ ∧ Line.idxFun  …
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩
    -- 🎉 no goals
  · exact fun m => m
    -- 🎉 no goals
  intro x xs
  -- ⊢ C (Finset.card s • x + ∑ i in sᶜ, Option.getD (Option.map (fun m => ↑m) (Lin …
  rw [← hl ⟨x, xs⟩]
  -- ⊢ C (Finset.card s • x + ∑ i in sᶜ, Option.getD (Option.map (fun m => ↑m) (Lin …
  clear hl; congr
  -- ⊢ C (Finset.card s • x + ∑ i in sᶜ, Option.getD (Option.map (fun m => ↑m) (Lin …
            -- ⊢ Finset.card s • x + ∑ i in sᶜ, Option.getD (Option.map (fun m => ↑m) (Line.i …
  rw [← Finset.sum_add_sum_compl s]
  -- ⊢ Finset.card s • x + ∑ i in sᶜ, Option.getD (Option.map (fun m => ↑m) (Line.i …
  congr 1
  -- ⊢ Finset.card s • x = ∑ i in s, ↑((fun x i => Option.getD (Line.idxFun l i) x) …
  · rw [← Finset.sum_const]
    -- ⊢ ∑ _x in s, x = ∑ i in s, ↑((fun x i => Option.getD (Line.idxFun l i) x) { va …
    apply Finset.sum_congr rfl
    -- ⊢ ∀ (x_1 : ι), x_1 ∈ s → x = ↑((fun x i => Option.getD (Line.idxFun l i) x) {  …
    intro i hi
    -- ⊢ x = ↑((fun x i => Option.getD (Line.idxFun l i) x) { val := x, property := x …
    rw [hs, Finset.mem_filter] at hi
    -- ⊢ x = ↑((fun x i => Option.getD (Line.idxFun l i) x) { val := x, property := x …
    rw [l.apply_none _ _ hi.right, Subtype.coe_mk]
    -- 🎉 no goals
  · apply Finset.sum_congr rfl
    -- ⊢ ∀ (x_1 : ι), x_1 ∈ sᶜ → Option.getD (Option.map (fun m => ↑m) (Line.idxFun l …
    intro i hi
    -- ⊢ Option.getD (Option.map (fun m => ↑m) (Line.idxFun l i)) 0 = ↑((fun x i => O …
    rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
    -- ⊢ Option.getD (Option.map (fun m => ↑m) (Line.idxFun l i)) 0 = ↑((fun x i => O …
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.right
    -- ⊢ Option.getD (Option.map (fun m => ↑m) (Line.idxFun l i)) 0 = ↑((fun x i => O …
    simp_rw [← hy, Option.map_some', Option.getD]
    -- 🎉 no goals
#align combinatorics.exists_mono_homothetic_copy Combinatorics.exists_mono_homothetic_copy

end Combinatorics
