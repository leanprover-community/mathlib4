/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Shrink
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Hales-Jewett theorem

We prove the Hales-Jewett theorem. We deduce Van der Waerden's theorem and the multidimensional
Hales-Jewett theorem as corollaries.

The Hales-Jewett theorem is a result in Ramsey theory dealing with *combinatorial lines*. Given
an 'alphabet' `α : Type*` and `a b : α`, an example of a combinatorial line in `α^5` is
`{ (a, x, x, b, x) | x : α }`. See `Combinatorics.Line` for a precise general definition. The
Hales-Jewett theorem states that for any fixed finite types `α` and `κ`, there exists a (potentially
huge) finite type `ι` such that whenever `ι → α` is `κ`-colored (i.e. for any coloring
`C : (ι → α) → κ`), there exists a monochromatic line. We prove the Hales-Jewett theorem using
the idea of *color focusing* and a *product argument*. See the proof of
`Combinatorics.Line.exists_mono_in_high_dimension'` for details.

*Combinatorial subspaces* are higher-dimensional analogues of combinatorial lines. See
`Combinatorics.Subspace`. The multidimensional Hales-Jewett theorem generalises the statement above
from combinatorial lines to combinatorial subspaces of a fixed dimension.

The version of Van der Waerden's theorem in this file states that whenever a commutative monoid `M`
is finitely colored and `S` is a finite subset, there exists a monochromatic homothetic copy of `S`.
This follows from the Hales-Jewett theorem by considering the map `(ι → S) → M` sending `v`
to `∑ i : ι, v i`, which sends a combinatorial line to a homothetic copy of `S`.

## Main results

- `Combinatorics.Line.exists_mono_in_high_dimension`: The Hales-Jewett theorem.
- `Combinatorics.Subspace.exists_mono_in_high_dimension`: The multidimensional Hales-Jewett theorem.
- `Combinatorics.exists_mono_homothetic_copy`: A generalization of Van der Waerden's theorem.

## Implementation details

For convenience, we work directly with finite types instead of natural numbers. That is, we write
`α, ι, κ` for (finite) types where one might traditionally use natural numbers `n, H, c`. This
allows us to work directly with `α`, `Option α`, `(ι → α) → κ`, and `ι ⊕ ι'` instead of `Fin n`,
`Fin (n+1)`, `Fin (c^(n^H))`, and `Fin (H + H')`.

## TODO

- Prove a finitary version of Van der Waerden's theorem (either by compactness or by modifying the
current proof).

- One could reformulate the proof of Hales-Jewett to give explicit upper bounds on the number of
coordinates needed.

## Tags

combinatorial line, Ramsey theory, arithmetic progression

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

-/

open Function
open scoped Finset

universe u v
variable {η α ι κ : Type*}

namespace Combinatorics

/-- The type of combinatorial subspaces. A subspace `l : Subspace η α ι` in the hypercube `ι → α`
defines a function `(η → α) → ι → α` from `η → α` to the hypercube, such that for each coordinate
`i : ι` and direction `e : η`, the function `fun x ↦ l x i` is either `fun x ↦ x e` for some
direction `e : η` or constant. We require subspaces to be non-degenerate in the sense that, for
every `e : η`, `fun x ↦ l x i` is `fun x ↦ x e` for at least one `i`.

Formally, a subspace is represented by a word `l.idxFun : ι → α ⊕ η` which says whether
`fun x ↦ l x i` is `fun x ↦ x e` (corresponding to `l.idxFun i = Sum.inr e`) or constantly `a`
(corresponding to `l.idxFun i = Sum.inl a`).

When `α` has size `1` there can be many elements of `Subspace η α ι` defining the same function. -/
@[ext]
structure Subspace (η α ι : Type*) where
  /-- The word representing a combinatorial subspace. `l.idxfun i = Sum.inr e` means that
  `l x i = x e` for all `x` and `l.idxfun i = some a` means that `l x i = a` for all `x`. -/
  idxFun : ι → α ⊕ η
  /-- We require combinatorial subspaces to be nontrivial in the sense that `fun x ↦ l x i` is
  `fun x ↦ x e` for at least one coordinate `i`. -/
  proper : ∀ e, ∃ i, idxFun i = Sum.inr e

namespace Subspace
variable {η α ι κ : Type*} {l : Subspace η α ι} {x : η → α} {i : ι} {a : α} {e : η}

/-- The combinatorial subspace corresponding to the identity embedding `(ι → α) → (ι → α)`. -/
instance : Inhabited (Subspace ι α ι) := ⟨⟨Sum.inr, fun i ↦ ⟨i, rfl⟩⟩⟩

/-- Consider a subspace `l : Subspace η α ι` as a function `(η → α) → ι → α`. -/
@[coe] def toFun (l : Subspace η α ι) (x : η → α) (i : ι) : α := (l.idxFun i).elim id x

instance instCoeFun : CoeFun (Subspace η α ι) (fun _ ↦ (η → α) → ι → α) := ⟨toFun⟩

lemma coe_apply (l : Subspace η α ι) (x : η → α) (i : ι) : l x i = (l.idxFun i).elim id x := rfl

-- Note: This is not made a `FunLike` instance to avoid having two syntactically different coercions
lemma coe_injective [Nontrivial α] : Injective ((⇑) : Subspace η α ι → (η → α) → ι → α) := by
  classical
  rintro l m hlm
  ext i
  simp only [funext_iff] at hlm
  cases hl : idxFun l i with
  | inl a =>
    obtain ⟨b, hba⟩ := exists_ne a
    cases hm : idxFun m i <;> simpa [hl, hm, hba.symm, coe_apply] using hlm (const _ b) i
  | inr e =>
    cases hm : idxFun m i with
    | inl a =>
      obtain ⟨b, hba⟩ := exists_ne a
      simpa [hl, hm, hba, coe_apply] using hlm (const _ b) i
    | inr f =>
      obtain ⟨a, b, hab⟩ := exists_pair_ne α
      simp only [Sum.inr.injEq]
      by_contra! hef
      simpa [hl, hm, hef, hab, coe_apply] using hlm (Function.update (const _ a) f b) i

lemma apply_def (l : Subspace η α ι) (x : η → α) (i : ι) : l x i = (l.idxFun i).elim id x := rfl
lemma apply_inl (h : l.idxFun i = Sum.inl a) : l x i = a := by simp [apply_def, h]
lemma apply_inr (h : l.idxFun i = Sum.inr e) : l x i = x e := by simp [apply_def, h]

/-- Given a coloring `C` of `ι → α` and a combinatorial subspace `l` of `ι → α`, `l.IsMono C`
means that `l` is monochromatic with regard to `C`. -/
def IsMono (C : (ι → α) → κ) (l : Subspace η α ι) : Prop := ∃ c, ∀ x, C (l x) = c

variable {η' α' ι' : Type*}

/-- Change the index types of a subspace. -/
def reindex (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') : Subspace η' α' ι' where
  idxFun i := (l.idxFun <| eι.symm i).map eα eη
  proper e := (eι.exists_congr fun i ↦ by cases h : idxFun l i <;>
    simp [*, funext_iff, Equiv.eq_symm_apply]).1 <| l.proper <| eη.symm e

@[simp] lemma reindex_apply (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') (x i) :
    l.reindex eη eα eι x i = eα (l (eα.symm ∘ x ∘ eη) <| eι.symm i) := by
  cases h : l.idxFun (eι.symm i) <;> simp [h, reindex, coe_apply]

@[simp] lemma reindex_isMono {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι' → α') → κ} :
    (l.reindex eη eα eι).IsMono C ↔ l.IsMono fun x ↦ C <| eα ∘ x ∘ eι.symm := by
  simp only [IsMono, funext (reindex_apply _ _ _ _ _), coe_apply]
  exact exists_congr fun c ↦ (eη.arrowCongr eα).symm.forall_congr <| by aesop

protected lemma IsMono.reindex {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι → α) → κ}
    (hl : l.IsMono C) : (l.reindex eη eα eι).IsMono fun x ↦ C <| eα.symm ∘ x ∘ eι := by
  simp [reindex_isMono, Function.comp_assoc]; simpa [← Function.comp_assoc]

end Subspace

/-- The type of combinatorial lines. A line `l : Line α ι` in the hypercube `ι → α` defines a
function `α → ι → α` from `α` to the hypercube, such that for each coordinate `i : ι`, the function
`fun x ↦ l x i` is either `id` or constant. We require lines to be nontrivial in the sense that
`fun x ↦ l x i` is `id` for at least one `i`.

Formally, a line is represented by a word `l.idxFun : ι → Option α` which says whether
`fun x ↦ l x i` is `id` (corresponding to `l.idxFun i = none`) or constantly `y` (corresponding to
`l.idxFun i = some y`).

When `α` has size `1` there can be many elements of `Line α ι` defining the same function. -/
@[ext]
structure Line (α ι : Type*) where
  /-- The word representing a combinatorial line. `l.idxfun i = none` means that
  `l x i = x` for all `x` and `l.idxfun i = some y` means that `l x i = y`. -/
  idxFun : ι → Option α
  /-- We require combinatorial lines to be nontrivial in the sense that `fun x ↦ l x i` is `id` for
  at least one coordinate `i`. -/
  proper : ∃ i, idxFun i = none

namespace Line
variable {l : Line α ι} {i : ι} {a x : α}

/-- Consider a line `l : Line α ι` as a function `α → ι → α`. -/
@[coe] def toFun (l : Line α ι) (x : α) (i : ι) : α := (l.idxFun i).getD x

-- This lets us treat a line `l : Line α ι` as a function `α → ι → α`.
instance instCoeFun : CoeFun (Line α ι) fun _ => α → ι → α := ⟨toFun⟩

@[simp] lemma coe_apply (l : Line α ι) (x : α) (i : ι) : l x i = (l.idxFun i).getD x := rfl

-- Note: This is not made a `FunLike` instance to avoid having two syntactically different coercions
lemma coe_injective [Nontrivial α] : Injective ((⇑) : Line α ι → α → ι → α) := by
  rintro l m hlm
  ext i a
  obtain ⟨b, hba⟩ := exists_ne a
  simp only [Option.mem_def, funext_iff] at hlm ⊢
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases hi : idxFun m i <;> simpa [@eq_comm _ a, hi, h, hba] using hlm b i
  · cases hi : idxFun l i <;> simpa [@eq_comm _ a, hi, h, hba] using hlm b i

/-- A line is monochromatic if all its points are the same color. -/
def IsMono {α ι κ} (C : (ι → α) → κ) (l : Line α ι) : Prop :=
  ∃ c, ∀ x, C (l x) = c

/-- Consider a line as a one-dimensional subspace. -/
def toSubspaceUnit (l : Line α ι) : Subspace Unit α ι where
  idxFun i := (l.idxFun i).elim (.inr ()) .inl
  proper _ := l.proper.imp fun i hi ↦ by simp [hi]

@[simp] lemma toSubspaceUnit_apply (l : Line α ι) (a) : ⇑l.toSubspaceUnit a = l (a ()) := by
  ext i; cases h : l.idxFun i <;> simp [toSubspaceUnit, h, Subspace.coe_apply]

@[simp] lemma toSubspaceUnit_isMono {C : (ι → α) → κ} : l.toSubspaceUnit.IsMono C ↔ l.IsMono C := by
  simp only [Subspace.IsMono, toSubspaceUnit_apply, IsMono]
  exact exists_congr fun c ↦ ⟨fun h a ↦ h fun _ ↦ a, fun h a ↦ h _⟩

protected alias ⟨_, IsMono.toSubspaceUnit⟩ := toSubspaceUnit_isMono

/-- Consider a line in `ι → η → α` as a `η`-dimensional subspace in `ι × η → α`. -/
def toSubspace (l : Line (η → α) ι) : Subspace η α (ι × η) where
  idxFun ie := (l.idxFun ie.1).elim (.inr ie.2) (fun f ↦ .inl <| f ie.2)
  proper e := let ⟨i, hi⟩ := l.proper; ⟨(i, e), by simp [hi]⟩

@[simp] lemma toSubspace_apply (l : Line (η → α) ι) (a ie) :
    ⇑l.toSubspace a ie = l a ie.1 ie.2 := by
  cases h : l.idxFun ie.1 <;> simp [toSubspace, h, coe_apply, Subspace.coe_apply]

@[simp] lemma toSubspace_isMono {l : Line (η → α) ι} {C : (ι × η → α) → κ} :
    l.toSubspace.IsMono C ↔ l.IsMono fun x : ι → η → α  ↦ C fun (i, e) ↦ x i e := by
  simp [Subspace.IsMono, IsMono, funext (toSubspace_apply _ _)]

protected alias ⟨_, IsMono.toSubspace⟩ := toSubspace_isMono

/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal (α ι) [Nonempty ι] : Line α ι where
  idxFun _ := none
  proper := ⟨Classical.arbitrary ι, rfl⟩

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

instance {α ι κ} (C : (ι → Option α) → κ) : Inhabited (ColorFocused C) := by
  refine ⟨⟨0, fun _ => none, fun h => ?_, Multiset.nodup_zero⟩⟩
  simp only [Multiset.notMem_zero, IsEmpty.forall_iff]

/-- A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
def map {α α' ι} (f : α → α') (l : Line α ι) : Line α' ι where
  idxFun i := (l.idxFun i).map f
  proper := ⟨l.proper.choose, by simp only [l.proper.choose_spec, Option.map_none]⟩

/-- A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def vertical {α ι ι'} (v : ι → α) (l : Line α ι') : Line α (ι ⊕ ι') where
  idxFun := Sum.elim (some ∘ v) l.idxFun
  proper := ⟨Sum.inr l.proper.choose, l.proper.choose_spec⟩

/-- A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def horizontal {α ι ι'} (l : Line α ι) (v : ι' → α) : Line α (ι ⊕ ι') where
  idxFun := Sum.elim l.idxFun (some ∘ v)
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩

/-- One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α`. -/
def prod {α ι ι'} (l : Line α ι) (l' : Line α ι') : Line α (ι ⊕ ι') where
  idxFun := Sum.elim l.idxFun l'.idxFun
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩

theorem apply_def (l : Line α ι) (x : α) : l x = fun i => (l.idxFun i).getD x := rfl

theorem apply_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i = none) : l x i = x := by
  simp only [Option.getD_none, h, l.apply_def]

lemma apply_some (h : l.idxFun i = some a) : l x i = a := by simp [l.apply_def, h]

@[simp]
theorem map_apply {α α' ι} (f : α → α') (l : Line α ι) (x : α) : l.map f (f x) = f ∘ l x := by
  simp only [Line.apply_def, Line.map, Option.getD_map, comp_def]

@[simp]
theorem vertical_apply {α ι ι'} (v : ι → α) (l : Line α ι') (x : α) :
    l.vertical v x = Sum.elim v (l x) := by
  funext i
  cases i <;> rfl

@[simp]
theorem horizontal_apply {α ι ι'} (l : Line α ι) (v : ι' → α) (x : α) :
    l.horizontal v x = Sum.elim (l x) v := by
  funext i
  cases i <;> rfl

@[simp]
theorem prod_apply {α ι ι'} (l : Line α ι) (l' : Line α ι') (x : α) :
    l.prod l' x = Sum.elim (l x) (l' x) := by
  funext i
  cases i <;> rfl

@[simp]
theorem diagonal_apply {α ι} [Nonempty ι] (x : α) : diagonal α ι x = fun _ => x := by
  ext; simp [diagonal]

/-- The **Hales-Jewett theorem**. This version has a restriction on universe levels which is
necessary for the proof. See `exists_mono_in_high_dimension` for a fully universe-polymorphic
version. -/
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
            ⟨l.map e, c, e.forall_congr_right.mp fun x => by rw [← lc x, Line.map_apply]⟩)
  (by
    -- This deals with the degenerate case where `α` is empty.
    intro κ _
    by_cases h : Nonempty κ
    · refine ⟨Unit, inferInstance, fun C => ⟨default, Classical.arbitrary _, PEmpty.rec⟩⟩
    · exact ⟨Empty, inferInstance, fun C => (h ⟨C (Empty.rec)⟩).elim⟩)
  (by
    -- Now we have to show that the theorem holds for `Option α` if it holds for `α`.
    intro α _ ihα κ _
    cases nonempty_fintype κ
    -- Later we'll need `α` to be nonempty. So we first deal with the trivial case where `α` is
    -- empty.
    -- Then `Option α` has only one element, so any line is monochromatic.
    by_cases h : Nonempty α
    case neg =>
      refine ⟨Unit, inferInstance, fun C => ⟨diagonal _ Unit, C fun _ => none, ?_⟩⟩
      rintro (_ | ⟨a⟩)
      · rfl
      · exact (h ⟨a⟩).elim
    -- The key idea is to show that for every `r`, in high dimension we can either find
    -- `r` color focused lines or a monochromatic line.
    suffices key :
      ∀ r : ℕ,
        ∃ (ι : Type) (_ : Fintype ι),
          ∀ C : (ι → Option α) → κ,
            (∃ s : ColorFocused C, Multiset.card s.lines = r) ∨ ∃ l, IsMono C l by
      -- Given the key claim, we simply take `r = |κ| + 1`. We cannot have this many distinct colors
      -- so we must be in the second case, where there is a monochromatic line.
      obtain ⟨ι, _inst, hι⟩ := key (Fintype.card κ + 1)
      refine ⟨ι, _inst, fun C => (hι C).resolve_left ?_⟩
      rintro ⟨s, sr⟩
      apply Nat.not_succ_le_self (Fintype.card κ)
      rw [← Nat.add_one, ← sr, ← Multiset.card_map, ← Finset.card_mk]
      exact Finset.card_le_univ ⟨_, s.distinct_colors⟩
    -- We now prove the key claim, by induction on `r`.
    intro r
    induction r with
    -- The base case `r = 0` is trivial as the empty collection is color-focused.
    | zero => exact ⟨Empty, inferInstance, fun C => Or.inl ⟨default, Multiset.card_zero⟩⟩
    | succ r ihr =>
    -- Supposing the key claim holds for `r`, we need to show it for `r+1`. First pick a high
    -- enough dimension `ι` for `r`.
    obtain ⟨ι, _inst, hι⟩ := ihr
    -- Then since the theorem holds for `α` with any number of colors, pick a dimension `ι'` such
    -- that `ι' → α` always has a monochromatic line whenever it is `(ι → Option α) → κ`-colored.
    specialize ihα ((ι → Option α) → κ)
    obtain ⟨ι', _inst, hι'⟩ := ihα
    -- We claim that `ι ⊕ ι'` works for `Option α` and `κ`-coloring.
    refine ⟨ι ⊕ ι', inferInstance, ?_⟩
    intro C
    -- A `κ`-coloring of `ι ⊕ ι' → Option α` induces an `(ι → Option α) → κ`-coloring of `ι' → α`.
    specialize hι' fun v' v => C (Sum.elim v (some ∘ v'))
    -- By choice of `ι'` this coloring has a monochromatic line `l'` with color class `C'`, where
    -- `C'` is a `κ`-coloring of `ι → α`.
    obtain ⟨l', C', hl'⟩ := hι'
    -- If `C'` has a monochromatic line, then so does `C`. We use this in two places below.
    have mono_of_mono : (∃ l, IsMono C' l) → ∃ l, IsMono C l := by
      rintro ⟨l, c, hl⟩
      refine ⟨l.horizontal (some ∘ l' (Classical.arbitrary α)), c, fun x => ?_⟩
      rw [Line.horizontal_apply, ← hl, ← hl']
    -- By choice of `ι`, `C'` either has `r` color-focused lines or a monochromatic line.
    specialize hι C'
    rcases hι with (⟨s, sr⟩ | h)
    on_goal 2 => exact Or.inr (mono_of_mono h)
    -- Here we assume `C'` has `r` color focused lines. We split into cases depending on whether
    -- one of these `r` lines has the same color as the focus point.
    by_cases h : ∃ p ∈ s.lines, (p : AlmostMono _).color = C' s.focus
    -- If so then this is a `C'`-monochromatic line and we are done.
    · obtain ⟨p, p_mem, hp⟩ := h
      refine Or.inr (mono_of_mono ⟨p.line, p.color, ?_⟩)
      rintro (_ | _)
      · rw [hp, s.is_focused p p_mem]
      · apply p.has_color
    -- If not, we get `r+1` color focused lines by taking the product of the `r` lines with `l'`
    -- and adding to this the vertical line obtained by the focus point and `l`.
    refine Or.inl ⟨⟨(s.lines.map ?_).cons ⟨(l'.map some).vertical s.focus, C' s.focus, fun x => ?_⟩,
            Sum.elim s.focus (l'.map some none), ?_, ?_⟩, ?_⟩
    -- The product lines are almost monochromatic.
    · refine fun p => ⟨p.line.prod (l'.map some), p.color, fun x => ?_⟩
      rw [Line.prod_apply, Line.map_apply, ← p.has_color, ← congr_fun (hl' x)]
    -- The vertical line is almost monochromatic.
    · rw [vertical_apply, ← congr_fun (hl' x), Line.map_apply]
    -- Our `r+1` lines have the same endpoint.
    · simp_rw [Multiset.mem_cons, Multiset.mem_map]
      rintro _ (rfl | ⟨q, hq, rfl⟩)
      · simp only [vertical_apply]
      · simp only [prod_apply, s.is_focused q hq]
    -- Our `r+1` lines have distinct colors (this is why we needed to split into cases above).
    · rw [Multiset.map_cons, Multiset.map_map, Multiset.nodup_cons, Multiset.mem_map]
      exact ⟨fun ⟨q, hq, he⟩ => h ⟨q, hq, he⟩, s.distinct_colors⟩
    -- Finally, we really do have `r+1` lines!
    · rw [Multiset.card_cons, Multiset.card_map, sr])

/-- The **Hales-Jewett theorem**: For any finite types `α` and `κ`, there exists a finite type `ι`
such that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromatic combinatorial
line. -/
theorem exists_mono_in_high_dimension (α : Type u) [Finite α] (κ : Type v) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension'.{u,v} α (ULift.{u,v} κ)
  ⟨ι, ιfin, fun C =>
    let ⟨l, c, hc⟩ := hι (ULift.up ∘ C)
    ⟨l, c.down, fun x => by rw [← hc x, Function.comp_apply]⟩⟩

end Line

/-- A generalization of Van der Waerden's theorem: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`. -/
theorem exists_mono_homothetic_copy {M κ : Type*} [AddCommMonoid M] (S : Finset M) [Finite κ]
    (C : M → κ) : ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Line.exists_mono_in_high_dimension S κ
  specialize hι fun v => C <| ∑ i, v i
  obtain ⟨l, c, hl⟩ := hι
  set s : Finset ι := {i | l.idxFun i = none} with hs
  refine ⟨#s, Finset.card_pos.mpr ⟨l.proper.choose, ?_⟩, ∑ i ∈ sᶜ, ((l.idxFun i).map ?_).getD 0,
    c, ?_⟩
  · rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩
  · exact fun m => m
  intro x xs
  rw [← hl ⟨x, xs⟩]
  clear hl; congr
  rw [← Finset.sum_add_sum_compl s]
  congr 1
  · rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.mem_filter] at hi
    rw [l.apply_none _ _ hi.right, Subtype.coe_mk]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.right
    simp [← hy, Option.map_some, Option.getD]

namespace Subspace

/-- The **multidimensional Hales-Jewett theorem**, aka **extended Hales-Jewett theorem**: For any
finite types `η`, `α` and `κ`, there exists a finite type `ι` such that whenever the hypercube
`ι → α` is `κ`-colored, there is a monochromatic combinatorial subspace of dimension `η`. -/
theorem exists_mono_in_high_dimension (α κ η) [Finite α] [Finite κ] [Finite η] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Subspace η α ι, l.IsMono C := by
  cases nonempty_fintype η
  obtain ⟨ι, _, hι⟩ := Line.exists_mono_in_high_dimension (Shrink.{0} η → α) κ
  refine ⟨ι × Shrink η, inferInstance, fun C ↦ ?_⟩
  obtain ⟨l, hl⟩ := hι fun x ↦ C fun (i, e) ↦ x i e
  refine ⟨l.toSubspace.reindex (equivShrink.{0} η).symm (Equiv.refl _) (Equiv.refl _), ?_⟩
  convert hl.toSubspace.reindex
  simp

/-- A variant of the **extended Hales-Jewett theorem** `exists_mono_in_high_dimension` where the
returned type is some `Fin n` instead of a general fintype. -/
theorem exists_mono_in_high_dimension_fin (α κ η) [Finite α] [Finite κ] [Finite η] :
    ∃ n, ∀ C : (Fin n → α) → κ, ∃ l : Subspace η α (Fin n), l.IsMono C := by
  obtain ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension α κ η
  refine ⟨Fintype.card ι, fun C ↦ ?_⟩
  obtain ⟨l, c, cl⟩ := hι fun v ↦ C (v ∘ (Fintype.equivFin _).symm)
  refine ⟨⟨l.idxFun ∘ (Fintype.equivFin _).symm, fun e ↦ ?_⟩, c, cl⟩
  obtain ⟨i, hi⟩ := l.proper e
  use Fintype.equivFin _ i
  simpa using hi

end Subspace
end Combinatorics
