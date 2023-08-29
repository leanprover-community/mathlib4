/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Order.WellFounded
import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Combinatorics.Quiver.Path

#align_import combinatorics.quiver.arborescence from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Arborescences

A quiver `V` is an arborescence (or directed rooted tree) when we have a root vertex `root : V` such
that for every `b : V` there is a unique path from `root` to `b`.

## Main definitions

- `Quiver.Arborescence V`: a typeclass asserting that `V` is an arborescence
- `arborescenceMk`: a convenient way of proving that a quiver is an arborescence
- `RootedConnected r`: a typeclass asserting that there is at least one path from `r` to `b` for
every `b`.
- `geodesicSubtree r`: given `[RootedConnected r]`, this is a subquiver of `V` which contains
just enough edges to include a shortest path from `r` to `b` for every `b`.
- `geodesicArborescence : Arborescence (geodesicSubtree r)`: an instance saying that the geodesic
subtree is an arborescence. This proves the directed analogue of 'every connected graph has a
spanning tree'. This proof avoids the use of Zorn's lemma.
-/


open Opposite

universe v u

namespace Quiver

/-- A quiver is an arborescence when there is a unique path from the default vertex
    to every other vertex. -/
class Arborescence (V : Type u) [Quiver.{v} V] : Type max u v where
  /-- The root of the arborescence. -/
  root : V
  /-- There is a unique path from the root to any other vertex. -/
  uniquePath : ∀ b : V, Unique (Path root b)
#align quiver.arborescence Quiver.Arborescence

/-- The root of an arborescence. -/
def root (V : Type u) [Quiver V] [Arborescence V] : V :=
  Arborescence.root
#align quiver.root Quiver.root

instance {V : Type u} [Quiver V] [Arborescence V] (b : V) : Unique (Path (root V) b) :=
  Arborescence.uniquePath b

/-- To show that `[Quiver V]` is an arborescence with root `r : V`, it suffices to
  - provide a height function `V → ℕ` such that every arrow goes from a
    lower vertex to a higher vertex,
  - show that every vertex has at most one arrow to it, and
  - show that every vertex other than `r` has an arrow to it. -/
noncomputable def arborescenceMk {V : Type u} [Quiver V] (r : V) (height : V → ℕ)
    (height_lt : ∀ ⦃a b⦄, (a ⟶ b) → height a < height b)
    (unique_arrow : ∀ ⦃a b c : V⦄ (e : a ⟶ c) (f : b ⟶ c), a = b ∧ HEq e f)
    (root_or_arrow : ∀ b, b = r ∨ ∃ a, Nonempty (a ⟶ b)) :
    Arborescence V where
  root := r
  uniquePath b :=
    ⟨Classical.inhabited_of_nonempty (by
      rcases show ∃ n, height b < n from ⟨_, Nat.lt.base _⟩ with ⟨n, hn⟩
      -- ⊢ Nonempty (Path r b)
      induction' n with n ih generalizing b
      -- ⊢ Nonempty (Path r b)
      · exact False.elim (Nat.not_lt_zero _ hn)
        -- 🎉 no goals
      rcases root_or_arrow b with (⟨⟨⟩⟩ | ⟨a, ⟨e⟩⟩)
      -- ⊢ Nonempty (Path r r)
      · exact ⟨Path.nil⟩
        -- 🎉 no goals
      · rcases ih a (lt_of_lt_of_le (height_lt e) (Nat.lt_succ_iff.mp hn)) with ⟨p⟩
        -- ⊢ Nonempty (Path r b)
        exact ⟨p.cons e⟩), by
        -- 🎉 no goals
      have height_le : ∀ {a b}, Path a b → height a ≤ height b := by
        intro a b p
        induction' p with b c _ e ih
        rfl
        exact le_of_lt (lt_of_le_of_lt ih (height_lt e))
      suffices ∀ p q : Path r b, p = q by
        intro p
        apply this
      intro p q
      -- ⊢ p = q
      induction' p with a c p e ih <;> cases' q with b _ q f
      -- ⊢ Path.nil = q
                                       -- ⊢ Path.nil = Path.nil
                                       -- ⊢ Path.cons p e = Path.nil
      · rfl
        -- 🎉 no goals
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt (height_le q) (height_lt f)))
        -- 🎉 no goals
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt (height_le p) (height_lt e)))
        -- 🎉 no goals
      · rcases unique_arrow e f with ⟨⟨⟩, ⟨⟩⟩
        -- ⊢ Path.cons p e = Path.cons q e
        rw [ih]⟩
        -- 🎉 no goals
#align quiver.arborescence_mk Quiver.arborescenceMk

/-- `RootedConnected r` means that there is a path from `r` to any other vertex. -/
class RootedConnected {V : Type u} [Quiver V] (r : V) : Prop where
  nonempty_path : ∀ b : V, Nonempty (Path r b)
#align quiver.rooted_connected Quiver.RootedConnected

attribute [instance] RootedConnected.nonempty_path

section GeodesicSubtree

variable {V : Type u} [Quiver.{v + 1} V] (r : V) [RootedConnected r]

/-- A path from `r` of minimal length. -/
noncomputable def shortestPath (b : V) : Path r b :=
  WellFounded.min (measure Path.length).wf Set.univ Set.univ_nonempty
#align quiver.shortest_path Quiver.shortestPath

/-- The length of a path is at least the length of the shortest path -/
theorem shortest_path_spec {a : V} (p : Path r a) : (shortestPath r a).length ≤ p.length :=
  not_lt.mp (WellFounded.not_lt_min (measure _).wf Set.univ _ trivial)
#align quiver.shortest_path_spec Quiver.shortest_path_spec

/-- A subquiver which by construction is an arborescence. -/
def geodesicSubtree : WideSubquiver V := fun a b =>
  { e | ∃ p : Path r a, shortestPath r b = p.cons e }
#align quiver.geodesic_subtree Quiver.geodesicSubtree

noncomputable instance geodesicArborescence : Arborescence (geodesicSubtree r) :=
  arborescenceMk r (fun a => (shortestPath r a).length)
    (by
      rintro a b ⟨e, p, h⟩
      -- ⊢ (fun a => Path.length (shortestPath r a)) a < (fun a => Path.length (shortes …
      simp_rw [h, Path.length_cons, Nat.lt_succ_iff]
      -- ⊢ Path.length (shortestPath r a) ≤ Path.length p
      apply shortest_path_spec)
      -- 🎉 no goals
    (by
      rintro a b c ⟨e, p, h⟩ ⟨f, q, j⟩
      -- ⊢ a = b ∧ HEq { val := e, property := (_ : ∃ p, shortestPath r c = Path.cons p …
      cases h.symm.trans j
      -- ⊢ a = a ∧ HEq { val := e, property := (_ : ∃ p, shortestPath r c = Path.cons p …
      constructor <;> rfl)
      -- ⊢ a = a
                      -- 🎉 no goals
                      -- 🎉 no goals
    (by
      intro b
      -- ⊢ b = r ∨ ∃ a, Nonempty (a ⟶ b)
      rcases hp : shortestPath r b with (_ | ⟨p, e⟩)
      -- ⊢ r = r ∨ ∃ a, Nonempty (a ⟶ r)
      · exact Or.inl rfl
        -- 🎉 no goals
      · exact Or.inr ⟨_, ⟨⟨e, p, hp⟩⟩⟩)
        -- 🎉 no goals
#align quiver.geodesic_arborescence Quiver.geodesicArborescence

end GeodesicSubtree

end Quiver
