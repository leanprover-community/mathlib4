/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
import Mathlib.Order.OrderIsoNat

/-!
# Rank functions for pairings

We introduce types of (weak) rank functions for a pairing `P`
of a subcomplex `A` of a simplicial set `X`. These are
functions `f : P.II → α` such that `P.AncestralRel x y` implies `f x < f y`
(in the weak case, we require this only under the additional condition
that `x` and `y` are of the same dimension). Such rank functions
are used in order to show that the ancestral relation on `P.II` is well founded,
i.e. that `P` is regular (when we already know `P` is proper).
Conversely, we shall show that if `P` is regular,
then `P.RankFunction ℕ` is non empty (TODO @joelriou).

(We also introduce similar definitions for the structure `PairingCore`.)


## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
  (α : Type v) [PartialOrder α]

/-- A rank function for a pairing is a function from the type (II) simplices
to a partially ordered type which maps ancestrality relations to strict inequalities. -/
structure RankFunction where
  /-- the rank function -/
  rank : P.II → α
  lt {x y : P.II} : P.AncestralRel x y → rank x < rank y

namespace RankFunction

variable {P α} [WellFoundedLT α] (f : P.RankFunction α)

include f

lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun ⟨g, hg⟩ ↦ not_strictAnti_of_wellFoundedLT (f.rank ∘ g)
    (strictAnti_nat_of_succ_lt (fun n ↦ f.lt (hg n)))⟩

lemma isRegular [P.IsProper] : P.IsRegular where
  wf := f.wf_ancestralRel

end RankFunction

/-- A weak rank function for a pairing is a function from the type (II) simplices
to a partially ordered type which maps an ancestrality relation between
simplices of the same dimension to a strict inequality. -/
structure WeakRankFunction where
  /-- the (weak) rank function -/
  rank : P.II → α
  lt {x y : P.II} : P.AncestralRel x y → x.1.dim = y.1.dim → rank x < rank y

namespace WeakRankFunction

variable {P α} [WellFoundedLT α] [P.IsProper] (f : P.WeakRankFunction α)

include f

lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ :=
    (wellFoundedGT_iff_monotone_chain_condition (α := ℕᵒᵈ)).1
      inferInstance ⟨fun n ↦ (g n).1.dim,
        monotone_nat_of_le_succ (fun n ↦ (hg n).dim_le)⟩
  dsimp at hn₀
  refine not_strictAnti_of_wellFoundedLT (fun n ↦ f.rank (g (n₀ + n)))
    (strictAnti_nat_of_succ_lt (fun n ↦ ?_))
  rw [← add_assoc]
  exact f.lt (hg _) (by rw [← hn₀ (n₀ + n + 1) (by omega), ← hn₀ (n₀ + n) (by omega)])

lemma isRegular : P.IsRegular where
  wf := f.wf_ancestralRel

end WeakRankFunction

/-- The weak rank function attached to a rank function. -/
@[simps]
def RankFunction.toWeakRankFunction (f : P.RankFunction α) :
    P.WeakRankFunction α where
  rank := f.rank
  lt h _ := f.lt h

end Pairing

namespace PairingCore

variable {X : SSet.{u}} {A : X.Subcomplex} (h : A.PairingCore)
  (α : Type v) [PartialOrder α]

/-- A rank function for `h : A.PairincgCore` is a function from the index type `h.ι`
to a partially ordered type which maps the ancestrality relations to strict inequalities. -/
structure RankFunction where
  /-- the rank function -/
  rank : h.ι → α
  lt {x y : h.ι} : h.AncestralRel x y → rank x < rank y

/-- A weak rank function `h : A.PairingCore` is a function from the index type `h.ι`
to a partially ordered type which maps an ancestrality relation between
indices of the same dimension to a strict inequality. -/
structure WeakRankFunction where
  /-- the (weak) rank function -/
  rank : h.ι → α
  lt {x y : h.ι} : h.AncestralRel x y → h.d x = h.d y → rank x < rank y

/-- Rank functions for `h : A.PairingCore` correspond to
rank functions for `h.pairing : A.Pairing`. -/
noncomputable def rankFunctionEquiv :
    h.RankFunction α ≃ h.pairing.RankFunction α where
  toFun f :=
    { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := by
        rw [ancestralRel_iff] at hxy
        exact g.lt hxy }
  left_inv _ := by simp
  right_inv _ := by simp

/-- Weak rank functions for `h : A.PairingCore` correspond to
weak rank functions for `h.pairing : A.Pairing`. -/
noncomputable def weakRankFunctionEquiv :
    h.WeakRankFunction α ≃ h.pairing.WeakRankFunction α where
  toFun f :=
    { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := by
        rw [ancestralRel_iff] at hxy
        exact g.lt hxy }
  left_inv _ := by simp
  right_inv _ := by simp

end PairingCore

end SSet.Subcomplex
