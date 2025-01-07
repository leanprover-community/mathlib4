/-
Copyright (c) 2025 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.Util.Superscript

namespace SSet.Truncated

/-- Some quick attempts to prove that `[m]` is `n`-truncated (`m ≤ n`). -/
macro "trunc" : tactic =>
  `(tactic| first | decide | assumption | apply zero_le | apply le_rfl |
    simp only [SimplexCategory.len_mk]; omega)

/-- For `X : SSet.Truncated n` and `m ≤ n`, `X _[m]ₙ` is the type of `m`-simplices in `X`. -/
scoped macro:1000 (priority := high)
  X:term " _[" m:term "]"n:subscript(term) : term =>
  `(($X : SSet.Truncated $(⟨n.raw[0]⟩)).obj (Opposite.op ⟨SimplexCategory.mk $m,
    by first | trunc | fail "Failed to prove SSet.Truncated property."⟩))

/-- For `X : SSet.Truncated n` and `p : m ≤ n`, `X _[m, p]ₙ` is the type of `m`-simplices in `X`. -/
scoped macro:1000 (priority := high)
  X:term " _[" m:term "," p:term "]"n:subscript(term) : term =>
    `(($X : SSet.Truncated $(⟨n.raw[0]⟩)).obj
      (Opposite.op ⟨SimplexCategory.mk $m, $p⟩))

end SSet.Truncated

namespace SimplexCategory.Truncated
open CategoryTheory SimplexCategory

/-- The truncated form of the inclusion functor. -/
def incl {n m : ℕ} (h : n ≤ m) : Truncated n ⥤ Truncated m where
  obj a := ⟨a.1, a.2.trans h⟩
  map := id

lemma incl_comp_inclusion {n m : ℕ} (h : n ≤ m) : incl h ⋙ inclusion m = inclusion n := rfl

end SimplexCategory.Truncated

universe v u

namespace SimplicialObject.Truncated
open CategoryTheory SimplicialObject

variable (C : Type u) [Category.{v} C]

/-- The truncated form of the truncation functor. -/
def trunc {n m : ℕ} (h : n ≤ m) : Truncated C m ⥤ Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl h).op

lemma truncation_comp_trunc {n m : ℕ} (h : n ≤ m) : truncation m ⋙ trunc C h = truncation n := rfl

end SimplicialObject.Truncated

namespace SSet.Truncated
open CategoryTheory SimplexCategory Simplicial

/-- The truncated form of the truncation functor. -/
def trunc {n m : ℕ} (h : n ≤ m) : Truncated m ⥤ Truncated n :=
  SimplicialObject.Truncated.trunc (Type u) h

lemma truncation_comp_trunc {n m : ℕ} (h : n ≤ m) : truncation m ⋙ trunc h = truncation n := rfl

/-- A path of length `n` in a 1-truncated simplicial set is a directed path of `n` edges. -/
@[ext]
structure Path₁ (X : Truncated.{u} 1) (n : ℕ) where
  vertex (i : Fin (n + 1)) : X _[0]₁
  arrow (i : Fin n) : X _[1]₁
  arrow_src (i : Fin n) : X.map (δ 1).op (arrow i) = vertex i.castSucc
  arrow_tgt (i : Fin n) : X.map (δ 0).op (arrow i) = vertex i.succ

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- A path in any `n + 1`-truncated simplicial set `X` is defined by further 1-truncating `X`, then
taking the 1-truncated path. -/
abbrev Path : ℕ → Type u := trunc (by omega) |>.obj X |>.Path₁

/-- The spine of an `n + 1`-simplex in an `n + 1`-truncated simplicial set `X` is the path of edges
of length `n + 1` formed by traversing through its vertices in order. -/
def spine {m} (hmn : m ≤ n + 1) (Δ : X _[m]ₙ₊₁) : Path X m where
  vertex i := X.map (SimplexCategory.const [0] [m] i).op Δ
  arrow i := X.map (SimplexCategory.mkOfSucc i).op Δ
  arrow_src i := by
    erw [← FunctorToTypes.map_comp_apply, ← op_comp (f := (δ 1).op.unop)]
    simp
  arrow_tgt i := by
    erw [← FunctorToTypes.map_comp_apply, ← op_comp (f := (δ 0).op.unop)]
    simp

/-- An `n + 1`-truncated simplicial set satisfies the strict Segal condition if its
`n + 1`-simplices are uniquely determined by their spine. -/
class StrictSegal where
  spineToSimplex {m : ℕ} (hmn : m ≤ n + 1) : Path X m → X _[m]ₙ₊₁
  spine_spineToSimplex {m : ℕ} (hmn : m ≤ n + 1) : X.spine hmn ∘ spineToSimplex hmn = id
  spineToSimplex_spine {m : ℕ} (hmn : m ≤ n + 1) : spineToSimplex hmn ∘ X.spine hmn = id

end SSet.Truncated

namespace SSet
open Truncated CategoryTheory SimplexCategory Simplicial

variable (X : SSet.{u})

/-- A path in a simplicial set is defined by 1-truncating, then taking the
1-truncated path. -/
abbrev Path : ℕ → Type u := truncation 1 |>.obj X |>.Path₁

/-- The spine of an `n + 1` simplex in `X` is the path of edges of length
`n + 1` formed by traversing in order through the vertices of the `n + 1`
truncation. -/
abbrev spine {n : ℕ} : X _[n + 1] → X.Path (n + 1) :=
  truncation (n + 1) |>.obj X |>.spine (Nat.le_refl _)

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices
are uniquely determined by their spine. -/
-- TODO: can we define this directly in terms of `Truncated.StrictSegal`?
class StrictSegal where
  spineToSimplex {n : ℕ} : Path X (n + 1) → X _[n + 1]
  spine_spineToSimplex {n : ℕ} : X.spine (n := n) ∘ spineToSimplex = id
  spineToSimplex_spine {n : ℕ} : spineToSimplex ∘ X.spine (n := n) = id

instance strictSegal_of_strictSegal
    [∀ n : ℕ, Truncated.StrictSegal ((truncation (n + 1)).obj X)] :
    StrictSegal X where
  spineToSimplex {n} :=
    Truncated.StrictSegal.spineToSimplex (X := (truncation (n + 1)).obj X) (Nat.le_refl _)
  spine_spineToSimplex {n} :=
    Truncated.StrictSegal.spine_spineToSimplex (Nat.le_refl _)
  spineToSimplex_spine {n} :=
    Truncated.StrictSegal.spineToSimplex_spine (Nat.le_refl _)

end SSet

namespace SSet.Truncated.StrictSegal

variable {n} {X : SSet.Truncated.{u} (n + 1)} [StrictSegal X]

/-- The fields of `StrictSegal` define an equivalence between `X [m]ₙ₊₁` and `Path X m`.-/
def spineEquiv {m : ℕ} (hmn : m ≤ n + 1) : X _[m]ₙ₊₁ ≃ Path X m where
  toFun := spine X hmn
  invFun := spineToSimplex hmn
  left_inv := by
    exact congrFun (spineToSimplex_spine (X := X) hmn)
  right_inv := by
    exact congrFun (spine_spineToSimplex (X := X) hmn)

end SSet.Truncated.StrictSegal
