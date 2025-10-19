/-
Copyright (c) 2022 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Disjoint sum of graphs

This file defines the disjoint sum of graphs. The disjoint sum of `G : SimpleGraph α` and
`H : SimpleGraph β` is a graph on `α ⊕ β` where `u` and `v` are adjacent if and only if they are
both in `G` and adjacent in `G`, or they are both in `H` and adjacent in `H`.

## Main declarations

* `SimpleGraph.Sum`: The disjoint sum of graphs.

## Notation

* `G ⊕g H`: The disjoint sum of `G` and `H`.
-/

variable {α β γ : Type*}

namespace SimpleGraph

/-- Disjoint sum of `G` and `H`. -/
@[simps!]
protected def sum (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => false
  symm
    | Sum.inl u, Sum.inl v => G.adj_symm
    | Sum.inr u, Sum.inr v => H.adj_symm
    | Sum.inl _, Sum.inr _ | Sum.inr _, Sum.inl _ => id
  loopless u := by cases u <;> simp

@[inherit_doc] infixl:60 " ⊕g " => SimpleGraph.sum

variable {G : SimpleGraph α} {H : SimpleGraph β}

/-- The disjoint sum is commutative up to isomorphism. `Iso.sumComm` as a graph isomorphism. -/
@[simps!]
def Iso.sumComm : G ⊕g H ≃g H ⊕g G := ⟨Equiv.sumComm α β, by
  rintro (u | u) (v | v) <;> simp⟩

/-- The disjoint sum is associative up to isomorphism. `Iso.sumAssoc` as a graph isomorphism. -/
@[simps!]
def Iso.sumAssoc {I : SimpleGraph γ} : (G ⊕g H) ⊕g I ≃g G ⊕g (H ⊕g I) := ⟨Equiv.sumAssoc α β γ, by
  rintro ((u | u) | u) ((v | v) | v) <;> simp⟩

/-- The embedding of `G` into `G ⊕g H`. -/
@[simps]
def Embedding.sumInl : G ↪g G ⊕g H where
  toFun u := _root_.Sum.inl u
  inj' u v := by simp
  map_rel_iff' := by simp

/-- The embedding of `H` into `G ⊕g H`. -/
@[simps]
def Embedding.sumInr : H ↪g G ⊕g H where
  toFun u := _root_.Sum.inr u
  inj' u v := by simp
  map_rel_iff' := by simp

/-- Color `G ⊕g H` with colorings of `G` and `H` -/
def Coloring.sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (G ⊕g H).Coloring γ where
  toFun := Sum.elim cG cH
  map_rel' {u v} huv := by cases u <;> cases v <;> simp_all [cG.valid, cH.valid]

/-- Get coloring of `G` from coloring of `G ⊕g H` -/
def Coloring.sumLeft (c : (G ⊕g H).Coloring γ) : G.Coloring γ := c.comp Embedding.sumInl.toHom

/-- Get coloring of `H` from coloring of `G ⊕g H` -/
def Coloring.sumRight (c : (G ⊕g H).Coloring γ) : H.Coloring γ := c.comp Embedding.sumInr.toHom

@[simp]
theorem Coloring.sumLeft_sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (cG.sum cH).sumLeft = cG :=
  rfl

@[simp]
theorem Coloring.sumRight_sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (cG.sum cH).sumRight = cH :=
  rfl

@[simp]
theorem Coloring.sum_sumLeft_sumRight (c : (G ⊕g H).Coloring γ) : c.sumLeft.sum c.sumRight = c := by
  ext (u | u) <;> rfl

/-- Bijection between `(G ⊕g H).Coloring γ` and `G.Coloring γ × H.Coloring γ` -/
def Coloring.sumEquiv : (G ⊕g H).Coloring γ ≃ G.Coloring γ × H.Coloring γ where
  toFun c := ⟨c.sumLeft, c.sumRight⟩
  invFun p := p.1.sum p.2
  left_inv c := by simp [sum_sumLeft_sumRight c]

/-- Color `G ⊕g H` with `Fin (n + m)` given a coloring of `G` with `Fin n` and a coloring of `H`
with `Fin m` -/
def Coloring.sumFin {n m : ℕ} (cG : G.Coloring (Fin n)) (cH : H.Coloring (Fin m)) :
    (G ⊕g H).Coloring (Fin (max n m)) := sum
  (G.recolorOfEmbedding (Fin.castLEEmb (n.le_max_left m)) cG)
  (H.recolorOfEmbedding (Fin.castLEEmb (n.le_max_right m)) cH)

theorem Colorable.sum_max {n m : ℕ} (hG : G.Colorable n) (hH : H.Colorable m) :
    (G ⊕g H).Colorable (max n m) := Nonempty.intro (hG.some.sumFin hH.some)

theorem Colorable.of_sum_left {n : ℕ} (h : (G ⊕g H).Colorable n) : G.Colorable n :=
  Nonempty.intro (h.some.sumLeft)

theorem Colorable.of_sum_right {n : ℕ} (h : (G ⊕g H).Colorable n) : H.Colorable n :=
  Nonempty.intro (h.some.sumRight)

@[simp]
theorem colorable_sum {n : ℕ} : (G ⊕g H).Colorable n ↔ G.Colorable n ∧ H.Colorable n :=
  ⟨fun cGH => ⟨cGH.of_sum_left, cGH.of_sum_right⟩,
    fun ⟨cG, cH⟩ => by rw [← n.max_self]; exact cG.sum_max cH⟩

theorem chromaticNumber_le_sum_left : G.chromaticNumber ≤ (G ⊕g H).chromaticNumber :=
  chromaticNumber_le_of_forall_imp (fun _ h ↦ h.of_sum_left)

theorem chromaticNumber_le_sum_right : H.chromaticNumber ≤ (G ⊕g H).chromaticNumber :=
  chromaticNumber_le_of_forall_imp (fun _ h ↦ h.of_sum_right)

@[simp]
theorem chromaticNumber_sum :
    (G ⊕g H).chromaticNumber = max G.chromaticNumber H.chromaticNumber := by
  refine eq_max chromaticNumber_le_sum_left chromaticNumber_le_sum_right fun {d} hG hH => ?_
  cases d with
  | top => simp
  | coe n =>
    let cG : G.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hG).some
    let cH : H.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hH).some
    exact chromaticNumber_le_iff_colorable.mpr (Nonempty.intro (cG.sum cH))

end SimpleGraph
