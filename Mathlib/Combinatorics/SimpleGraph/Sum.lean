/-
Copyright (c) 2022 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Disjoint sum of graphs

This file defines the disjoint sum of graphs. The disjoint sum of `G : SimpleGraph V` and
`H : SimpleGraph W` is a graph on `V ⊕ W` where `u` and `v` are adjacent if and only if they are
both in `G` and adjacent in `G`, or they are both in `H` and adjacent in `H`.

## Main declarations

* `SimpleGraph.Sum`: The disjoint sum of graphs.

## Notation

* `G ⊕g H`: The disjoint sum of `G` and `H`.
-/

@[expose] public section

namespace SimpleGraph
variable {U U' V V' W W' γ : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph U}
  {G' : SimpleGraph V'} {H' : SimpleGraph W'} {I' : SimpleGraph U'} {v v' : V} {w w' : W}

/-- Disjoint sum of `G` and `H`. -/
@[simps!]
protected def sum (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => false
  symm.symm
    | Sum.inl u, Sum.inl v => G.adj_symm
    | Sum.inr u, Sum.inr v => H.adj_symm
    | Sum.inl _, Sum.inr _ | Sum.inr _, Sum.inl _ => id

@[inherit_doc] infixl:60 " ⊕g " => SimpleGraph.sum

theorem sum_adj_inl : (G ⊕g H).Adj (.inl v) (.inl v') ↔ G.Adj v v' := by
  simp

theorem sum_adj_inr : (G ⊕g H).Adj (.inr w) (.inr w') ↔ H.Adj w w' := by
  simp

/-- The disjoint sum is commutative up to isomorphism. `Iso.sumComm` as a graph isomorphism. -/
@[simps!]
def Iso.sumComm : G ⊕g H ≃g H ⊕g G := ⟨Equiv.sumComm V W, by
  rintro (u | u) (v | v) <;> simp⟩

/-- The disjoint sum is associative up to isomorphism. `Iso.sumAssoc` as a graph isomorphism. -/
@[simps!]
def Iso.sumAssoc : (G ⊕g H) ⊕g I ≃g G ⊕g (H ⊕g I) where
  toEquiv := .sumAssoc ..
  map_rel_iff' := by rintro ((u | u) | u) ((v | v) | v) <;> simp

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

/-- Given homomorphisms `f : G →g G'` and `g : H →g H'`, returns a homomorphism from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps]
def Hom.sum (f : G →g G') (g : H →g H') : G ⊕g H →g G' ⊕g H' where
  toFun := Sum.map f g
  map_rel' {u v} := by cases u <;> cases v <;> simp_all [f.map_rel, g.map_rel]

lemma Hom.sum_comp_sumComm (f : G →g G') (g : H →g H') :
    comp (sum f g) Iso.sumComm.toHom = comp Iso.sumComm.toHom (sum g f) := by
  ext (v | w) <;> simp

lemma Hom.sum_sum_comp_sumAssoc (f : G →g G') (g : H →g H') (h : I →g I') :
    comp (sum f (sum g h)) Iso.sumAssoc.toHom = comp Iso.sumAssoc.toHom (sum (sum f g) h) := by
  ext ((v | w) | u) <;> simp

/-- Given embeddings `f : G ↪g G'` and `g : H ↪g H'`, returns an embedding from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps]
def Embedding.sum (f : G ↪g G') (g : H ↪g H') : G ⊕g H ↪g G' ⊕g H' where
  toFun := Sum.map f g
  inj' u v := by cases u <;> cases v <;> simp
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp

lemma Embedding.toHom_sum (f : G ↪g G') (g : H ↪g H') :
    (Embedding.sum f g).toHom = Hom.sum f.toHom g.toHom := rfl

lemma Embedding.sum_comp_sumComm (f : G ↪g G') (g : H ↪g H') :
    comp (sum g f) Iso.sumComm.toEmbedding = comp Iso.sumComm.toEmbedding (sum f g) := by
  ext (v | w) <;> simp

lemma Embedding.sum_sum_comp_sumAssoc (f : G ↪g G') (g : H ↪g H') (h : I ↪g I') :
    comp (sum f (sum g h)) Iso.sumAssoc.toEmbedding =
      comp Iso.sumAssoc.toEmbedding (sum (sum f g) h) := by
  ext ((v | w) | u) <;> simp

/-- Given isomorphisms `f : G ≃g G'` and `g : H ≃g H'`, returns an isomorphism from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps!, simps toEquiv]
def Iso.sumCongr (f : G ≃g G') (g : H ≃g H') : G ⊕g H ≃g G' ⊕g H' where
  toEquiv := f.toEquiv.sumCongr g.toEquiv
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp [f.map_rel_iff, g.map_rel_iff]

lemma Iso.toHom_sumCongr (f : G ≃g G') (g : H ≃g H') :
    (Iso.sumCongr f g).toHom = Hom.sum f.toHom g.toHom := rfl

lemma Iso.toEmbedding_sumCongr (f : G ≃g G') (g : H ≃g H') :
    (Iso.sumCongr f g).toEmbedding = Embedding.sum f.toEmbedding g.toEmbedding := rfl

lemma Iso.sumComm_comp_sumCongr (f : G ≃g G') (g : H ≃g H') :
    comp sumComm (sumCongr f g) = comp (sumCongr g f) sumComm := by
  ext (v | w) <;> simp

lemma Iso.sumAssoc_comp_sumCongr (f : G ≃g G') (g : H ≃g H') (h : I ≃g I') :
    comp sumAssoc (sumCongr (sumCongr f g) h) = comp (sumCongr f (sumCongr g h)) sumAssoc := by
  ext ((v | w) | u) <;> simp

/-- The edges of the disjoint sum of `G` and `H` are in bijection with
the disjoint sum of the edges of `G` and the edges of `H` -/
def edgeSetSumEquiv : (G ⊕g H).edgeSet ≃ G.edgeSet ⊕ H.edgeSet where
  toFun :=
    fun ⟨e, he⟩ ↦ e.fromRelNdrec (sym := symm _) he (fun
      | Sum.inl u, Sum.inl v, h => .inl ⟨s(u, v), h⟩
      | Sum.inr u, Sum.inr v, h => .inr ⟨s(u, v), h⟩
      | Sum.inl u, Sum.inr v, h => by contradiction
      | Sum.inr u, Sum.inl v, h => by contradiction
    ) fun a b h ↦ by cases a <;> cases b <;> simp
  invFun
    | Sum.inl ⟨e, he⟩ =>
      e.fromRelNdrec (sym := G.symm) he (fun u v h ↦ ⟨s(.inl u, .inl v), h⟩) <| by simp
    | Sum.inr ⟨e, he⟩ =>
      e.fromRelNdrec (sym := H.symm) he (fun u v h ↦ ⟨s(.inr u, .inr v), h⟩) <| by simp
  left_inv := by rintro ⟨⟨u | u, v | v⟩, h⟩ <;> first | contradiction | rfl
  right_inv := by rintro (⟨⟨u, v⟩, h⟩ | ⟨⟨u, v⟩, h⟩) <;> rfl

lemma not_adj_sum_inl_inr (v w) : ¬(G ⊕g H).Adj (.inl v) (.inr w) := by simp

lemma not_reachable_sum_inl_inr (v w) : ¬(G ⊕g H).Reachable (.inl v) (.inr w) := by
  rintro ⟨p⟩
  have hs : ∀ x : V ⊕ W, x ∉ Set.range .inl ↔ x ∈ Set.range .inr := by simp
  obtain ⟨⟨d, hadj⟩, _, hd1, hd2⟩ := p.exists_boundary_dart (Set.range .inl) (by simp) (by simp)
  simp only [hs] at hadj hd1 hd2
  obtain ⟨v', hv'⟩ := hd1
  obtain ⟨w', hw'⟩ := hd2
  rw [← hv', ← hw'] at hadj
  exact not_adj_sum_inl_inr _ _ hadj

lemma not_preconnected_sum [Nonempty V] [Nonempty W] : ¬(G ⊕g H).Preconnected :=
  fun h ↦ not_reachable_sum_inl_inr (Classical.arbitrary _) (Classical.arbitrary _) (h ..)

lemma not_connected_sum [Nonempty V] [Nonempty W] : ¬(G ⊕g H).Connected := by
  simp [connected_iff, not_preconnected_sum]

lemma Reachable.sum_sup_edge (hv : G.Reachable v v') (hw : H.Reachable w w') :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Reachable (.inl v') (.inr w') :=
  ((hv.symm.map Embedding.sumInl.toHom).mono le_sup_left).trans <| .trans
    (Adj.reachable <| by simp [edge]) <| (hw.map Embedding.sumInr.toHom).mono le_sup_left

lemma Preconnected.sum_sup_edge (hG : G.Preconnected) (hH : H.Preconnected) :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Preconnected := by
  rintro (v₁ | w₁) (v₂ | w₂)
  · exact ((hG v₁ v₂).map Embedding.sumInl.toHom).mono le_sup_left
  · exact (hG ..).sum_sup_edge (hH ..)
  · exact ((hG ..).sum_sup_edge (hH ..)).symm
  · exact ((hH w₁ w₂).map Embedding.sumInr.toHom).mono le_sup_left

lemma Connected.sum_sup_edge (hG : G.Connected) (hH : H.Connected) :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Connected := by
  obtain ⟨hG⟩ := hG; exact ⟨hG.sum_sup_edge hH.preconnected⟩

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

lemma neighborSet_sum_inl (v : V) : (G ⊕g H).neighborSet (.inl v) = Sum.inl '' G.neighborSet v := by
  ext (v' | w') <;> simp

lemma neighborSet_sum_inr (w : W) : (G ⊕g H).neighborSet (.inr w) = Sum.inr '' H.neighborSet w := by
  ext (v' | w') <;> simp

instance [DecidableEq V] [DecidableEq W] [LocallyFinite G] [LocallyFinite H] :
    LocallyFinite (G ⊕g H) := by
  rintro (v | w) <;> simp only [neighborSet_sum_inl, neighborSet_sum_inr] <;>
    infer_instance

end SimpleGraph
