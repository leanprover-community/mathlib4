/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Mathlib.Combinatorics.SerreGraph.Covering
import Mathlib.Combinatorics.SerreGraph.ReducedPaths

/-!
## Construction of the Universal covering of Serre Graphs

We construct the universal cover given a baspoint `x₀` with

* Vertices: reduced edge paths starting at `x₀`
* Edges: reduces edge paths starting at `x₀` followed by an edge.

The non-trivial part is the construction of the `bar` map.
The initial vertex should be the terminal vertex of the given edge.
This is obtained by reduced concat, using the fact that the
result is reduced. The other result is used to show that
the `bar` map is an involution.
-/

namespace SerreGraph

open EdgePath PathClass

universe u v

variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

namespace UniversalCover

variable (G: SerreGraph V E) (x₀ : V)

/--
The vertices of the universal cover: reduced edge paths
starting at `x₀`.
-/
@[ext]
structure Vert where
  /-- Terminal vertex of the reduced path -/
  τ : V
  /-- The reduced path -/
  p : EdgePath G x₀ τ
  is_reduced : @reduced V E G x₀ τ p
deriving DecidableEq

/--
The edges of the universal cover: reduced edge paths
starting at `x₀` followed by an edge.
-/
@[ext]
structure Edge where
  /-- The terminal vertex of the reduced edge path -/
  τ₀ : V
  /-- The terminal vertex of the edge -/
  τ₁ : V
  /-- The edge between the terminal vertices -/
  nxt: EdgeBetween G τ₀ τ₁
  /-- The reduced path -/
  p : EdgePath G x₀ τ₀
  is_reduced : reduced p


namespace Edge

/--
The initial vertex of an edge in the universal cover
is the terminal vertex of the reduced path.
-/
def initial (e : Edge G x₀) : Vert G x₀ :=
  ⟨e.τ₀, e.p, e.is_reduced⟩

/--
The terminal vertex of an edge in the univeral cover
is the terminal vertex of the edge.
-/
def terminal (e : Edge G x₀) : Vert G x₀ :=
  ⟨e.τ₁, e.p :+ e.nxt, reducedConcat_reduced e.p e.nxt e.is_reduced⟩

/--
The involution on the edges of the universal cover.
-/
def bar (e : Edge G x₀) : Edge G x₀ :=
  ⟨e.τ₁, e.τ₀, e.nxt.bar, e.p :+ e.nxt,  reducedConcat_reduced e.p e.nxt e.is_reduced⟩


theorem bar_bar (e : Edge G x₀) :
    bar G x₀ (bar G x₀ e) = e := by
  simp only [bar, EdgeBetween.bar_bar]
  ext
  · rfl
  · rfl
  · rfl
  · simp only [Eq.ndrec, id_eq, heq_eq_eq]
    apply reducedConcat_cancel_pair
    exact e.is_reduced

/--
The list of edges of a path in the universal cover.
-/
def toList (e : Edge G x₀) : List E :=
  e.p.toList

theorem bar_neq_self (e: Edge G x₀) :
    e ≠ bar G x₀ e := by
  intro contra
  have : e.p.toList.length =  (bar G x₀ e).p.toList.length := by
      rw [← contra]
  simp [bar, Edge.p] at this
  let h' := concat_parity e.p e.nxt
  rw [this] at h'
  symm at h'
  let h'' := not_iff_self  h'
  assumption

/--
The universal cover of a Serre graph.
-/
def _root_.SerreGraph.univ : SerreGraph (Vert G x₀) (Edge G x₀) where
  ι := initial G x₀
  bar := bar G x₀
  bar_bar := bar_bar G x₀
  bar_ne_self := bar_neq_self G x₀

theorem bar_eq_bar (τ₀ τ₁ : V)
    (nxt: EdgeBetween G τ₀ τ₁)
    (p : EdgePath G x₀ τ₀)
    (is_reduced : reduced p) :
    (univ G x₀).bar ⟨τ₀, τ₁,  nxt, p, is_reduced⟩ =
    ⟨τ₁, τ₀, nxt.bar, p :+ nxt, reducedConcat_reduced p nxt is_reduced⟩ := rfl

theorem init_defn (τ₀ τ₁ : V)
    (nxt: EdgeBetween G τ₀ τ₁)
    (p : EdgePath G x₀ τ₀)
    (is_reduced : reduced p) :
    (univ G x₀).ι ⟨τ₀, τ₁,  nxt, p, is_reduced⟩  =
    ⟨τ₀, p, is_reduced⟩ := rfl

theorem terminal_defn (τ₀ τ₁ : V)
    (nxt: EdgeBetween G τ₀ τ₁)
    (p : EdgePath G x₀ τ₀)
    (is_reduced : reduced p) :
    (univ G x₀).τ ⟨τ₀, τ₁,  nxt, p, is_reduced⟩  =
    ⟨τ₁, p :+ nxt, reducedConcat_reduced p nxt is_reduced⟩ := rfl

theorem nxt_defn (τ₀ τ₁ : V)
    (nxt: EdgeBetween G τ₀ τ₁)
    (p : EdgePath G x₀ τ₀)
    (is_reduced : reduced p) :
    (⟨τ₀, τ₁,  nxt, p, is_reduced⟩ : Edge G x₀).nxt = nxt := rfl

end Edge

open Edge

/--
The projection map from the universal cover to the Serre graph.
-/
def proj : Morphism (G.univ x₀) G where
  toFuncV := Vert.τ
  toFuncE := fun e ↦ e.nxt.edge
  toFuncV_init := by
    intro e
    match e with
    | ⟨τ₀, τ₁, nxt, _, _⟩ =>
      simp only [init_defn, nxt.init_eq]
  toFuncE_bar := by
    intro e
    rfl

lemma shift_heq (τ₀ τ₁ τ₂ : V)(edge : E)(init_eq : G.ι edge = τ₀)
    (term_eq₁ : G.τ edge = τ₁)(term_eq₂ : G.τ edge = τ₂):
    HEq (⟨edge, init_eq, term_eq₁⟩ : EdgeBetween G τ₀ τ₁)
      (⟨edge, init_eq, term_eq₂⟩ : EdgeBetween G τ₀ τ₂) := by
    cases term_eq₁
    cases term_eq₂
    rfl

/--
The covering map structure on the projection
from the universal cover to the Serre graph.
-/
instance : CoveringMap (proj G x₀) where
  localSection :=
    fun v₁ e h ↦
      ⟨v₁.τ, G.τ e, ⟨e, Eq.symm h, rfl⟩, v₁.p, v₁.is_reduced⟩
  init_localSection := by
    intro v₁ e h
    rfl
  toFuncE_localSection := by
    intro v₁ e h
    rfl
  localSection_toFuncE := by
    intro v₁ e₁ h₁
    have l: G.τ ((proj G x₀).toFuncE e₁) = e₁.τ₁ := by
      simp [← e₁.nxt.term_eq]
      rfl
    cases e₁
    cases h₁
    ext
    · rfl
    · rw [← l]
    · simp only [nxt_defn]
      apply shift_heq
    · rfl

/--
The basepoint in the universal cover.
-/
def basepoint : Vert G x₀  :=
  ⟨x₀, EdgePath.nil _, reduced_nil⟩

/--
Ray to the vetex in the universal cover corresponding to the reverse of
a reduced path `p`, starting at the basepoint.
-/
def rayToRev (G: SerreGraph V E)(x₀ τ : V)(p : EdgePath G τ x₀)
    (hyp : reduced p.reverse)  :
    EdgePath  (G.univ x₀) (basepoint G x₀) ⟨τ, p.reverse, hyp⟩ := by
  match p, hyp with
  | nil _,  hyp => apply nil
  | cons e p', hyp' =>
    rename_i x₀' u
    have red_cons : reduced (cons e p') := by
      rw [← reverse_reverse (cons e p')]
      apply reverse_reduced
      assumption
    have red_p' : reduced p' := by
      apply tail_reduced e p' red_cons
    have red' : reduced p'.reverse := by
      apply reverse_reduced
      assumption
    have init := rayToRev G x₀ u p' red'
    apply init.concat
    exact ⟨⟨u, τ, e.bar, p'.reverse, red'⟩, rfl, (by
      simp [terminal_defn, reducedConcat]
      congr
      apply redCons_eq_cons_of_reduced
      assumption)⟩

theorem rayToRev_proj_list (G: SerreGraph V E)(x₀ τ : V)
    (p : EdgePath G τ x₀)
    (hyp : reduced p.reverse) :
    (rayToRev G x₀ τ p hyp).toList.map (fun e ↦ e.nxt.edge) =
    p.toList.reverse.map (G.bar) := by
  induction p with
  | nil _ =>
    simp [rayToRev, nil_toList]
  | cons e p' ih =>
    rename_i x₀' u u'
    have red_cons : reduced (cons e p') := by
      rw [← reverse_reverse (cons e p')]
      apply reverse_reduced
      assumption
    have red_p' : reduced p' := by
      apply tail_reduced e p'
      assumption
    have red' : reduced p'.reverse := by
      apply reverse_reduced
      assumption
    simp [rayToRev, cons_toList, concat_toList, ih red']

/--
Ray to the vetex in the universal cover corresponding to a
reduced path `p`, starting at the basepoint.
-/
def rayTo (G: SerreGraph V E)(x₀ τ : V)(p : EdgePath G x₀ τ)
    (hyp : reduced p)  :
    EdgePath  (G.univ x₀) (basepoint G x₀) ⟨τ, p, hyp⟩ := by
  let ray := rayToRev G x₀ τ p.reverse
    (by simp [reverse_reverse, hyp])
  apply shiftTarget ray
  simp [reverse_reverse]


theorem rayTo_proj_list (G: SerreGraph V E)(x₀ τ : V)(p : EdgePath G x₀ τ)
    (hyp : reduced p) :
    (rayTo G x₀ τ p hyp).toList.map (fun e ↦ e.nxt.edge) =
      p.toList := by
  simp [rayTo, toList_shiftTarget, rayToRev_proj_list,
    reverse_toList, List.map_reverse]
  have : G.bar ∘ G.bar = id := by
    funext x
    simp only [Function.comp, bar_bar, id_eq]
  simp [this]

/--
Lift of a reduced path `p` to the universal cover.
This is the ray to the vertex corresponding to `p`.
-/
def rayLift (G: SerreGraph V E)(x₀ τ : V)(p : EdgePath G x₀ τ)
    (hyp : reduced p) : PathLift (proj G x₀) (basepoint G x₀)
    rfl p := {
  τ := ⟨τ, p, hyp⟩
  path := rayTo G x₀ τ p hyp
  term_pushdown := rfl
  list_pushdown := by
    simp [proj]
    simp [rayTo_proj_list]
  }

theorem lift_of_reduced {G: SerreGraph V E}{x₀ τ: V}(p : EdgePath G x₀ τ)
    (hyp : reduced p) :
    p.lift (proj G x₀) (basepoint G x₀) rfl =
      rayLift G x₀ τ p hyp := by
      apply unique_Pathlift

theorem reduced_liftTerminal {G: SerreGraph V E}{x₀ τ: V}
    (p : EdgePath G x₀ τ)
    (hyp : reduced p) :
    liftTerminal (proj G x₀) (basepoint G x₀)  rfl p =
      ⟨τ, p, hyp⟩ := by
      simp [liftTerminal, liftClass, lift_of_reduced p hyp, rayLift]
      rfl

theorem reduced_unique {G: SerreGraph V E}(x₀ τ: V)
    {p₁ p₂ : EdgePath G x₀ τ}
    (hyp₁ : reduced p₁)(hyp₂ : reduced p₂):
    [[ p₁ ]] = [[ p₂ ]] → p₁ = p₂ := by
  intro hyp
  have leq :
    liftTerminal (proj G x₀) (basepoint G x₀) rfl p₁ =
    liftTerminal (proj G x₀) (basepoint G x₀) rfl p₂ := by
    simp [liftTerminal]
    apply congrArg
    apply liftClass_eq_of_homotopic
    assumption
  simp [reduced_liftTerminal p₁ hyp₁, reduced_liftTerminal p₂ hyp₂] at leq
  exact leq

theorem homotopic_iff_reduction_eq {G: SerreGraph V E}(x₀ τ: V)
    (p₁ p₂ : EdgePath G x₀ τ):
    [[ p₁ ]] = [[ p₂ ]] ↔ reduction p₁ = reduction p₂ := by
  apply Iff.intro
  · intro eql
    rw [← reduction_homotopic_self p₁, ← reduction_homotopic_self p₂] at eql
    have red₁ : reduced (reduction p₁) := by
      apply reduction_reduced
    have red₂ : reduced (reduction p₂) := by
      apply reduction_reduced
    exact reduced_unique x₀ τ red₁ red₂ eql
  · intro hyp
    rw [← reduction_homotopic_self p₁, ← reduction_homotopic_self p₂]
    rw [hyp]

theorem homotopic_of_liftTerminal_eq  {G: SerreGraph V E}{x₀ τ: V}
    {p₁ p₂ : EdgePath G x₀ τ} :
    liftTerminal (proj G x₀) (basepoint G x₀) rfl p₁ =
        liftTerminal (proj G x₀) (basepoint G x₀) rfl p₂ →
    [[ p₁ ]] = [[ p₂ ]] := by
  intro hyp
  have red₁ :  [[ reduction p₁ ]] = [[ p₁ ]] := by
    apply reduction_homotopic_self
  have red₂ :  [[ reduction p₂ ]] = [[ p₂ ]] := by
    apply reduction_homotopic_self
  let l₁ :=
    liftTerminal_eq_of_homotopic (proj G x₀) (basepoint G x₀)  rfl red₁
  let _l₂ :=
    liftTerminal_eq_of_homotopic (proj G x₀) (basepoint G x₀)  rfl red₂
  rw [← l₁, ← _l₂] at hyp
  rw [reduced_liftTerminal (reduction p₁) (reduction_reduced p₁)] at hyp
  rw [reduced_liftTerminal (reduction p₂) (reduction_reduced p₂)] at hyp
  simp at hyp
  rw [homotopic_iff_reduction_eq]
  exact hyp

theorem proj_liftTerminal {G: SerreGraph V E}{x₀: V}{vert : Vert G x₀}
    (e: EdgePath (G.univ x₀) (basepoint G x₀) vert) :
    liftTerminal (proj G x₀) (basepoint G x₀) rfl
      (e.map (proj G x₀)) = vert := by
  simp [liftTerminal, liftClass]
  simp [lift_of_proj]
  rfl

theorem simple_connectivity_for_paths {G: SerreGraph V E}{x₀: V}
    {vert : Vert G x₀}
    (e₁ e₂: EdgePath (G.univ x₀) (basepoint G x₀) vert) :
    [[ e₁ ]] = [[ e₂ ]] := by
  apply proj_injective (proj G x₀)
  let lem :
    liftTerminal (proj G x₀) (basepoint G x₀) rfl
      (e₁.map (proj G x₀)) =
    liftTerminal (proj G x₀) (basepoint G x₀) rfl
      (e₂.map (proj G x₀)) := by
    rw [proj_liftTerminal e₁, proj_liftTerminal e₂]
  apply homotopic_of_liftTerminal_eq lem
