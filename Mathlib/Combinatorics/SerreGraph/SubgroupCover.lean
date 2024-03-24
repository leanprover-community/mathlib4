/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Mathlib.Combinatorics.SerreGraph.UniversalCover
import Mathlib.GroupTheory.Subgroup.Basic
/-!
## Covers of Serre Graphs for Subgroups of the Fundamental Group

We construct a cover corresponding to a subgroup of the
fundamental group of a Serre graph. We show that the
fundamental group of this cover is isomorphic to the subgroup.

The cover is constructed as a quotient of the universal cover.
-/

namespace SerreGraph

universe u v

namespace SubgroupCover

open EdgePath PathClass UniversalCover Edge

variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

variable {G: SerreGraph V E} {x₀ : V}

variable (H : Subgroup (π₁ G x₀))

/--
Relation on vertices of the universal cover of `G`
corresponding to the subgroup `H` of the fundamental group.
-/
abbrev rel : Vert G x₀ → Vert G x₀ → Prop
| ⟨τ₁, v₁, _⟩, ⟨τ₂, v₂, _⟩ => by
    if c:τ₁=τ₂ then
      cases c
      exact [[ v₁ ++ v₂.reverse ]] ∈ H
    else
      exact False

/--
Relation on edge-paths corresponding to lifts in the cover
corresponding to the subgroup `H` of the fundamental group
having the same terminal point.
-/
def relH {τ : V} (v₁ v₂ : EdgePath G x₀ τ) : Prop :=
  [[v₁ ++ v₂.reverse]] ∈ H


theorem relH_refl {τ : V} (v : EdgePath G x₀ τ) : relH H v v :=
  by
    simp [relH]
    apply one_mem


theorem relH_symm {τ : V} {v₁ v₂ : EdgePath G x₀ τ} :
    relH H v₁ v₂ → relH H v₂ v₁ :=by
  simp [relH]
  intro h
  let h': [[v₁ ++ v₂.reverse]].inv ∈ H := inv_mem h
  rw [inv_equiv_reverse,
    reverse_append,  reverse_reverse] at h'
  exact h'

theorem relH_trans {τ : V} {v₁ v₂ v₃ : EdgePath G x₀ τ} :
    relH H v₁ v₂ → relH H v₂ v₃ → relH H v₁ v₃ := by
  simp [relH]
  intro h₁ h₂
  let h₃  := mul_mem h₁ h₂
  rw [mul_path_path, append_assoc,
    ← append_assoc v₂.reverse, ← mul_path_path,
    ← mul_path_path] at h₃
  simp only [reverse_append_self] at h₃
  rw [mul_path_path] at h₃
  simp  [nil_append] at h₃
  rw [← mul_path_path, ← inv_equiv_reverse]
  exact h₃

/--
Setoid on vertices of the universal cover of `G`
corresponding to the subgroup `H` of the fundamental group.
-/
scoped instance vertSetoid  : Setoid (Vert G x₀) where
  r := fun ⟨τ₁, v₁, _⟩ ⟨τ₂, v₂, _⟩ => by
    if c:τ₁=τ₂ then
      cases c
      exact relH H v₁ v₂
    else
      exact False
  iseqv := by
    apply Equivalence.mk
    · intro ⟨τ₁, v₁, _⟩
      simp only [↓reduceDite, relH_refl]
    · intro ⟨τ₁, v₁, _⟩ ⟨τ₂, v₂, _⟩
      if c:τ₁=τ₂ then
      cases c
      simp only [dite_eq_ite, ite_true]
      apply relH_symm
    else
      simp only [c, dite_false, IsEmpty.forall_iff]
    · intro ⟨τ₁, v₁, _⟩ ⟨τ₂, v₂, _⟩ ⟨τ₃, v₃, _⟩
      if c₁:τ₁=τ₂ then
        cases c₁
        simp only [↓reduceDite]
        if c₂:τ₁=τ₃ then
          cases c₂
          simp only [dite_eq_ite, ite_true]
          apply relH_trans
        else
          simp [c₂]
      else
        simp [c₁]

theorem terminal_eq_of_r {v₁ v₂ : Vert G x₀ } :
    vertSetoid H |>.r v₁ v₂ → v₁.τ = v₂.τ := by
  intro h
  simp [Setoid.r] at h
  by_cases c:v₁.τ=v₂.τ <;> simp [c] at h
  simp [c]

theorem path_eq_iff_r {τ : V}(p₁ p₂ : EdgePath G x₀ τ)
    {red₁ : reduced p₁} {red₂ : reduced p₂} :
    (vertSetoid H |>.r ⟨τ, p₁, red₁⟩ ⟨τ, p₂, red₂⟩) ↔
      [[ p₁ ++ p₂.reverse ]] ∈ H := by
  simp [Setoid.r, relH]

/--
Setoid on edges of the universal cover of `G`
corresponding to the subgroup `H` of the fundamental group.
-/
scoped instance edgeSetoid : Setoid (Edge G x₀) where
  r := fun ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩ => by
    if c:τ₀=τ₀' ∧ τ₁ = τ₁' then
      cases c.left
      cases c.right
      exact (relH H p p') ∧ (e = e')
    else
      exact False
  iseqv := by
    apply Equivalence.mk
    · intro ⟨τ₀, τ₁, e, p, _⟩
      simp only [and_self, ↓reduceDite, relH_refl]
    · intro ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩
      if c:τ₀=τ₀' ∧ τ₁ = τ₁' then
      cases c.left
      cases c.right
      simp only [dite_eq_ite, ite_true]
      intro hyp
      apply And.intro
      · apply relH_symm H hyp.1
      · rw [hyp.2]
    else
      simp only [c, dite_false, IsEmpty.forall_iff]
    · intro ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩ ⟨τ₀'', τ₁'', e'', p'', _⟩
      if c₁:τ₀=τ₀' ∧ τ₁ = τ₁' then
        cases c₁.left
        cases c₁.right
        simp only [and_self, ↓reduceDite, and_imp]
        if c₂:τ₀=τ₀'' ∧ τ₁ = τ₁'' then
          cases c₂.left
          cases c₂.right
          simp only [and_self, ↓reduceDite, and_imp]
          intro hyp₁ hyp₂ hyp₃ hyp₄
          apply And.intro
          · apply relH_trans H hyp₁ hyp₃
          · rw [hyp₂, hyp₄]
        else
          simp [c₂]
      else
        simp [c₁]

theorem terminal₁_eq_of_r {e₁ e₂ : Edge G x₀ } :
    edgeSetoid H |>.r e₁ e₂ → e₁.τ₁ = e₂.τ₁ := by
  intro h
  simp [Setoid.r] at h
  by_cases c:(e₁.τ₁=e₂.τ₁) <;> simp [c] at h
  simp [c]

theorem terminal₀_eq_of_r {e₁ e₂ : Edge G x₀ } :
    edgeSetoid H |>.r e₁ e₂ → e₁.τ₀ = e₂.τ₀ := by
  intro h
  simp [Setoid.r] at h
  by_cases c:(e₁.τ₀=e₂.τ₀) <;> simp [c] at h
  simp [c]

theorem edge_eq_of_r :{e₁ e₂ : Edge G x₀ } →
    edgeSetoid H |>.r e₁ e₂ → e₁.nxt.edge = e₂.nxt.edge := by
  intro ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩
  if c:τ₀=τ₀' ∧ τ₁ = τ₁' then
    cases c.left
    cases c.right
    simp [Setoid.r, relH]
    intro _ h
    rw [h]
  else
    simp [Setoid.r, relH, c]

/--
The vertices of the cover corresponding to the subgroup `H`.
-/
def QuotVert  := Quotient (vertSetoid H)
/--
The edges of the cover corresponding to the subgroup `H`.
-/
def QuotEdge  := Quotient (edgeSetoid H)

/--
The basepoint of the cover corresponding to the subgroup `H`.
-/
def basepoint : QuotVert H  :=
  ⟦ UniversalCover.basepoint G x₀ ⟧

namespace Quot

/--
The initial point of an edge in the cover
corresponding to the subgroup `H`.
-/
def ι : Quotient (edgeSetoid H) → Quotient (vertSetoid H) := by
  apply Quotient.lift (⟦ (G.univ x₀).ι ·⟧)
  intro ⟨τ₀, τ₁, e, p, pf⟩ ⟨τ₀', τ₁', e', p', pf'⟩ h
  let lem₀ := terminal₁_eq_of_r H h
  let lem₁ := terminal₀_eq_of_r H h
  simp only at lem₁
  simp only at lem₀
  cases lem₀
  cases lem₁
  simp only [init_defn]
  apply Quotient.sound
  simp only [HasEquiv.Equiv]
  rw [path_eq_iff_r]
  simp [HasEquiv.Equiv, Setoid.r, relH] at h
  exact h.1

/--
The inverse of an edge in the cover
corresponding to the subgroup `H`.
-/
def bar : Quotient (edgeSetoid H) → Quotient (edgeSetoid H) := by
  apply Quotient.lift (⟦ (G.univ x₀).bar ·⟧)
  intro ⟨τ₀, τ₁, e, p, pf⟩ ⟨τ₀', τ₁', e', p', pf'⟩ h
  let lem₀ := terminal₁_eq_of_r H h
  let lem₁ := terminal₀_eq_of_r H h
  simp only at lem₁
  simp only at lem₀
  cases lem₀
  cases lem₁
  simp only [bar_eq_bar]
  have h': edgeSetoid H |>.r ⟨τ₀, τ₁, e, p, pf⟩ ⟨τ₀, τ₁, e', p', pf'⟩ := h
  simp [Setoid.r, relH] at h'
  apply Quotient.sound
  simp [HasEquiv.Equiv, Setoid.r, relH]
  apply And.intro
  · rw [← h'.2]
    rw [← mul_path_path]
    simp [reducedConcat,← inv_equiv_reverse, ← cons_homotopic_redCons, cons_equiv_of_equiv, PathClass]
    rw [inv_equiv_reverse, mul_path_path, reverse_cons,
      reverse_reverse, EdgeBetween.bar_bar, concat_append]
    have : [[p ++ cons e (cons (e.bar) (p'.reverse))]] = [[ p ++ p'.reverse ]] := by
      apply Quot.sound
      apply Reduction.step
    rw [this]
    exact h'.1
  · rw [h'.2]

theorem initial_defn (e: Edge G x₀):
    ι H ⟦ e ⟧ = ⟦ (G.univ x₀).ι e ⟧ := rfl

theorem bar_eq_barn (e : Edge G x₀):
    bar H ⟦ e ⟧ = ⟦ (G.univ x₀).bar e ⟧ := rfl

theorem bar_bar :(ebar : Quotient (edgeSetoid H)) →
    bar H (bar H ebar) = ebar := by
  apply Quotient.ind
  intro e
  simp [bar_eq_barn]

theorem bar_ne_self : (ebar : Quotient (edgeSetoid H)) →
    ebar ≠ bar H ebar := by
  apply Quotient.ind
  intro ⟨τ₀, τ₁, e, p, pf⟩
  simp only [bar_eq_barn, Edge.bar_eq_bar]
  intro contra
  rw [@Quotient.eq _ (edgeSetoid H)] at contra
  let lem := terminal₀_eq_of_r H contra
  simp only at lem
  cases lem
  simp [HasEquiv.Equiv, Setoid.r, relH] at contra
  let c := contra.2
  have : e.bar.edge = e.edge := by rw [← c]
  simp at this
  let nfp := G.bar_ne_self e.edge
  simp [this] at nfp

end Quot

/--
The cover corresponding to the subgroup `H` of the fundamental group.
-/
def groupCover :
    SerreGraph (Quotient (vertSetoid H)) (Quotient (edgeSetoid H)) where
  ι := Quot.ι H
  bar := Quot.bar H
  bar_bar := Quot.bar_bar H
  bar_ne_self := Quot.bar_ne_self H

namespace Quot

/--
The projection of a vertex in the cover.
-/
def toFuncV : Quotient (vertSetoid H) → V := by
  apply Quotient.lift (fun v : Vert G x₀ ↦ v.τ)
  simp [HasEquiv.Equiv]
  intro v₁ v₂
  apply terminal_eq_of_r H

theorem toFuncV_defn (v : Vert G x₀):
    toFuncV H ⟦ v ⟧ = v.τ := rfl

/--
The projection of an edge in the cover.
-/
def toFuncE : Quotient (edgeSetoid H) → E := by
  apply Quotient.lift (fun e : Edge G x₀ ↦ e.nxt.edge)
  simp [HasEquiv.Equiv]
  intro e₁ e₂
  apply edge_eq_of_r H

theorem toFuncE_defn (e : Edge G x₀):
    toFuncE H ⟦ e ⟧ = e.nxt.edge := rfl

theorem initial (e : Edge G x₀):
    (groupCover H).ι ⟦ e ⟧ = ⟦ (G.univ x₀).ι e⟧ := rfl

theorem bar_eq_barn' (e : Edge G x₀):
    (groupCover H).bar ⟦ e ⟧ = ⟦ (G.univ x₀).bar e ⟧ := rfl

theorem toFuncV_init : (ebar : Quotient (edgeSetoid H)) →
    toFuncV H ((groupCover H).ι ebar) =
    G.ι (toFuncE H ebar) := by
  apply Quotient.ind
  intro e
  rw [initial]
  rw [toFuncV_defn, toFuncE_defn]
  apply (proj G x₀).toFuncV_init

theorem toFuncE_bar : (ebar : Quotient (edgeSetoid H)) →
    toFuncE H ((groupCover H).bar ebar) = G.bar (toFuncE H ebar) := by
  apply Quotient.ind
  intro e
  rw [toFuncE_defn, bar_eq_barn']
  apply (proj G x₀).toFuncE_bar

end Quot

/--
The projection morphism of the cover to the base graph.
-/
def groupCoverProj : Morphism (groupCover H) G where
  toFuncV := Quot.toFuncV H
  toFuncE := Quot.toFuncE H
  toFuncV_init := Quot.toFuncV_init H
  toFuncE_bar := Quot.toFuncE_bar H

/--
The projection morphism of the universal cover to the cover.
-/
def univGroupProj : Morphism (G.univ x₀) (groupCover H)  where
  toFuncV := fun v ↦ ⟦ v ⟧
  toFuncE := fun e ↦ ⟦ e ⟧
  toFuncV_init := by
    intro e
    rfl
  toFuncE_bar := by
    intro e
    rfl

theorem projections_compose :
    (groupCoverProj H).comp (univGroupProj H) =
    UniversalCover.proj G x₀ := by
    ext
    · rfl
    · rfl

namespace Quot

theorem toFuncV_defn' (v : Vert G x₀):
    (groupCoverProj H).toFuncV ⟦ v ⟧ = v.τ := rfl

theorem toFuncE_defn' (τ₀ : V) (τ₁: V)(nxt: EdgeBetween G τ₀ τ₁)
    (p: EdgePath G x₀ τ₀)(red: reduced p):
  (groupCoverProj H).toFuncE ⟦ ⟨τ₀, τ₁, nxt, p, red⟩  ⟧ = nxt.edge := rfl

/--
Local section of the cover corresponding to the subgroup `H`.
-/
def localSection : (v₁ : Quotient (vertSetoid H)) → (e : E) →
    ((groupCoverProj H).toFuncV v₁) = G.ι e →
    Quotient (edgeSetoid H) := by
  intro v₁
  apply Quotient.hrecOn v₁
    (motive:= fun v₁ ↦ (e : E) → Morphism.toFuncV (groupCoverProj H) v₁ = SerreGraph.ι G e → Quotient (edgeSetoid H))
    (fun ⟨τ, p, is_reduced⟩ e h ↦
        ⟦ ⟨τ, G.τ e, ⟨e, Eq.symm h, rfl⟩, p, is_reduced⟩ ⟧)
  intro ⟨τ, p, is_reduced⟩ ⟨τ', p', is_reduced'⟩ rel
  have : τ = τ' := terminal_eq_of_r H rel
  cases this
  simp only [heq_eq_eq]
  simp [HasEquiv.Equiv, Setoid.r, relH] at rel
  funext e h
  apply Quotient.sound
  simp [HasEquiv.Equiv, Setoid.r, relH]
  exact rel

theorem localSection_defn (τ : V) (p : EdgePath G x₀ τ)
    (is_reduced : reduced p)
    (e: E) (h: τ = G.ι e):
    localSection H ⟦ ⟨τ, p, is_reduced⟩ ⟧ e h =
    ⟦ ⟨τ, G.τ e, ⟨e, Eq.symm h, rfl⟩, p, is_reduced⟩ ⟧ := rfl

theorem localSection_composition (τ₀ : V) (p : EdgePath G x₀ τ₀)
    (is_reduced : reduced p)
    (e: Edge G x₀) (h: τ₀ = G.ι e.nxt.edge) :
    localSection H ⟦ ⟨τ₀, p, is_reduced⟩ ⟧
    ((groupCoverProj H).toFuncE ⟦ e⟧) h =
    ⟦ ⟨τ₀, G.τ (e.nxt.edge),
    ⟨e.nxt.edge, Eq.symm h, rfl⟩, p, is_reduced⟩ ⟧ := rfl

theorem localSection_composition' (τ : V) (p : EdgePath G x₀ τ)
    (is_reduced : reduced p)(τ₀ τ₁ : V) (nxt: EdgeBetween G τ₀ τ₁)
    (p' : EdgePath G x₀ τ₀)
    (is_reduced' : reduced p')
    (h: τ = G.ι nxt.edge) :
    localSection H ⟦ ⟨τ, p, is_reduced⟩ ⟧
    ((groupCoverProj H).toFuncE ⟦ (⟨τ₀, τ₁, nxt, p', is_reduced'⟩ :
    Edge G x₀)⟧) h =
    ⟦ ⟨τ, τ₁,
    ⟨nxt.edge, Eq.symm h, nxt.term_eq⟩, p, is_reduced⟩ ⟧ := by
  rw [localSection_composition]
  apply Quotient.sound
  simp [nxt.term_eq]
  have : (⟨τ, G.τ (nxt.edge),
    ⟨nxt.edge, Eq.symm h, rfl⟩, p, is_reduced⟩ : Edge G x₀) =
    ⟨τ, τ₁,
    ⟨nxt.edge, Eq.symm h, nxt.term_eq⟩, p, is_reduced⟩ := by
    simp [nxt.term_eq, eq_of_edge_eq]
    congr
    rw [nxt.term_eq]
    have l {τ : V}(pf: G.τ nxt.edge = τ) :
      HEq (rfl: G.τ nxt.edge  = G.τ nxt.edge ) pf   := by
      cases pf
      simp only [heq_eq_eq]
    apply l nxt.term_eq
  rw [this]
  apply @Setoid.refl _ (edgeSetoid H)



theorem edge_from (e : Edge G x₀)(τ₀ : V): τ₀ = e.τ₀  →
    ∃ τ₁: V, ∃ nxt: EdgeBetween G τ₀ τ₁,
    ∃ p': EdgePath G x₀ τ₀, ∃ red: reduced p',
    e = ⟨τ₀, τ₁, nxt, p', red⟩ := by
  intro h
  cases h
  use e.τ₁, e.nxt, e.p, e.is_reduced

theorem edge_to (e : Edge G x₀)(τ₀ : V){τ₁ : V}: τ₀ = e.τ₀  →  e.τ₁ = τ₁  →
    ∃ nxt: EdgeBetween G τ₀ τ₁,
    ∃ p': EdgePath G x₀ τ₀, ∃ red: reduced p',
    e = ⟨τ₀, τ₁, nxt, p', red⟩ := by
  intro h₁ h₂
  cases h₁
  cases h₂
  use e.nxt, e.p, e.is_reduced

end Quot

/--
Covering map structure on the cover corresponding to the subgroup `H`.
-/
instance groupCovering : CoveringMap (groupCoverProj H)  where
  localSection := Quot.localSection H

  init_localSection := by
    apply Quotient.ind
    intro ⟨τ, p, is_reduced⟩ e h
    simp [Quot.localSection_defn]
    rw [Quot.initial, init_defn]

  toFuncE_localSection := by
    apply Quotient.ind
    intro ⟨τ, p, is_reduced⟩ e h
    simp [Quot.localSection_defn]
    rw [Quot.toFuncE_defn']

  localSection_toFuncE := by
    apply Quotient.ind
    intro ⟨τ, p, is_reduced⟩
    apply Quotient.ind
    intro ⟨τ₀, τ₁, nxt, p', red⟩   h
    simp only [Quot.localSection_composition']
    rw [Quot.initial, init_defn] at h
    let rel:= Quotient.exact h
    let teq :τ = τ₀ := terminal_eq_of_r H rel
    apply Quotient.sound
    cases teq
    simp [HasEquiv.Equiv, Setoid.r, relH]
    simp [HasEquiv.Equiv, Setoid.r, relH] at rel
    exact rel

/-!
- Show that lifts are compositions of lifts to the universal cover and pushdowns, using uniqueness of lifts.
- Conclude terminal points of lifts are pushforwards of terminal points.
- Can take initial points as basepoints
-/

/--
Lift via lifting to the universal cover and projecting
of an edge-path in the cover corresponding to the subgroup `H`.
-/
def liftViaUniv {w₂ : V}
    (e: EdgePath G x₀ w₂):
    PathLift (groupCoverProj H) (basepoint H) rfl e :=
  let univPath :=
    e.lift (proj G x₀) (UniversalCover.basepoint G x₀) rfl
  {
    τ := ⟦ univPath.τ ⟧
    path := univPath.path.map (univGroupProj H)
    term_pushdown := by
      rw [Quot.toFuncV_defn']
      exact univPath.term_pushdown
    list_pushdown := by
      simp [map_toList, List.map_map]
      rw [← Morphism.comp_toFuncE']
      simp only [projections_compose, univPath.list_pushdown]
  }

theorem liftFactors {w₂ : V}(e: EdgePath G x₀ w₂) :
    (e.lift (groupCoverProj H) (basepoint H) rfl) = liftViaUniv H e := by
    apply unique_Pathlift

theorem liftTermFactors {w₂ : V}(e: EdgePath G x₀ w₂) :
    (e.lift (groupCoverProj H) (basepoint H) rfl).τ =
    ⟦liftTerminal (proj G x₀) (UniversalCover.basepoint G x₀) rfl e⟧ := by
  rw [liftFactors]
  rfl

theorem reduced_liftTerminal_factor {w₂ : V}(e: EdgePath G x₀ w₂)
    (hyp : reduced e) :
    (e.lift (groupCoverProj H) (basepoint H) rfl).τ =
    ⟦ ⟨w₂, e, hyp⟩ ⟧ := by
  rw [liftTermFactors, reduced_liftTerminal]

theorem reduced_liftTerminal_factor' {w₂ : V}(e: EdgePath G x₀ w₂)
    (hyp : reduced e) :
    (liftTerminal (groupCoverProj H) (basepoint H) rfl e) =
    ⟦ ⟨w₂, e, hyp⟩ ⟧ := by
  apply reduced_liftTerminal_factor


theorem imageInSubgroup : ∀ h : π₁ (groupCover H) (basepoint H),
    (groupCoverProj H).π₁map (basepoint H) x₀ rfl h ∈ H := by
  apply Quot.ind
  intro η
  let θ : EdgePath G x₀ x₀ := η.map (groupCoverProj H)
  let heqn := reduction_homotopic_self θ
  simp [Morphism.π₁map, PathClass.map]
  rw [← heqn]
  have term_eqn :=
    liftTerminal_eq_of_homotopic (groupCoverProj H)
    (basepoint H) rfl heqn
  rw [liftTerminal_of_proj (groupCoverProj H)  η] at term_eqn
  rw [reduced_liftTerminal_factor' H (reduction θ)
    (by apply reduction_reduced)] at term_eqn
  simp only [basepoint, UniversalCover.basepoint] at term_eqn
  rw [Quotient.eq (r := vertSetoid H)] at term_eqn
  simp [HasEquiv.Equiv, Setoid.r, relH] at term_eqn
  exact term_eqn


theorem proj_image : ∀ (g : π₁ G x₀),
    (g ∈ H ↔ ∃ h' : π₁ (groupCover H) (basepoint H),
    g = (groupCoverProj H).π₁map (basepoint H) x₀ rfl h') := by
apply Quot.ind
intro η
let η' := reduction η
apply Iff.intro
· intro mem
  have mem' :  [[ η ]] ∈ H := mem
  rw [← reduction_homotopic_self] at mem'
  let pL := η'.lift (groupCoverProj H) (basepoint H) rfl
  let p := pL.path
  have term_lift : pL.τ = _ :=
    reduced_liftTerminal_factor H η' (reduction_reduced η)
  have term_lift' : pL.τ = basepoint H := by
    rw [term_lift]
    simp only [basepoint, UniversalCover.basepoint]
    apply Quotient.sound
    simp [HasEquiv.Equiv, Setoid.r, relH]
    exact mem'
  let p' := p.shiftTarget term_lift'
  let h' : π₁ (groupCover H) (basepoint H) :=
    [[ p' ]]
  use h'
  simp [Morphism.π₁map, PathClass.map]
  show [[ η ]] = _
  rw [← reduction_homotopic_self]
  congr
  apply eq_of_toList_eq
  rw [EdgePath.map_toList, toList_shiftTarget,
    pL.list_pushdown]
· intro ⟨h, heqn⟩
  simp [imageInSubgroup H h, heqn]

theorem range_proj : MonoidHom.range
    (Morphism.π₁map (basepoint H) x₀ (groupCoverProj H) rfl) = H := by
  apply Subgroup.ext
  intro x
  simp [MonoidHom.mem_range]
  let l := proj_image H x
  apply Iff.intro
  · intro ⟨h, heq⟩
    apply l.2
    use h
    rw [heq]
  · intro g
    let ⟨h, heq⟩  := l.1 g
    use h
    rw [heq]

theorem group_of_cover_is_subgroup :
    π₁ (groupCover H) (basepoint H) ≃* H := by
  let hf :=
    cover_π₁injective (groupCoverProj H) (basepoint H) x₀ rfl
  let lem := MonoidHom.ofInjective hf
  apply MulEquiv.trans lem
  rw [range_proj]


end SubgroupCover

end SerreGraph
