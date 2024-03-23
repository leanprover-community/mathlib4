/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Mathlib.Combinatorics.SerreGraph.Basic
import Mathlib.Data.List.Basic

/-!
Covering space theory for Serre graphs.
We define covering maps, and the notion of a lift of a path.
We prove the basic results about existence and uniqueness of lifts.

We show that the covering map induces an injection on fundamental groups.
-/

namespace SerreGraph

open EdgePath PathClass

universe u v

variable {V V₁ V₂ V₃ : Type u} {E E₁ E₂ E₃ : Type v}

/--
A morphism of Serre graphs.
This consists of a map on vertices and edges that are compatible.

We do not allow here edges to be mapped to vertices. That will be a separate notion.
This definition is restrictive but useful for covering spaces.
-/
@[ext] structure Morphism (G₁ : SerreGraph V₁ E₁) (G₂ : SerreGraph V₂ E₂) where
  toFuncV : V₁ → V₂
  toFuncE : E₁ → E₂
  toFuncV_init : ∀ (e : E₁),  toFuncV (G₁.ι e) = G₂.ι (toFuncE e)
  toFuncE_bar : ∀ (e : E₁), toFuncE (G₁.bar e) = G₂.bar (toFuncE e)

theorem toFuncV_init {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) :
      ∀ (e : E₁), f.toFuncV (G₁.ι e) = G₂.ι (f.toFuncE e)  := by
  intro e
  exact f.toFuncV_init e

theorem toFuncE_bar {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) :
      ∀ (e : E₁), f.toFuncE (G₁.bar e) = G₂.bar (f.toFuncE e) := by
  intro e
  exact f.toFuncE_bar e

theorem toFuncV_term {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) :
      ∀ (e : E₁), f.toFuncV (G₁.τ e)=  G₂.τ (f.toFuncE e)  := by
  intro e
  rw [SerreGraph.τ, SerreGraph.τ, ←toFuncE_bar, ←toFuncV_init]

/--
An auxiliary function to define the induced map on paths of a Morphism.
For convenience with recursion and proofs,
the results is a subtype giving a path and a
proof that the list of edges of the path is mapped correctly.
-/
def Morphism.pathMapAux {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) (v₁ w₁: V₁) (p: G₁.EdgePath v₁ w₁):
    {path : G₂.EdgePath (f.toFuncV v₁) (f.toFuncV w₁) //
    path.toList = p.toList.map f.toFuncE} := by
      match p with
      | nil _ =>
        exact ⟨nil _, by simp [nil_toList]⟩
      | cons e p' =>
        rename_i  w₁'' u'
        let e₁ := f.toFuncE e.edge
        let init_vert : G₂.ι e₁ = f.toFuncV v₁ := by
          rw [←e.init_eq, ←toFuncV_init]
        let term_vert : G₂.τ e₁ = f.toFuncV u' := by
          rw [← toFuncV_term, e.term_eq]
        let edge₂ : EdgeBetween G₂ (f.toFuncV v₁) (f.toFuncV u') :=
          ⟨e₁, init_vert, term_vert⟩
        let ⟨tail, ih⟩ := pathMapAux f u' w₁ p'
        exact ⟨cons edge₂ tail, by simp [cons_toList, ih]⟩

/--
Map on paths induced by a morphism.
-/
def EdgePath.map {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}{v₁ w₁: V₁}
    (p: G₁.EdgePath v₁ w₁)(f: Morphism G₁ G₂)  :=
    (f.pathMapAux v₁ w₁ p).val

theorem EdgePath.map_toList {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (p: G₁.EdgePath v₁ w₁) :
      (p.map f).toList = p.toList.map f.toFuncE :=
      (f.pathMapAux v₁ w₁ p).property

/--
Map on edges between vertices induced by a morphism.
-/
def EdgeBetween.map {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (e: G₁.EdgeBetween v₁ w₁) :
      G₂.EdgeBetween (f.toFuncV v₁) (f.toFuncV w₁) :=
      ⟨f.toFuncE e.edge, by
        simp [← f.toFuncV_init]
        congr
        exact e.init_eq
        , by
        rw [← toFuncV_term]
        congr
        exact e.term_eq⟩

theorem EdgeBetween.map_toList {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (e: G₁.EdgeBetween v₁ w₁) :
      (e.map f).edge = f.toFuncE e.edge := by
        simp [EdgeBetween.map, toList]

theorem EdgeBetween.map_bar {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (e: G₁.EdgeBetween v₁ w₁) :
      (e.map f).bar = e.bar.map f := by
        ext
        simp [f.toFuncE_bar, EdgeBetween.map]

namespace Morphism

variable {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂} (f: Morphism G₁ G₂)

theorem append_map {u v w : V₁}(η : EdgePath G₁ u v)
    (η' : EdgePath G₁ v w):
    (η ++ η').map f = (η.map f) ++ (η'.map f) := by
      apply eq_of_toList_eq
      simp [map_toList, append_toList]

theorem cons_map {u v w : V₁}(e : G₁.EdgeBetween u v)
    (η : EdgePath G₁ v w):
    (cons e η).map f = cons (e.map f) (η.map f) := by
      apply eq_of_toList_eq
      simp [map_toList, EdgeBetween.map_toList, cons_toList]

theorem reverse_map {u v : V₁}(η : EdgePath G₁ u v):
    η.reverse.map f = (η.map f).reverse := by
      apply eq_of_toList_eq
      simp [map_toList, reverse_toList, List.map_reverse]
      congr
      funext e
      simp only [Function.comp, f.toFuncE_bar]

theorem map_of_reduction {v w : V₁} (η₁ η₂ : EdgePath G₁ v w):
    Reduction η₁ η₂ → Reduction (η₁.map f) (η₂.map f)
  | Reduction.step u u' e p₁ p₂ => by
    simp [append_map, cons_map]
    rw [← EdgeBetween.map_bar]
    apply Reduction.step

theorem reduced_of_image_reduced {v w : V₁} (η : EdgePath G₁ v w):
    reduced (η.map f) → reduced η := by
  intro hyp η' contra
  apply hyp (η'.map f)
  apply map_of_reduction
  exact contra

/--
Composition of morphisms.
-/
def comp {G₃: SerreGraph V₃ E₃} (g: Morphism G₂ G₃)(f: Morphism G₁ G₂) :
    Morphism G₁ G₃ := {
  toFuncV := g.toFuncV ∘ f.toFuncV,
  toFuncE := g.toFuncE ∘ f.toFuncE,
  toFuncV_init := by
    intro e
    simp [Function.comp]
    rw [← g.toFuncV_init, ← f.toFuncV_init]
  toFuncE_bar := by
    intro e
    simp [Function.comp]
    rw [← g.toFuncE_bar, ← f.toFuncE_bar]
  }

/--
Identity morphism.
-/
protected def id : Morphism G₁ G₁ where
  toFuncV := id
  toFuncE := id
  toFuncV_init := by
    intro e
    simp
  toFuncE_bar := by
    intro e
    simp

protected theorem comp_id  (f: Morphism G₁ G₂) :
    Morphism.comp (Morphism.id) f = f := by
  cases f
  rfl

protected theorem id_comp (f: Morphism G₁ G₂) :
    Morphism.id.comp f  = f := by
  cases f
  rfl

theorem comp_toFuncV {G₃: SerreGraph V₃ E₃} (g: Morphism G₂ G₃)
    (f: Morphism G₁ G₂) (v : V₁) :
    (g.comp f).toFuncV v = g.toFuncV (f.toFuncV v) := by
  rfl

theorem comp_toFuncE {G₃: SerreGraph V₃ E₃} (g: Morphism G₂ G₃)
    (f: Morphism G₁ G₂) (e : E₁) :
    (g.comp f).toFuncE e = g.toFuncE (f.toFuncE e) := by
  rfl

theorem comp_toFuncE' {G₃: SerreGraph V₃ E₃} (g: Morphism G₂ G₃)
    (f: Morphism G₁ G₂)  :
    (g.comp f).toFuncE  = g.toFuncE ∘ f.toFuncE  := by
  rfl


theorem comp_assoc {G₃ G₄: SerreGraph V₃ E₃} (h: Morphism G₃ G₄)
    (g: Morphism G₂ G₃)(f: Morphism G₁ G₂) :
    Morphism.comp h (Morphism.comp g f) =
    Morphism.comp (Morphism.comp h g) f := by
  cases h
  cases g
  cases f
  rfl

end Morphism

namespace PathClass

variable {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂)

/--
Map on path classes induced by a morphism.
-/
def map  {v w : V₁}:
    PathClass G₁ v w → PathClass G₂ (f.toFuncV v) (f.toFuncV w) := by
  apply Quot.lift (fun η => [[η.map f ]])
  intro η₁ η₂ step
  apply Quot.sound
  apply Morphism.map_of_reduction f η₁ η₂ step

theorem map_on_quotient  {v w : V₁}
    (η : EdgePath G₁ v w) : [[ η ]].map f = [[ η.map f ]] := by
  rfl

theorem map_mul {v w u : V₁}:
    (η₁ : PathClass G₁ v w) →  (η₂ : PathClass G₁ w u) →
    (η₁ * η₂).map f = η₁.map f * η₂.map f := by
  apply Quot.ind
  intro a
  apply Quot.ind
  intro b
  simp only [mul_path_path, map_on_quotient, Morphism.append_map]


end PathClass

/--
Map on fundamental groups induced by a morphism.
-/
def Morphism.π₁map  (v₁ : V₁)(v₂ : V₂)
    {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (f: Morphism G₁ G₂) (hyp : f.toFuncV v₁ = v₂) :
    π₁ G₁ v₁  →* π₁ G₂ v₂  := by
  cases hyp
  exact {
    toFun := fun η => η.map f,
    map_mul' := fun η₁ η₂ => map_mul f η₁ η₂,
    map_one' := by rfl
    }



/--
A covering map is a morphism of Serre graphs that is a local homeomorphism.
-/
class CoveringMap {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
      (p: Morphism G₁ G₂)  where
  /--
  A section of the covering map on edges adjacent to a vertex.
  -/
  localSection : (v₁ : V₁) → (e : E₂) →
      p.toFuncV v₁ = G₂.ι e   → E₁
  init_localSection : (v₁ : V₁) → (e₂ : E₂) →
    (h : p.toFuncV v₁ = G₂.ι e₂) →
    G₁.ι (localSection v₁ e₂ h) = v₁
  toFuncE_localSection : (v₁ : V₁) → (e₂ :E₂) →
    (h : p.toFuncV v₁ = G₂.ι e₂) →
    p.toFuncE (localSection v₁ e₂ h) = e₂
  localSection_toFuncE : (v₁ : V₁) → (e₁ : E₁) →
    (h : v₁ = G₁.ι e₁) →
    localSection v₁ (p.toFuncE e₁) (by rw [← p.toFuncV_init, h]) =
      e₁

namespace Morphism

/--
Local section of a covering map on edges adjacent to a vertex.
-/
def localSection {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂)
      (h : p.toFuncV v₁ = G₂.ι e₂) : E₁ :=
        CoveringMap.localSection v₁ e₂ h

theorem init_localSection {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂)
      (h : p.toFuncV v₁ = G₂.ι e₂) :
      G₁.ι (localSection p v₁ e₂ h) = v₁ :=
        CoveringMap.init_localSection v₁ e₂ h

theorem toFuncE_localSection {G₁ : SerreGraph V₁ E₁}
    {G₂ : SerreGraph V₂ E₂}
    (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂)
    (h : p.toFuncV v₁ = G₂.ι e₂) :
    p.toFuncE (localSection p v₁ e₂ h) = e₂ :=
        CoveringMap.toFuncE_localSection v₁ e₂ h


theorem localSection_toFuncE {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₁ : E₁)
    (h : v₁ = G₁.ι e₁) :
    localSection p v₁ (p.toFuncE e₁)
    (by rw [← p.toFuncV_init, h]) = e₁ :=
          CoveringMap.localSection_toFuncE v₁ e₁ h

end Morphism

/--
Strcuture for the lift of a path in a covering space.
-/
@[ext]
structure PathLift {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂ : V₂}
    (h : p.toFuncV v₁ = v₂)(e: EdgePath G₂ v₂ w₂) where
  /-- The terminal vertex of the lift -/
  τ : V₁
  /-- The lifted path in the covering space -/
  path: EdgePath G₁ v₁ τ
  term_pushdown : p.toFuncV τ = w₂
  list_pushdown : path.toList.map p.toFuncE = e.toList

/--
The lift of a path-class in a covering space given a lifted path.
-/
def PathLift.pathClass {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.toFuncV v₁ = v₂}{e: EdgePath G₂ v₂ w₂} (l : PathLift p v₁ h e) : PathClassFrom G₁ v₁  :=
      ⟨ l.τ , [[ l.path ]]⟩

/--
The lift of a path in a covering space.
-/
def EdgePath.lift {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    {v₂ w₂ : V₂}
    (e: EdgePath G₂ v₂ w₂)
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁)
    (h : p.toFuncV v₁ = v₂):
    PathLift p v₁ h e := by
    match e with
    | nil _ => exact ⟨v₁, nil _, h, (by simp [toList])⟩
    | cons e₂ b₂ =>
      rename_i w₂' w₂''
      let e₁ := p.localSection v₁ e₂.edge (by rw [h, e₂.init_eq])
        -- lift of the edge
      let v₁' := G₁.τ e₁ -- the final vertex of the lift
      have init_vert : G₁.ι e₁ = v₁ := by apply p.init_localSection
      have term_vert : p.toFuncV (G₁.τ e₁) = w₂'' := by
        rw [← e₂.term_eq]
        rw [toFuncV_term ]
        congr
        apply p.toFuncE_localSection
      let ⟨w₁, tail, pf₁, pf₂⟩ := lift b₂  p v₁' term_vert
      let edge₁ : EdgeBetween G₁ v₁ v₁' :=
        ⟨e₁, init_vert, rfl⟩
      exact ⟨w₁, cons edge₁ tail, pf₁, by
        simp [cons_toList, pf₂]
        apply p.toFuncE_localSection⟩

/--
Viewing a path in a covering space as the lift of a path in the base space.
-/
def asPathLift {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} (e: G₁.EdgePath v₁ w₁) :
    PathLift p v₁ rfl (e.map p) :=
  ⟨w₁, e, rfl, by simp [map_toList]⟩

theorem lifts_homotopic {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    {v₁ w₁ v₂ w₂ : V₁}
    (p : Morphism G₁ G₂)[CoveringMap p]
    (e₁ : EdgePath G₁ v₁ w₁) (e₂ : EdgePath G₁ v₂ w₂) (hv: v₁ = v₂) :
    e₁.toList.map p.toFuncE = e₂.toList.map p.toFuncE →
    e₁.toList = e₂.toList := by
    intro hyp
    match e₁ with
    | nil v =>
      simp [nil_toList] at hyp
      simp [nil_toList]
      symm at hyp
      rw [List.map_eq_nil] at hyp
      symm
      exact hyp
    | cons edg₁ p₁' =>
      match e₂, hv with
      | nil v, _ =>
        simp [nil_toList] at *
        assumption
      | cons edg₂ p₂', rfl =>
        simp [cons_toList] at *
        let ⟨h₁, h₂⟩ := hyp
        have edg_eq : edg₁.edge = edg₂.edge := by
          let eq₁ := p.localSection_toFuncE v₁ edg₁.edge (Eq.symm edg₁.init_eq)
          let eq₂ := p.localSection_toFuncE v₁ edg₂.edge (Eq.symm edg₂.init_eq)
          rw [← eq₁, ← eq₂]
          congr
        simp [edg_eq]
        apply lifts_homotopic p p₁' p₂'
        · rw [← edg₁.term_eq, ← edg₂.term_eq, edg_eq]
        · exact h₂

theorem unique_Pathlift {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h₁ h₂ : p.toFuncV v₁ = v₂}{e: EdgePath G₂ v₂ w₂} :
    (p₁ : PathLift p v₁ h₁ e) → (p₂ : PathLift p v₁ h₂ e) → p₁ = p₂ := by
    intro p₁ p₂
    have eq_edgepath_aux :
      p₁.path.toList.map p.toFuncE =
        p₂.path.toList.map p.toFuncE := by
      rw [p₁.list_pushdown, p₂.list_pushdown]
    have eq_edgepath : p₁.path.toList = p₂.path.toList := by
      apply lifts_homotopic p p₁.path p₂.path rfl
      apply eq_edgepath_aux
    have term_eq : p₁.τ = p₂.τ :=
      terminal_eq_of_toList_eq p₁.path p₂.path eq_edgepath rfl
    match p₁, p₂ with
    | ⟨τ₁, path₁, h₁, lc₁⟩, ⟨τ₂, path₂, h₂, lc₂⟩ =>
    have teq : τ₁ = τ₂ := term_eq
    cases teq
    have peq : path₁ = path₂ := by
      apply eq_of_toList_eq
      assumption
    cases peq
    rfl

/--
Pathlift obtained by appending two lifts with endpoints compatible.
-/
def PathLift.append {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.toFuncV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}
    (lift : PathLift p v₁ h e)
    (lift' : PathLift p lift.τ  lift.term_pushdown e') :
      PathLift p v₁  h (e ++ e') :=
      {τ := lift'.τ,
        path := lift.path ++ lift'.path,
        term_pushdown := lift'.term_pushdown,
        list_pushdown := by
          simp [append_toList]
          rw [lift.list_pushdown, lift'.list_pushdown]}

theorem EdgePath.lift_append {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.toFuncV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}:
      (e ++ e').lift p v₁ h  =
        (e.lift p v₁ h).append
          (e'.lift p (e.lift p v₁ h).τ
            (e.lift p v₁ h).term_pushdown) := by
        apply unique_Pathlift

theorem EdgePath.lift_append_tail {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.toFuncV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}:
      ((e ++ e').lift p v₁ h).τ  =
        ((e.lift p v₁ h).append
          (e'.lift p (e.lift p v₁ h).τ
            (e.lift p v₁ h).term_pushdown)).τ := by
        simp [lift_append]

/--
Pathlift obtained by reversing a path-lift.
-/
def PathLift.reverse {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.toFuncV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}
    (lift : PathLift p v₁ h e) :
      PathLift p lift.τ  lift.term_pushdown e.reverse :=
      {τ := v₁,
        path := lift.path.reverse,
        term_pushdown := h,
        list_pushdown := by
          simp [reverse_toList]
          rw [← lift.list_pushdown]
          simp [List.map_reverse]
          congr
          funext edge
          simp only [Function.comp, toFuncE_bar]}

theorem EdgePath.lift_reverse {G₁ : SerreGraph V₁ E₁}
    {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.toFuncV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}:
      (e.reverse).lift p (e.lift p v₁ h).τ
        (e.lift p v₁ h).term_pushdown  =
        (e.lift p v₁ h).reverse := by
        apply unique_Pathlift

def PathLift.cons_bar_cons {G₁ : SerreGraph V₁ E₁}
    {G₂ : SerreGraph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ w₂' : V₂}
    {h : p.toFuncV v₁ = v₂}{e: EdgeBetween G₂ v₂ w₂'}{e': EdgePath G₂ v₂ w₂}(lift' : PathLift p v₁  h e') :
      PathLift p v₁ h (cons e (cons e.bar e')) :=
      let edgeLift := p.localSection v₁ e.edge (by rw [h, e.init_eq])
      let edgeBetween : EdgeBetween G₁ v₁ (G₁.τ edgeLift) :=
          ⟨edgeLift, p.init_localSection _ _ _, rfl⟩

      {τ := lift'.τ,
        path := cons edgeBetween (cons edgeBetween.bar lift'.path),
        term_pushdown := lift'.term_pushdown,
        list_pushdown := by
          simp [cons_toList, p.toFuncE_localSection, EdgeBetween.bar]
          apply And.intro
          · rw [p.toFuncE_bar, p.toFuncE_localSection]
          · rw [lift'.list_pushdown]}


theorem homotopy_step_lift {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ w₂' u₂  : V₂}
    {h : p.toFuncV v₁ = v₂}{η₁: EdgePath G₂ v₂ w₂}{e: EdgeBetween G₂ w₂ w₂'}{η₂: EdgePath G₂ w₂ u₂}:
    ((η₁ ++ (cons e (cons e.bar η₂))).lift p v₁  h ).pathClass =
    ((η₁ ++ η₂).lift p v₁  h).pathClass := by
  let θ₁ := η₁.lift p v₁ h
  let w₁ := θ₁.τ
  let hw : p.toFuncV w₁ = w₂ := θ₁.term_pushdown
  let edgeLift := p.localSection w₁ e.edge (by rw [hw, e.init_eq])
  let e' : EdgeBetween G₁ w₁ (G₁.τ edgeLift) :=
          ⟨edgeLift, p.init_localSection _ _ _, rfl⟩
  let θ₂ := η₂.lift p w₁ hw
  let liftTailCanc : PathLift p w₁ hw (cons e (cons e.bar η₂)) :=
    {τ := θ₂.τ,
        path := cons e' (cons e'.bar θ₂.path),
        term_pushdown := θ₂.term_pushdown,
        list_pushdown := by
          simp [cons_toList, p.toFuncE_localSection, EdgeBetween.bar]
          apply And.intro
          · rw [p.toFuncE_bar, p.toFuncE_localSection]
          · rw [θ₂.list_pushdown]}
  let liftCanc :=
    θ₁.append liftTailCanc
  have splitLift :
    (η₁ ++ (cons e (cons e.bar η₂))).lift p v₁ h  =
      liftCanc := by
        apply unique_Pathlift
  rw [splitLift]
  have splitLift' :
    (η₁ ++ η₂).lift p v₁ h =
      θ₁.append θ₂ := by
        apply unique_Pathlift
  rw [splitLift']
  show (⟨θ₂.τ, [[ liftCanc.path ]]⟩ : PathClassFrom G₁ v₁) =
    ⟨θ₂.τ, [[ (θ₁.append θ₂).path ]]⟩
  have path1 : liftCanc.path =
    θ₁.path ++ (cons e' (cons e'.bar θ₂.path)) := by
      rfl
  have : [[ liftCanc.path ]] = [[ (θ₁.append θ₂).path ]] := by
    apply Quot.sound
    rw [path1]
    apply Reduction.step
  rw [this]

/--
Lifting a homotopy of paths to the covering space.
-/
def homotopyLift {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.toFuncV v₁ = v₂): PathClass G₂ v₂ w₂ →
    PathClassFrom G₁ v₁ := by
  apply Quot.lift (fun (η₂: EdgePath G₂ v₂ w₂) => (η₂.lift p v₁ h).pathClass)
  intro η₂ η₂' red
  induction red
  apply homotopy_step_lift

theorem homotopyLift_of_path {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂   : V₂}
    {h : p.toFuncV v₁ = v₂} (e : EdgePath G₂ v₂ w₂) :
    homotopyLift p v₁ h [[ e ]] =
      (e.lift p v₁ h).pathClass := by
    rfl

/--
Lifting a path-class to the covering space.
-/
def liftClass {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) (v₂ w₂ : V₂)
    (h : p.toFuncV v₁ = v₂)(e: EdgePath G₂ v₂ w₂):
    PathClassFrom G₁ v₁ :=
  (e.lift p v₁ h).pathClass

theorem liftClass_eq_of_homotopic {G₁ : SerreGraph V₁ E₁}
    {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.toFuncV v₁ = v₂) {e₁ e₂ : EdgePath G₂ v₂ w₂}
    (red : [[ e₁ ]] = [[ e₂ ]]) :
    liftClass p v₁ v₂ w₂ h e₁ = liftClass p v₁ v₂ w₂ h  e₂ := by
    simp [liftClass, ← homotopyLift_of_path]
    congr

/--
The terminal vertex of the lift of a path in the covering space,
given the path and the initial vertex.
-/
def liftTerminal {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂ : V₂}
    (h : p.toFuncV v₁ = v₂)(e: EdgePath G₂ v₂ w₂) : V₁:=
  (liftClass p v₁ v₂ w₂ h e).τ

theorem liftTerminal_eq_of_homotopic {G₁ : SerreGraph V₁ E₁}
    {G₂ : SerreGraph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.toFuncV v₁ = v₂) {e₁ e₂ : EdgePath G₂ v₂ w₂}
    (red : [[ e₁ ]] = [[ e₂ ]]) :
    liftTerminal p v₁ h e₁ = liftTerminal p v₁ h  e₂ := by
    simp [liftTerminal]
    rw [liftClass_eq_of_homotopic _ _ _ red]

theorem lift_of_proj {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} (e: G₁.EdgePath v₁ w₁):
    (e.map p).lift p v₁ rfl   = ⟨w₁, e, rfl, by simp [map_toList]⟩ := by
    apply unique_Pathlift

theorem liftTerminal_of_proj {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} (e: G₁.EdgePath v₁ w₁):
    liftTerminal p v₁ rfl (e.map p) = w₁ := by
      simp only [liftTerminal, liftClass, lift_of_proj]
      rfl

theorem proj_injective {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁}
    (e₁ e₂: G₁.EdgePath v₁ w₁): [[ e₁.map p ]] = [[ e₂.map p ]] → [[ e₁ ]] = [[ e₂ ]] := by
    intro hyp
    let lem :=
      liftClass_eq_of_homotopic p v₁ rfl hyp
    simp [liftClass, PathLift.pathClass] at lem
    rw [lift_of_proj] at lem
    rw [lift_of_proj] at lem
    simp at lem
    exact lem

theorem cover_π₁injective {G₁ : SerreGraph V₁ E₁} {G₂ : SerreGraph V₂ E₂}
    (p: Morphism G₁ G₂)[inst : CoveringMap p] (v₁ : V₁)(v₂ : V₂)(hyp : p.toFuncV v₁ = v₂):
    Function.Injective (p.π₁map v₁ v₂ hyp) := by
    cases hyp
    apply Quot.ind
    intro η₁
    apply Quot.ind
    intro η₂
    simp [Morphism.π₁map]
    apply proj_injective

end SerreGraph
