/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/

import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Functor.Functorial
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Logic.Small.Set
import Mathlib.Tactic.ApplyFun

/-!
  # Quivers as (co-)presheaves on the walking quiver

  In this file, we show that the category `Quiv.{v, u}` is equivalent to the full subcategory of
  the category **PSh(WPPair)** of presheaves on the walking parallel pair which are
  `u`-small and locally `v`-small. Here, `WalkingParallelPairᵒᵖ` takes the role of the
  "walking quiver", the category `1 ⇉ 0`. Every presheaf on the walking quiver picks out:

  * A type for `0`, which we interpret as the type of vertices
  * A type for `1`, which we interpret as the type of edges (sum of all hom-types)
  * A function for `left : 1 ⟶ 0`, which we interpret as assigning a source vertex to each edge
  * A function for `right : 1 ⟶ 0`, which we intepret as assigning a target vertex to each edge

  When `u = v`, `Quiv.{u, u}` is equivalent to the entire category **PSh(WPPair)** and
  as such is complete and cocomplete, as well as enjoying many other nice properties.
  Otherwise, we can still generate structure in `Quiv.{v, u}` by showing that relevant
  properties are closed under being `{u, v}`-small.

  ## Implementation

  We define `asFunctor` and `ofFunctor` as functions first, and then show that
  they are functorial and give an equivalence of categories. This is primarily
  so that `asFunctor` can be used with projection notation when the universe
  levels can be inferred, and because showing the functoriality of `ofFunctor`
  is easier after defining some API for the base function.

  We define both `asFunctor` and `ofFunctor` with an extra universe level `w`,
  which allows us to more easily state the equivalence between
  `SmallAsQuivSubcategory` at size `max v u` and any larger size.
-/

open CategoryTheory Limits Bicategory Strict UnivLE ObjectProperty

attribute [pp_with_univ] Quiv Quiver

namespace CategoryTheory.Quiv
open Opposite
universe w₂ w₁ w' w v₂ v₁ v u₂ u₁ u

scoped instance : Zero (WalkingParallelPairᵒᵖ) := ⟨.op .zero⟩
scoped instance : One (WalkingParallelPairᵒᵖ) := ⟨.op .one⟩

@[simp← ] lemma WalkingQuiver.zero_def : (0 : WalkingParallelPairᵒᵖ) = .op .zero := rfl
@[simp← ] lemma WalkingQuiver.one_def : (1 : WalkingParallelPairᵒᵖ) = .op .one := rfl

open WalkingQuiver

/-- Interpret a quiver as a co-presheaf on the walking quiver. -/
@[simps -fullyApplied, pp_with_univ]
def asFunctor (Q : Quiv.{v, u}) : WalkingParallelPairᵒᵖ ⥤ Type max w v u where
  obj
  | 0 => ULift.{max w v} Q.α
  | 1 => (s t : ULift.{max w v} Q.α) × (Q.str.Hom s.1 t.1)
  map :=
  @fun
  | .op _, .op _, ⟨.id x⟩ => ↾id
  | 1, 0, .op .left => ↾(·.1)
  | 1, 0, .op .right => ↾(·.2.1)
  map_id := by rintro ⟨⟨⟩⟩ <;> rfl
  map_comp := by rintro ⟨⟩ ⟨⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ <;> rfl


/-- `asFunctor` is itself functorial. -/
@[simps] instance asFunctor.functorial : Functorial asFunctor where
  map {U V : Quiv.{v, u}} (f : U ⟶ V) :=
  { app
    | ⟨.zero⟩ => ULift.map f.obj
    | 1 => ↾(fun ⟨s, t, hom⟩ ↦ ⟨ULift.map f.obj s, ULift.map f.obj t, f.map hom⟩)
    naturality := by rintro ⟨⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ <;> rfl }

variable {F : WalkingParallelPairᵒᵖ ⥤ Type w} {X : Quiv.{v, u}}

/-- The source of an element of `F.obj 1`, interpreted as the source of an edge in the
corresponding quiver. -/
abbrev src (e : F.obj 1) := F.map (Quiver.Hom.op .left) e
/-- The target of an element of `F.obj 1`, interpreted as the target of an edge in the
corresponding quiver. -/
abbrev tgt (e : F.obj 1) := F.map (Quiver.Hom.op .right) e

unif_hint hom_eq_asFunctor1 (X : Quiv.{v, u}) where
  ⊢ (s t : ULift.{max w v} X) × (s.1 ⟶ t.1) ≟ (asFunctor.{w} X).obj 1

@[simp] lemma asFunctor_src (e : (s t : ULift X) × (s.1 ⟶ t.1)) :
  src e = e.1 := rfl
@[simp] lemma asFunctor_tgt (e : (s t : ULift X) × (s.1 ⟶ t.1)) :
  tgt e = e.2.1 := rfl

@[simp] lemma src_asFunctor {s t : ULift X} (e : (s.1 ⟶ t.1)) :
  src (⟨s, t, e⟩ : (asFunctor.{w} X).obj 1) = s := rfl
@[simp] lemma tgt_asFunctor {s t : ULift X} (e : (s.1 ⟶ t.1)) :
  tgt (⟨s, t, e⟩ : (asFunctor.{w} X).obj 1) = t := rfl

@[ext]
lemma asFunctor.hom_ext (f g : (s t : ULift.{max w v} X) × (s.1 ⟶ t.1))
    (hs : src f = src g) (ht : tgt f = tgt g) (he : HEq f.2.2 g.2.2) : f = g := by
  rcases f with ⟨fs, ft, fe⟩
  rcases g with ⟨gs, gt, ge⟩
  simp_all only [src, tgt, asFunctor_map, asHom]
  cases hs; cases ht
  congr
  exact heq_iff_eq.mp he

attribute [simp high] asFunctor.hom_ext_iff

/-- The type of vertices of a quiver in functor form. -/
abbrev Vertex (F : WalkingParallelPairᵒᵖ ⥤ Type w) := F.obj 0
/-- The type of all edges of a quiver in functor form. -/
abbrev Edges (F : WalkingParallelPairᵒᵖ ⥤ Type w) := F.obj 1
/-- The type of edges between two vertices of a quiver in functor form. -/
abbrev Edge (F : WalkingParallelPairᵒᵖ ⥤ Type w) (s t : Vertex F) :=
  {e : F.obj 1 // src e = s ∧ tgt e = t}

instance {F s t} : CoeOut (Edge F s t) (F.obj 1) where
  coe e := e.1

instance {F e} : CoeDep (F.obj 1) e (Edge F (src e) (tgt e)) where
  coe := ⟨e, rfl, rfl⟩

@[ext]
lemma Edge.ext {s t : Vertex F} {e f : Edge F s t} (h : e.1 = f.1) :
  e = f := by cases e; cases f; simp_all

/-- Assign a more precise type to an edge of a quiver in functor form. -/
@[coe] abbrev hom (e : F.obj 1) : Edge F (src e) (tgt e) := ↑e

@[simp]
lemma src_edge {s t : Vertex F} (e : Edge F s t) : src e = s := e.2.1
@[simp]
lemma tgt_edge {s t : Vertex F} (e : Edge F s t) : tgt e = t := e.2.2

variable (F)

/-- A vertex of a quiver in functor form is connected iff it is either the
source or target of an edge. -/
abbrev vertexConnected (x : Vertex F) :=
  ∃ y, Nonempty (Edge F x y) ∨ Nonempty (Edge F y x)

/-- A more useful statement of `¬ vertexConnected F ·`. -/
@[simp]
lemma not_vertexConnected_iff (x : Vertex F) :
    ¬ vertexConnected F x ↔ ∀ (e : F.obj 1), src e ≠ x ∧ tgt e ≠ x where
  mp h e := by
    contrapose h
    rw [Classical.not_and_iff_not_or_not] at h
    simp_rw [Classical.not_not] at h ⊢
    rcases h with (rfl | rfl)
    · use tgt e
      left
      exact ⟨e, rfl, rfl⟩
    · use src e
      right
      exact ⟨e, rfl, rfl⟩
  mpr h := by
    simp only [not_exists, nonempty_subtype, not_or, not_and]
    intro y
    constructor
    all_goals
      rintro e rfl
      specialize h e
      cases h; simp_all

variable {F}

/-- If the source or target vertices of two sets of edges differ, then the sets
are disjoint. -/
lemma edge_disjoint {F : WalkingParallelPairᵒᵖ ⥤ Type w}
    (st₁ st₂ : Vertex F × Vertex F) (h : st₁ ≠ st₂) :
    Function.onFun Disjoint (fun st' ↦ {e.1 | e : Edge F st'.1 st'.2 }) st₁ st₂ := by
  intro es hst₁ hst₂ e he
  specialize hst₁ he
  specialize hst₂ he
  simp only [Set.mem_setOf_eq] at hst₁ hst₂
  rcases hst₁ with ⟨⟨e₁, hs₁, ht₁⟩, he₁⟩
  rcases hst₂ with ⟨⟨e₂, hs₂, ht₂⟩, he₂⟩
  simp only at he₁ he₂; subst he₁ he₂
  have : st₁ = st₂ := by ext <;> simp_all
  contradiction

/-- We can cast an `Edge` along paired equalities of its source and target.
Unlike `Quiver.Hom` and `homOfEq`, the source and target are internally only tracked
by the subtype prop, so no casts appear in the result and `edgeOfEq` is a bit better
behaved. -/
-- @[simp]
def edgeOfEq {s s' t t' : Vertex F} (e : Edge F s t)
    (hs : s = s') (ht : t = t') : Edge F s' t' := ⟨e.1, by simp [←hs, ←ht]⟩

/-- `edgeOfEq` as an Equiv. -/
@[simps]
def Edge.equivOfEq {s s' t t' : Vertex F} (hs : s = s') (ht : t = t') :
    Edge F s t ≃ Edge F s' t' := {
  toFun e := edgeOfEq e hs ht
  invFun e := edgeOfEq e hs.symm ht.symm
  left_inv e := by simp [edgeOfEq]
  right_inv e := by simp [edgeOfEq]
}

@[simp]
lemma edgeOfEq_val {s s' t t' : Vertex F} (hs : s = s') (ht : t = t')
    (e : Edge F s t) : (edgeOfEq e hs ht).1 = e.1 := by simp [edgeOfEq]

lemma edgeOfEq_inj {s s' t t' : Vertex F}
    (hs₁ hs₂ : s = s') (ht₁ ht₂ : t = t') (e e' : Edge F s t) :
    edgeOfEq e hs₁ ht₁ = edgeOfEq e' hs₂ ht₂ ↔ e = e' := by
  cases hs₁; cases hs₂; cases ht₁; cases ht₂; simp [edgeOfEq]

@[simp]
lemma edgeOfEq_refl {s t : Vertex F} (e : Edge F s t) :
    edgeOfEq e rfl rfl = e := by simp [edgeOfEq]

@[simp]
lemma edgeOfEq_trans {s s' s'' t t' t'' : Vertex F}
    (e : Edge F s t) (hs : s = s') (hs' : s' = s'') (ht : t = t') (ht' : t' = t'') :
    edgeOfEq (edgeOfEq e hs ht) hs' ht' = edgeOfEq e (hs.trans hs') (ht.trans ht') :=
  by simp [edgeOfEq]

@[simp]
lemma edgeOfEq_eq_iff {s s' t t' : Vertex F}
    (e : Edge F s t) (e' : Edge F s' t') (hs : s = s') (ht : t = t') :
    edgeOfEq e hs ht = e' ↔ e = edgeOfEq e' hs.symm ht.symm := by
  cases hs; cases ht; rfl

@[simp]
lemma eq_edgeOfEq_iff {s s' t t' : Vertex F}
    (e : Edge F s t) (e' : Edge F s' t') (hs : s' = s) (ht : t' = t) :
    e = edgeOfEq e' hs ht ↔ edgeOfEq e hs.symm ht.symm = e' := by
  cases hs; cases ht; rfl

@[simp]
lemma hom_edge {s t : Vertex F} (e : Edge F s t) :
    hom e.1 = edgeOfEq e (src_edge _).symm (tgt_edge _).symm := by
  simp [edgeOfEq]

instance {Q : Quiv.{v, u}} : Small.{u} (Vertex Q.asFunctor) where
  equiv_small := ⟨Q, ⟨Equiv.ulift⟩⟩

instance {Q : Quiv.{v, u}} {s t : Vertex Q.asFunctor} :
    Small.{v} (Edge Q.asFunctor s t) where
  equiv_small := ⟨s.down ⟶ t.down, ⟨{
    toFun := fun ⟨⟨s, t, e⟩, ⟨hs, ht⟩⟩ ↦ hs ▸ ht ▸ e
    invFun e := ⟨⟨s, t, e⟩, ⟨rfl, rfl⟩⟩
    left_inv := by rintro ⟨⟨s, t, e⟩, ⟨rfl, rfl⟩⟩; simp
    right_inv e := rfl
  }⟩⟩

@[elab_as_elim]
def map_hom {motive : (F.obj 1) → Sort*}
    (f : {s t : Vertex F} → (e : Edge F s t) → motive e) (e : F.obj 1) : motive e :=
  f (hom e)

section naturality

variable {X Y : Quiv.{v, u}} {F G : WalkingParallelPairᵒᵖ ⥤ Type w} --{X Y : Quiv.{u, max u v}}
         (μ : F ⟶ G) {s t : Vertex F} {f : Edge F s t}

/-- Rephrasing naturality as a property of `src`, which can be more convenient when rewriting
by hand. -/
@[simp↓]
lemma naturality_src (f : F.obj 1) : src (μ.app 1 f) = (μ.app 0 (src f)) := by
  simpa using congrFun (μ.naturality ⟨.left⟩).symm f

/-- Rephrasing naturality as a property of `tgt`, which can be more convenient when rewriting
by hand. -/
@[simp↓]
lemma naturality_tgt (f : F.obj 1) : tgt (μ.app 1 f) = (μ.app 0 (tgt f)) := by
  simpa using congrFun (μ.naturality ⟨.right⟩).symm f

/-- The image of an precisely-typed edge under a natural transformation. -/
def natTransEdge (f : Edge F s t) : Edge G (μ.app 0 s) (μ.app 0 t) :=
  Subtype.map (μ.app 1) (fun e ⟨hs, ht⟩ ↦ by simp [hs, ht]) f

@[simp]
lemma naturality_src_limit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingParallelPairᵒᵖ ⥤ Type max w u} (j : J) e :
    src (limit.π (F.flip.obj 1) j e) = limit.π (F.flip.obj 0) j (src (F := F.flip ⋙ lim) e) := by
  simp [zero_def, one_def, src]

@[simp]
lemma naturality_src_colimit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingParallelPairᵒᵖ ⥤ Type max w u} (j : J) e :
    src (F := F.flip ⋙ colim) (colimit.ι (F.flip.obj 1) j e) =
      colimit.ι (F.flip.obj 0) j (src e) := by
  simp [zero_def, one_def, src]

@[simp]
lemma naturality_tgt_limit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingParallelPairᵒᵖ ⥤ Type max w u} (j : J) e :
    tgt (limit.π (F.flip.obj 1) j e) = limit.π (F.flip.obj 0) j (tgt (F := F.flip ⋙ lim) e) := by
  simp [zero_def, one_def, tgt]

@[simp]
lemma naturality_tgt_colimit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingParallelPairᵒᵖ ⥤ Type max w u} (j : J) e :
    tgt (F := F.flip ⋙ colim) (colimit.ι (F.flip.obj 1) j e) =
      colimit.ι (F.flip.obj 0) j (tgt e) := by
  simp [zero_def, one_def, tgt]

--Special cases for `ULift` and postcomposition by `uliftFunctor`, which
--can't be written as natural transformations from `F` as `Type w ≠ Type max w w'`.

@[simp]
lemma naturality_src_up {f : F.obj 1} :
  @src (F ⋙ uliftFunctor.{w'}) (ULift.up f) = ULift.up (src f) := by rfl


lemma naturality_src_down {f : ULift (F.obj 1)} :
    src f.down = ULift.down (@src (F ⋙ uliftFunctor.{w'}) f) := by rfl

@[simp]
lemma naturality_tgt_up {f : F.obj 1} :
  @tgt (F ⋙ uliftFunctor.{w'}) (ULift.up f) = ULift.up (tgt f) := by rfl

-- @[simp]
lemma naturality_tgt_down {f : ULift (F.obj 1)} :
    tgt f.down = ULift.down (@tgt (F ⋙ uliftFunctor.{w'}) f) := by rfl

def natTransEdge_up {f : F.obj 1} :
    Edge (F ⋙ uliftFunctor.{w'}) (ULift.up (src f)) (ULift.up (tgt f)) :=
  ⟨ULift.up f, by simp⟩

def natTransEdge_down (f : ULift (F.obj 1)) :
    Edge F (ULift.down (@src (F ⋙ uliftFunctor.{w'}) f))
      (ULift.down (@tgt (F ⋙ uliftFunctor.{w'}) f)) :=
  ⟨ULift.down f, by simp [naturality_src_down, naturality_tgt_down]⟩

namespace asFunctor

def natTransEdge
    (μ : X.asFunctor ⟶ Y.asFunctor) {s t : X} (f : s ⟶ t) :
    Y.str.Hom (μ.app 0 ⟨s⟩).1 (μ.app 0 ⟨t⟩).1 :=
  Quiver.homOfEq (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩).2.2
    (congrArg ULift.down <| naturality_src μ _) (congrArg ULift.down <| naturality_tgt μ _)

@[simp]
lemma natTransEdge_heq
    (μ : X.asFunctor ⟶ Y.asFunctor) {s t : X} {f : s ⟶ t} :
    HEq (natTransEdge μ f) (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩).2.2 := by
  simp [natTransEdge, Quiver.homOfEq]

@[simp]
lemma natTransEdge_heq'
    (μ : X.asFunctor ⟶ Y.asFunctor) {f : (s t : ULift X) × (s.1 ⟶ t.1)} :
    HEq (natTransEdge μ f.2.2) (μ.app 1 f).2.2 := by
  simp [natTransEdge, Quiver.homOfEq]

@[simp]
lemma naturality_src {U V : Quiv.{v, u}} {s t : U.α} (f : s ⟶ t)
    (μ : U.asFunctor ⟶ V.asFunctor) :
    src (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩) = μ.app 0 ⟨s⟩ := by
  simp [asFunctor, src, Quiver.Hom.op]

@[simp]
lemma naturality_tgt {U V : Quiv.{v, u}} {s t : U.α} (f : s ⟶ t)
    (μ : U.asFunctor ⟶ V.asFunctor) :
    tgt (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩) = μ.app 0 ⟨t⟩ := by
  simp [asFunctor, tgt, Quiver.Hom.op]


instance : (Functor.of (asFunctor.{w, v, u})).Full := ⟨fun {U V : Quiv.{v, u}} μ ↦
  ⟨⟨ULift.down ∘ μ.app 0 ∘ ULift.up, asFunctor.natTransEdge μ⟩, by
    ext q₀ x
    rcases q₀ with ⟨⟨⟩⟩
    · simp [Functor.of, ULift.map, ULift.up_down]
    · rcases x with ⟨⟨s⟩, ⟨t⟩, f : s ⟶ t⟩
      simp only [Functor.of, asFunctor_obj, ULift.down_up, asFunctor.functorial_map_app, asHom,
        ULift.map_up, Function.comp_apply, ULift.up_down]
      ext <;> simp_rw [← one_def] <;> [rw [naturality_src]; rw [naturality_tgt]; simp] <;> simp⟩⟩

instance : (Functor.of (asFunctor.{w, v, u})).Faithful := ⟨fun {X Y} μ ν h => by
  rw [NatTrans.ext_iff, funext_iff] at h
  apply Prefunctor.ext
  · intro x₁ x₂ f
    simp_rw [eqRec_eq_cast, cast_cast, eq_cast_iff_heq]
    replace h := congrFun (h 1) ⟨⟨x₁⟩, ⟨x₂⟩, f⟩
    rw [asFunctor.hom_ext_iff] at h
    rcases h with ⟨_, _, he⟩
    exact he
  · intro x
    simpa [Functor.of] using congrFun (h 0) ⟨x⟩⟩

end asFunctor
end naturality
end CategoryTheory.Quiv
