/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/

import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Functor.Functorial
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Logic.Small.Set

import Mathlib.CategoryTheory.Category.Quiv.Shapes
import Mathlib.CategoryTheory.Category.Quiv.WalkingQuiver

set_option structureDiamondWarning true

open CategoryTheory Limits Bicategory Strict UnivLE ObjectProperty

attribute [pp_with_univ] Quiv Quiver

/-!
  # Quivers as (co-)presheaves on the walking quiver

  In this file, we show that the category `Quiv.{v, u}` is equivalent to the full subcategory of
  the category **PSh(WQuivᵒᵖ)** of presheaves on the walking quiver which are
  `u`-small and locally `v`-small.

  When `u = v`, `Quiv.{u, u}` is equivalent to the entire category **PSh(WQuivᵒᵖ)** and
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


namespace CategoryTheory.Quiv
universe w₂ w₁ w v₂ v₁ v u₂ u₁ u

/-- Interpret a quiver as a co-presheaf on the walking quiver. -/
@[simps -fullyApplied, pp_with_univ]
def asFunctor (Q : Quiv.{v, u}) : WalkingQuiver ⥤ Type max w v u where
  obj
  | 0 => ULift.{max w v} Q.α
  | 1 => (s t : ULift.{max w v} Q.α) × (Q.str.Hom s.1 t.1)
  map
  | .id _ => ↾id
  | .source => ↾(·.1)
  | .target => ↾(·.2.1)
  map_id m := by cases m <;> {unfold_projs; simp}
  map_comp {X Y Z} f g := by
    cases Z; swap
    · cases g; cases f; rfl
    · cases Y; swap
      · cases f; cases g <;> rfl
      · cases g; cases f <;> rfl


/-- `asFunctor` is itself functorial. -/
@[simps] instance asFunctor.functorial: Functorial asFunctor where
  map' {U V : Quiv.{v, u}} (f : U ⟶ V) :=
  { app
    | 0 => ULift.map f.obj
    | 1 => ↾(fun ⟨s, t, hom⟩ ↦ ⟨ULift.map f.obj s, ULift.map f.obj t, f.map hom⟩)
    naturality m m' f' := by
      cases m'; swap
      · cases f'; simp
      · cases m
        · cases f'; rfl
        · cases f' <;> { ext ⟨s, t, hom⟩; simp }}

namespace PresheafWalkingQuiver

/-- The source of an element of `F.obj 1`, interpreted as the source of an edge in the
corresponding quiver. -/
abbrev src {F : WalkingQuiver ⥤ Type w} (e : F.obj 1) := F.map .source e
/-- The target of an element of `F.obj 1`, interpreted as the target of an edge in the
corresponding quiver. -/
abbrev tgt {F : WalkingQuiver ⥤ Type w} (e : F.obj 1) := F.map .target e

unif_hint hom_eq_asFunctor1 (X : Quiv.{v, u}) where
  ⊢ (s t : ULift.{max w v} X) × (s.1 ⟶ t.1) ≟ (asFunctor.{w} X).obj 1

@[simp] lemma asFunctor_src {X : Quiv} (e : (s t :  ULift X) × (s.1 ⟶ t.1)) :
  src e = e.1 := rfl
@[simp] lemma asFunctor_tgt {X : Quiv} (e : (s t :  ULift X) × (s.1 ⟶ t.1)) :
  tgt e = e.2.1 := rfl

@[simp] lemma src_asFunctor {X : Quiv} {s t : ULift X} (e : (s.1 ⟶ t.1)) :
  src (⟨s, t, e⟩ : (asFunctor.{w} X).obj 1) = s := rfl
@[simp] lemma tgt_asFunctor {X : Quiv} {s t : ULift X} (e : (s.1 ⟶ t.1)) :
  tgt (⟨s, t, e⟩ : (asFunctor.{w} X).obj 1) = t := rfl

@[ext]
lemma asFunctor.hom_ext {X : Quiv.{v, u}} (f g : (s t : ULift.{max w v} X) × (s.1 ⟶ t.1))
    (hs : src f = src g) (ht : tgt f = tgt g) (he : HEq f.2.2 g.2.2) : f = g := by
  rcases f with ⟨fs, ft, fe⟩
  rcases g with ⟨gs, gt, ge⟩
  simp_all only [src, tgt, asFunctor_map, asHom, ULift.up_inj]
  cases hs; cases ht
  congr
  exact heq_iff_eq.mp he

attribute [simp high] asFunctor.hom_ext_iff

/-- The type of vertices of a quiver in functor form. -/
abbrev Vertex (F : WalkingQuiver ⥤ Type w) := F.obj 0
/-- The type of all edges of a quiver in functor form. -/
abbrev Edges (F : WalkingQuiver ⥤ Type w) := F.obj 1
/-- The type of edges between two vertices of a quiver in functor form. -/
abbrev Edge (F : WalkingQuiver ⥤ Type w) (s t : Vertex F) := {e : F.obj 1 // src e = s ∧ tgt e = t}

instance {F s t} : CoeOut (Edge F s t) (F.obj 1) where
  coe e := e.1

instance {F e} : CoeDep (F.obj 1) e (Edge F (src e) (tgt e)) where
  coe := ⟨e, rfl, rfl⟩

@[ext]
lemma Edge.ext {F : WalkingQuiver ⥤ Type w} {s t : Vertex F} {e f : Edge F s t} (h : e.1 = f.1) :
  e = f := by cases e; cases f; simp_all

/-- Assign a more precise type to an edge of a quiver in functor form. -/
abbrev hom {F : WalkingQuiver ⥤ Type w} (e : F.obj 1) : Edge F (src e) (tgt e) := ↑e

@[simp]
lemma src_edge {F : WalkingQuiver ⥤ Type w} {s t : Vertex F} (e : Edge F s t) : src e = s := e.2.1
@[simp]
lemma tgt_edge {F : WalkingQuiver ⥤ Type w} {s t : Vertex F} (e : Edge F s t) : tgt e = t := e.2.2

/-- A vertex of a quiver in functor form is connected iff it is either the
source or target of an edge. -/
abbrev vertexConnected (F : WalkingQuiver ⥤ Type w) (x : Vertex F) :=
  ∃ y, Nonempty (Edge F x y) ∨ Nonempty (Edge F y x)

/-- A more useful statement of `¬ vertexConnected F ·`. -/
@[simp]
lemma not_vertexConnected_iff (F : WalkingQuiver ⥤ Type w) (x : Vertex F) :
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

/-- If the source or target vertices of two sets of edges differ, then the sets
are disjoint. -/
lemma edge_disjoint {F : WalkingQuiver ⥤ Type w}
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
def edgeOfEq {F : WalkingQuiver ⥤ Type w} {s s' t t' : Vertex F} (e : Edge F s t)
    (hs : s = s') (ht : t = t') : Edge F s' t' := ⟨e.1, by simp [←hs, ←ht]⟩

/-- `edgeOfEq` as an Equiv. -/
@[simps]
def Edge.equivOfEq {F : WalkingQuiver ⥤ Type w} {s s' t t' : Vertex F} (hs : s = s') (ht : t = t') :
    Edge F s t ≃ Edge F s' t' := {
  toFun e := edgeOfEq e hs ht
  invFun e := edgeOfEq e hs.symm ht.symm
  left_inv e := by simp [edgeOfEq]
  right_inv e := by simp [edgeOfEq]
}

@[simp]
lemma edgeOfEq_val {F : WalkingQuiver ⥤ Type w} {s s' t t' : Vertex F} (hs : s = s') (ht : t = t')
    (e : Edge F s t) : (edgeOfEq e hs ht).1 = e.1 := by simp [edgeOfEq]

lemma edgeOfEq_inj {F : WalkingQuiver ⥤ Type w} {s s' t t' : Vertex F}
    (hs₁ hs₂ : s = s') (ht₁ ht₂ : t = t') (e e' : Edge F s t) :
    edgeOfEq e hs₁ ht₁ = edgeOfEq e' hs₂ ht₂ ↔ e = e' := by
  cases hs₁; cases hs₂; cases ht₁; cases ht₂; simp [edgeOfEq]

@[simp]
lemma edgeOfEq_refl {F : WalkingQuiver ⥤ Type w} {s t : Vertex F} (e : Edge F s t) :
    edgeOfEq e rfl rfl = e := by simp [edgeOfEq]

@[simp]
lemma edgeOfEq_trans {F : WalkingQuiver ⥤ Type w} {s s' s'' t t' t'' : Vertex F}
    (e : Edge F s t) (hs : s = s') (hs' : s' = s'') (ht : t = t') (ht' : t' = t'') :
    edgeOfEq (edgeOfEq e hs ht) hs' ht' = edgeOfEq e (hs.trans hs') (ht.trans ht') :=
  by simp [edgeOfEq]

@[simp]
lemma edgeOfEq_eq_iff {F : WalkingQuiver ⥤ Type w} {s s' t t' : Vertex F}
    (e : Edge F s t) (e' : Edge F s' t') (hs : s = s') (ht : t = t') :
    edgeOfEq e hs ht = e' ↔ e = edgeOfEq e' hs.symm ht.symm := by
  cases hs; cases ht; rfl

@[simp]
lemma eq_edgeOfEq_iff {F : WalkingQuiver ⥤ Type w} {s s' t t' : Vertex F}
    (e : Edge F s t) (e' : Edge F s' t') (hs : s' = s) (ht : t' = t) :
    e = edgeOfEq e' hs ht ↔ edgeOfEq e hs.symm ht.symm = e' := by
  cases hs; cases ht; rfl

@[simp]
lemma hom_edge {F : WalkingQuiver ⥤ Type w} {s t : Vertex F} (e : Edge F s t) :
    hom e.1 = edgeOfEq e (src_edge _).symm (tgt_edge _).symm := by
  simp [edgeOfEq]

instance {Q : Quiv.{v,u}} : Small.{u} (Vertex Q.asFunctor) where
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
def map_hom {F : WalkingQuiver ⥤ Type w} {motive : (F.obj 1) → Sort*}
    (f : {s t : Vertex F} → (e : Edge F s t) → motive e) (e : F.obj 1) : motive e :=
  f (hom e)

section naturality

variable {X Y : Quiv.{v, u}} {F G : WalkingQuiver ⥤ Type w} --{X Y : Quiv.{u, max u v}}
         (μ : F ⟶ G) {s t : Vertex F} {f : Edge F s t}

/-- Rephrasing naturality as a property of `src`, which can be more convenient when rewriting
by hand. -/
@[simp↓]
lemma naturality_src (f : F.obj 1) : src (μ.app 1 f) = (μ.app 0 (src f)) := by
  simpa using congrFun (μ.naturality .source).symm f

/-- Rephrasing naturality as a property of `tgt`, which can be more convenient when rewriting
by hand. -/
@[simp↓]
lemma naturality_tgt (f : F.obj 1) : tgt (μ.app 1 f) = (μ.app 0 (tgt f)) := by
  simpa using congrFun (μ.naturality .target).symm f

/-- The image of an precisely-typed edge under a natural transformation. -/
def natTransEdge (f : Edge F s t) : Edge G (μ.app 0 s) (μ.app 0 t) :=
  Subtype.map (μ.app 1) (fun e ⟨hs, ht⟩ ↦ by simp [hs, ht]) f

@[simp]
lemma naturality_src_limit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingQuiver ⥤ Type max w u} (j : J) e :
    src (limit.π (F.flip.obj 1) j e) = limit.π (F.flip.obj 0) j (@src (F := F.flip ⋙ lim) e) := by
  let ε := Types.limIsoSectionsFunctor.app (F.flip.obj 1) |>.toEquiv
  set e' := ε e with e'_def
  symm at e'_def; rw [Equiv.apply_eq_iff_eq_symm_apply] at e'_def
  rcases e' with ⟨e', he'⟩
  subst e'_def
  simp only [zero_eq, Functor.sectionsFunctor_obj, Functor.flip_obj_obj, lim_obj,
    Iso.toEquiv_symm_fun, Iso.app_inv, ε]
  conv_rhs =>
    simp only [src, one_eq, zero_eq, Functor.comp_map, ε]
    rw [← types_comp_apply _ (lim.map _), ← Types.limIsoSectionsFunctor.inv.naturality,
    ← types_comp_apply _ (limit.π _ _), Category.assoc]
  simp [ε, Types.limIsoSectionsFunctor]

#check Types.colimitEquivQuot

@[simp]
lemma naturality_src_colimit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingQuiver ⥤ Type max w u} (j : J) e :
    @src (F := F.flip ⋙ colim) (colimit.ι (F.flip.obj 1) j e) =
      colimit.ι (F.flip.obj 0) j (src e) := by
  let ε := Types.colimIsoQuotFunctor.app (F.flip.obj 1) |>.toEquiv
  set e' := ε (colimit.ι (F.flip.obj 1) j e) with ← e'_def
  rw [Equiv.apply_eq_iff_eq_symm_apply] at e'_def
  rw [e'_def]
  simp_rw [ε, Iso.toEquiv_symm_fun, Iso.app_inv]
  simp only [zero_eq, Functor.comp_obj, colim_obj, src, one_eq, Functor.comp_map, ε]
  rw [← types_comp_apply _ (colim.map _), ← Types.colimIsoQuotFunctor.inv.naturality]
  unfold e' ε
  simpa [Sigma.map, Quot.map] using Types.colimitEquivQuot_symm_apply _ _ _

@[simp]
lemma naturality_tgt_limit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingQuiver ⥤ Type max w u} (j : J) e :
    tgt (limit.π (F.flip.obj 1) j e) = limit.π (F.flip.obj 0) j (@tgt (F := F.flip ⋙ lim) e) := by
  let ε := Types.limIsoSectionsFunctor.app (F.flip.obj 1) |>.toEquiv
  set e' := ε e with e'_def
  symm at e'_def; rw [Equiv.apply_eq_iff_eq_symm_apply] at e'_def
  rcases e' with ⟨e', he'⟩
  subst e'_def
  simp only [zero_eq, Functor.sectionsFunctor_obj, Functor.flip_obj_obj, lim_obj,
    Iso.toEquiv_symm_fun, Iso.app_inv, ε]
  conv_rhs =>
    simp only [tgt, one_eq, zero_eq, Functor.comp_map, ε]
    rw [← types_comp_apply _ (lim.map _), ← Types.limIsoSectionsFunctor.inv.naturality,
    ← types_comp_apply _ (limit.π _ _), Category.assoc]
  simp [ε, Types.limIsoSectionsFunctor]

@[simp]
lemma naturality_tgt_colimit {J : Type w} [SmallCategory J]
    {F : J ⥤ WalkingQuiver ⥤ Type max w u} (j : J) e :
    @tgt (F := F.flip ⋙ colim) (colimit.ι (F.flip.obj 1) j e) =
      colimit.ι (F.flip.obj 0) j (tgt e) := by
  let ε := Types.colimIsoQuotFunctor.app (F.flip.obj 1) |>.toEquiv
  set e' := ε (colimit.ι (F.flip.obj 1) j e) with ← e'_def
  rw [Equiv.apply_eq_iff_eq_symm_apply] at e'_def
  rw [e'_def]
  simp_rw [ε, Iso.toEquiv_symm_fun, Iso.app_inv]
  simp only [zero_eq, Functor.comp_obj, colim_obj, tgt, one_eq, Functor.comp_map, ε]
  rw [← types_comp_apply _ (colim.map _), ← Types.colimIsoQuotFunctor.inv.naturality]
  unfold e' ε
  simpa [Sigma.map, Quot.map] using Types.colimitEquivQuot_symm_apply _ _ _


--Special cases for `ULift` and postcomposition by `uliftFunctor`, which
--can't be written as natural transformations from `F` as `Type w ≠ Type max w w'`.

@[simp]
lemma naturality_src_up.{w'} {f : F.obj 1} :
  @src (F ⋙ uliftFunctor.{w'}) (ULift.up f) = ULift.up (src f) := by rfl


lemma naturality_src_down.{w'} {f : ULift (F.obj 1)} :
    src f.down = ULift.down (@src (F ⋙ uliftFunctor.{w'}) f) := by rfl

@[simp]
lemma naturality_tgt_up.{w'} {f : F.obj 1} :
  @tgt (F ⋙ uliftFunctor.{w'}) (ULift.up f) = ULift.up (tgt f) := by rfl

-- @[simp]
lemma naturality_tgt_down.{w'} {f : ULift (F.obj 1)} :
    tgt f.down = ULift.down (@tgt (F ⋙ uliftFunctor.{w'}) f) := by rfl

def natTransEdge_up.{w'} {f : F.obj 1} :
    Edge (F ⋙ uliftFunctor.{w'}) (ULift.up (src f)) (ULift.up (tgt f)) :=
  ⟨ULift.up f, by simp⟩

def natTransEdge_down.{w'} (f : ULift (F.obj 1)) :
    Edge F (ULift.down (@src (F ⋙ uliftFunctor.{w'}) f))
      (ULift.down (@tgt (F ⋙ uliftFunctor.{w'}) f)) :=
  ⟨ULift.down f, by simp [naturality_src_down, naturality_tgt_down]⟩

def asFunctor.natTransEdge
    (μ : X.asFunctor ⟶ Y.asFunctor) {s t : X} (f : s ⟶ t) :
    Y.str.Hom (μ.app 0 ⟨s⟩).1 (μ.app 0 ⟨t⟩).1 :=
  Quiver.homOfEq (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩).2.2
    (congrArg ULift.down <| naturality_src μ _) (congrArg ULift.down <| naturality_tgt μ _)

@[simp]
lemma asFunctor.natTransEdge_heq
    (μ : X.asFunctor ⟶ Y.asFunctor) {s t : X} {f : s ⟶ t} :
    HEq (asFunctor.natTransEdge μ f) (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩).2.2 := by
  simp [asFunctor.natTransEdge, Quiver.homOfEq]

@[simp]
lemma asFunctor.natTransEdge_heq'
    (μ : X.asFunctor ⟶ Y.asFunctor) {f : (s t : ULift X) × (s.1 ⟶ t.1)} :
    HEq (asFunctor.natTransEdge μ f.2.2) (μ.app 1 f).2.2 := by
  simp [asFunctor.natTransEdge, Quiver.homOfEq]


end naturality
end Quiv.PresheafWalkingQuiver
namespace uliftFunctor
open Quiv.PresheafWalkingQuiver

@[simps!]
def vertexEquiv.{w', w} {F : WalkingQuiver ⥤ Type w} :
    Vertex (F ⋙ uliftFunctor.{w'}) ≃ Vertex F :=
  Equiv.ulift

@[simps!]
def edgeEquiv.{w', w} {F : WalkingQuiver ⥤ Type w} (s t : Vertex (F ⋙ uliftFunctor.{w'})) :
    Edge (F ⋙ uliftFunctor.{w'}) s t ≃ Edge F (vertexEquiv s) (vertexEquiv t) :=
  Equiv.ulift.subtypeEquiv fun e ↦ by
    constructor
    · rintro ⟨rfl, rfl⟩
      constructor
      all_goals simp [vertexEquiv, src, tgt]
    · rintro ⟨h₁, h₂⟩
      constructor
      all_goals
        apply ULift.ext
        simp [src, tgt, ULift.ext_iff] at h₁ h₂
        simp [h₁, h₂, vertexEquiv, src, tgt]

end uliftFunctor
namespace Quiv
attribute [local simp] ULift.down_up ULift.up_down
open PresheafWalkingQuiver asFunctor uliftFunctor
section
universe w₂ w₁ w v₂ v₁ v u₂ u₁ u


-- At many points in the following proofs, we have multiple goals all of which we intend to
-- ultimately solve with `simp`, but some of which need to be unstuck first. As such, the
-- multiGoal linter is unhelpful here.
set_option linter.style.multiGoal false

@[simp]
def mk (α : Type u) (hom : α → α → Type v) : Quiv where
  α := α
  str := {Hom := hom}

-- -- linter false positives on `aesop_cat` syntax for tactic rules
-- set_option linter.unusedTactic false
-- set_option linter.unreachableTactic false

#check ULift.map_conj

--TODO move to `asFunctor`
@[simp]
lemma naturality_src_asFunctor {U V : Quiv.{v, u}} {s t : U.α} (f : s ⟶ t)
    (μ : U.asFunctor ⟶ V.asFunctor) :
    src (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩) = μ.app 0 ⟨s⟩ := by
  simp [asFunctor]

@[simp]
lemma naturality_tgt_asFunctor {U V : Quiv.{v, u}} {s t : U.α} (f : s ⟶ t)
    (μ : U.asFunctor ⟶ V.asFunctor) :
    tgt (μ.app 1 ⟨⟨s⟩, ⟨t⟩, f⟩) = μ.app 0 ⟨t⟩ := by
  simp [asFunctor]

instance : (Functor.of (asFunctor.{w, v, u})).Full := ⟨fun {U V : Quiv.{v, u}} μ ↦
  ⟨⟨ULift.conj (μ.app 0), asFunctor.natTransEdge μ⟩, by
    ext q₀ x
    cases q₀
    · simp [Functor.of]
    · rcases x with ⟨⟨s⟩, ⟨t⟩, f⟩
      simp only [Functor.of, asFunctor_obj, ULift.down_up, asFunctor.functorial_map_app, asHom,
        ULift.map_up, ULift.conj.eq_1, ULift.up_down]
      -- TODO: `ext <;> simp` doesn't work here, but once either the src or tgt cases
      -- are cleared with a manual `rw`, the rest is `all_goals simp`
      ext
      rw [naturality_src]
      all_goals simp⟩⟩

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

end

open PresheafWalkingQuiver in
/-- A functor `WalkingQuiver ⥤ Type w` is `v, u`-small "as a quiver" if it corresponds to a
`Quiv.{v, u}` -- that is, its indicated vertex type is `u`-small and the
subtype restricting its indicated edge type to a given source and target is
`v`-small for all sources and targets.

(This would be equivalent to being `Small.{u}` and `LocallySmall.{v}`, if `LocallySmall` were
defined for quivers.)

Since `w`, the universe level of the functor, can be inferred, we put the
parameters first `v, u` first. -/
--TODO: We'd like this to be in the `CategoryTheory.Functor` namespace, but we
--can't use the generalized projection notation on a local together with explicit
--universe levels, so there's not much point. If that ever changes, we should
--move this to `CategoryTheory.Functor`.
@[pp_with_univ, mk_iff]
class SmallAsQuiv.{v, u, w} (F : WalkingQuiver ⥤ Type w) where
  [small_vertex : Small.{u} (Vertex F)]
  [small_edge : ∀ (s t : Vertex F), Small.{v} (Edge F s t)]

@[pp_with_univ]
def SmallAsQuivSubcategory.{v, u, w} := FullSubcategory SmallAsQuiv.{v, u, w}

instance : Category SmallAsQuivSubcategory := inferInstanceAs <| Category <| FullSubcategory _

section universe v' u' v u w' w
open PresheafWalkingQuiver


instance (F : WalkingQuiver ⥤ Type w) [inst : SmallAsQuiv.{v, u, w} F] :
  Small.{u} (Vertex F) := inst.small_vertex
instance (F : WalkingQuiver ⥤ Type w) [inst : SmallAsQuiv.{v, u, w} F] (s t : Vertex F) :
  Small.{v} (Edge F s t) := inst.small_edge s t

instance (F : SmallAsQuivSubcategory.{v, u, w}) : SmallAsQuiv.{v, u, w} F.1 := F.2
instance (F : SmallAsQuivSubcategory.{v, u, w}) :
  SmallAsQuiv.{v, u, w} (fullSubcategoryInclusion _ |>.obj F) := F.2

/-- Producing a functor from a `Quiv.{v, u}` is always `SmallAsQuiv.{v, u}`, regardless of the
third universe level to `asFunctor`. -/
instance smallAsQuiv_asFunctor (V : Quiv.{v, u}) : SmallAsQuiv.{v, u} V.asFunctor where

/-- `smallAsQuiv_asFunctor` written in terms of `Functor.of asFunctor`. -/
instance smallAsQuiv_asFunctor' (V : Quiv.{v, u}) :
    SmallAsQuiv.{v, u} (Functor.of asFunctor.{w, v, u} |>.obj V) :=
  smallAsQuiv_asFunctor V

instance smallAsQuiv_trans {F : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v, u, w} F] :
    SmallAsQuiv.{max v' v, max u' u, w} F where
  small_vertex := small_lift _
  small_edge _ _ := small_lift _

instance smallAsQuiv_closedUnderIso : IsClosedUnderIsomorphisms SmallAsQuiv.{v, u, w} where
  of_iso {F G} μ [_] :=
  { small_vertex := small_map ((μ.app 0).toEquiv.symm),
    small_edge s t :=
      let εᵥ := (μ.app 0).toEquiv.symm
      let εₑ : Edge G s t ≃ Edge F (εᵥ s) (εᵥ t) :=
        (μ.app 1).toEquiv.symm.subtypeEquiv fun e ↦ by
          have {GX GX'} : (μ.inv.app 0 GX = μ.inv.app 0 GX') ↔ (GX = GX') := by
            refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
            apply_fun (μ.hom.app 0) at h
            simpa using h
          simp [src, tgt, εᵥ, this]
      small_map εₑ }

namespace SmallAsQuivSubcategory

@[ext]
lemma hom_ext {F G : SmallAsQuivSubcategory.{v, u, w}} {μ ν : F ⟶ G}
    (h : ∀ X, μ.app X = ν.app X) : μ = ν := by
  apply NatTrans.ext
  ext1 X
  simpa using h X

abbrev obj (F : SmallAsQuivSubcategory.{v, u, w}) := F.1

@[simp]
lemma id_app {F : SmallAsQuivSubcategory.{v, u, w}} X :
    NatTrans.app (𝟙 F) X = 𝟙 (F.1.obj X) := rfl

@[simp]
lemma comp_comp_left
    {F : WalkingQuiver ⥤ Type w} {G H I : SmallAsQuivSubcategory.{v, u, w}}
    (μ : F ⟶ G.1) (η : G ⟶ H) (ϑ : H ⟶ I) :
    (μ ≫ (η ≫ ϑ : G ⟶ I)) = (μ ≫ η ≫ ϑ) := by
  rfl

@[simp]
lemma comp_comp_right
    {F G H : SmallAsQuivSubcategory.{v, u, w}} {I : WalkingQuiver ⥤ Type w}
    (μ : F ⟶ G) (η : G ⟶ H) (ϑ : H.1 ⟶ I) :
    ((μ ≫ η : F ⟶ H) ≫ ϑ : F.1 ⟶ I) = ((μ ≫ η : F.1 ⟶ H.1) ≫ ϑ) := by
  rfl

lemma comp_eq_comp
    {F G H : SmallAsQuivSubcategory.{v, u, w}} (μ : F ⟶ G) (η : G ⟶ H) :
    μ ≫ η = (μ ≫ η : F.1 ⟶ H.1) := by rfl

/-- Create an isomorphism in `SmallAsQuivSubcategory.{v, u, w}` from a natural
isomorphism between functors `F G : WalkingQuiver ⥤ Type w`. -/
@[simp]
def isoMk {F G : WalkingQuiver ⥤ Type w}
    [SmallAsQuiv.{v, u, w} F] [SmallAsQuiv.{v, u, w} G] (μ : F ≅ G) :
    (⟨F, ‹_›⟩ : SmallAsQuivSubcategory) ≅ ⟨G, ‹_›⟩ :=
  InducedCategory.isoMk μ

end SmallAsQuivSubcategory

@[simps -isSimp]
def ofFunctor F [SmallAsQuiv.{v, u, w} F] : Quiv.{v, u} where
  α := Shrink (Vertex F)
  str := { Hom x y := Shrink (Edge F (equivShrink _ |>.symm x) (equivShrink _ |>.symm y)) }

/-- If `F` is `SmallAsQuiv.{v, u}`, then so is `F ⋙ uliftFunctor.{w}` for any `w`. -/
instance uliftFunctor_smallAsQuiv {F : WalkingQuiver ⥤ Type w} [inst : SmallAsQuiv.{v, u, w} F] :
    SmallAsQuiv.{v, u} (F ⋙ uliftFunctor.{w'}) where
  small_vertex := ⟨⟨ inst.small_vertex.1.choose,
    ⟨vertexEquiv.trans inst.small_vertex.1.choose_spec.some⟩⟩⟩
  small_edge s t :=
    let τ := inst.small_edge (vertexEquiv s) (vertexEquiv t) |>.1
    ⟨⟨τ.choose, ⟨edgeEquiv s t |>.trans τ.choose_spec.some⟩⟩⟩

namespace ofFunctor
variable {F : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v, u, w} F]

instance : Quiver (Shrink <| Vertex F) := ofFunctor F |>.str

-- @[simp]
noncomputable def mk  :
    Vertex F → (ofFunctor F) := equivShrink (Vertex F)

noncomputable abbrev out (x : ofFunctor F) : Vertex F := equivShrink (Vertex F) |>.symm x

@[simp]
lemma out_mk  (X : Vertex F) : out (mk X) = X := by simp [mk, out]

@[simp]
lemma mk_out  (x : ofFunctor F) : mk (out x) = x := by simp [mk, out]

/-- Help the type-checker recognize edges of `ofFunctor`s. Hides a cast, so
use with caution. -/
-- @[simp]
noncomputable def mkHom {S T : Vertex F} : (Edge F S T) → (mk S ⟶ mk T) :=
  Edge.equivOfEq (out_mk _) (out_mk _) |>.symm.trans <| equivShrink (Edge F _ _)

-- @[simp]
noncomputable def outHom {s t : ofFunctor F} : (s ⟶ t) → (Edge F (out s) (out t)) :=
  equivShrink (Edge F (out s) (out t)) |>.symm

@[simp]
lemma outHom_mkHom  {S T : Vertex F} (e : Edge F S T) :
    outHom (mkHom e) = edgeOfEq e (out_mk S).symm (out_mk T).symm := by
  unfold outHom mkHom
  dsimp
  simp_rw [equivShrink _ |>.symm_apply_apply]

lemma mk_injective : Function.Injective (@mk F _) :=
  Equiv.injective (equivShrink _)

@[simp]
lemma mk_inj {X Y : Vertex F} : mk X = mk Y ↔ X = Y :=
  ⟨@mk_injective F _ _ _, by rintro rfl; rfl⟩

lemma out_injective : Function.Injective (@out F _) :=
  Equiv.injective (equivShrink _ |>.symm)

@[simp]
lemma mkHom_edgeOfEq  {S S' T T' : Vertex F}
    (e : Edge F S T) {hs : S = S'} {ht : T = T'} :
    mkHom (edgeOfEq e hs ht) = Quiver.homOfEq (mkHom e) (congrArg mk hs) (congrArg mk ht) := by
  cases hs; cases ht; simp

lemma homOfEq_mkHom {S S' T T' : Vertex F} (e : Edge F S T)
    {hs : mk S = mk S'} {ht : mk T = mk T'} :
    Quiver.homOfEq (mkHom e) hs ht =
      mkHom (edgeOfEq e (mk_inj.mp hs) (mk_inj.mp ht)) := by
  rw [mkHom_edgeOfEq]

/-- Remove `out (mk ...)` pairs from the front of a chain of compositions. -/
@[simps]
def edge_unit {S T : Vertex F}: Edge F (out (mk S)) (out (mk T)) ≃ Edge F S T where
  toFun e := edgeOfEq e (out_mk S) (out_mk T)
  invFun e := edgeOfEq e (out_mk S).symm (out_mk T).symm
  left_inv e := by simp
  right_inv e := by simp

/-- Remove `out (mk ...)` pairs from the back of a chain of compositions. -/
@[simps]
def edge_unit_whisker {G : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v', u'} G]
    {S T : Vertex F} (f : Vertex F → Vertex G) :
    Edge G (f <| out (mk S)) (f <| out (mk T)) ≃ Edge G (f S) (f T) where
  toFun e := edgeOfEq e (congrArg f (out_mk S)) (congrArg f (out_mk T))
  invFun e := edgeOfEq e (congrArg f (out_mk S)).symm (congrArg f (out_mk T)).symm
  left_inv e := by simp
  right_inv e := by simp

@[simps!]
noncomputable def hom_unit {s t : ofFunctor F} : (mk (out s) ⟶ mk (out t)) ≃ (s ⟶ t) :=
  equivShrink _ |>.symm.trans edge_unit |>.trans <| equivShrink _

/-- Convenience recursor for working with `ofFunctor` output. -/
@[elab_as_elim]
noncomputable def recOn_mk {motive : ofFunctor F → Sort*}
    (x : ofFunctor F) (h : (X : Vertex F) → motive (mk X)) : motive x :=
  Shrink.rec h x

/-- Convenience recursor for working with `ofFunctor` output. (Cannot be a `cases_eliminator`
as it would be used for all homs in all quivers.) -/
@[elab_as_elim]
noncomputable def recOn_mkHom
    {motive : (x y : ofFunctor F) → (x ⟶ y) → Sort*}
    {x y : ofFunctor F} (g : x ⟶ y)
    (h : {X Y : Vertex F} → (G : Edge F X Y) → motive (mk X) (mk Y) (mkHom G)) :
    motive x y g :=
  recOn_mk x (motive := (∀ g, motive · y g)) (fun _ ↦
    recOn_mk y fun _ g ↦
      Shrink.rec
        (fun f ↦ h (edgeOfEq f (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _))) g) g

@[simp]
lemma recOn_mk_mk {motive : ofFunctor F → Sort*}
    (x : Vertex F) (h : (X : Vertex F) → motive (mk X)):
    Shrink.rec h (mk x) = h x := by
  simp only [mk, Shrink.rec, eqRec_eq_cast, cast_eq_iff_heq]
  rw [Equiv.symm_apply_apply]

@[simp]
lemma recOn_mkHom_mkHom {motive : (x y : ofFunctor F) → (x ⟶ y) → Sort*}
    {X Y : Vertex F} (G : Edge F X Y)
    (h : {X Y : Vertex F} → (G : Edge F X Y) → motive (mk X) (mk Y) (mkHom G)) :
    recOn_mkHom (mkHom G) h = h G := by
  simp only [mkHom, Equiv.trans_apply, Edge.equivOfEq_symm_apply, recOn_mkHom, recOn_mk,
    recOn_mk_mk]
  erw [Shrink.rec_equivShrink]
  congr

@[simp]
lemma mkHom_outHom {F : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v, u, w} F] {s t : ofFunctor F}
    (f : s ⟶ t) : mkHom (outHom f) = Quiver.homOfEq f (mk_out s).symm (mk_out t).symm := by
  cases' f using recOn_mkHom with s t f
  rw [outHom_mkHom, mkHom_edgeOfEq]

@[simps]
noncomputable def mkEquiv : (Vertex F) ≃ (ofFunctor F) := ⟨mk, out, out_mk, mk_out⟩

@[simps]
noncomputable def mkHomEquiv {S T : Vertex F} : (Edge F S T) ≃ (mk S ⟶ mk T) where
  toFun := mkHom
  invFun e := edgeOfEq (outHom e) (out_mk S) (out_mk T)
  left_inv e := by simp
  right_inv e := by simp

/-- `ofFunctor` is functorial. -/
@[simps]
noncomputable instance functorial :
    Functorial (ofFunctor <| SmallAsQuivSubcategory.obj.{v, u, w} ·) where
  map' {F G} η := {
    obj := mk ∘ (η.app 0) ∘ out
    map := mkHom ∘ (⟨η.app 1 ·.1, by simp, by simp⟩) ∘ outHom
  }
  map_id' F := by
    fapply Prefunctor.ext'
    · intro X; cases X using recOn_mk; simp
    · intro X Y f; cases f using recOn_mkHom; simp
  map_comp' {F G H} η ϑ := by
    fapply Prefunctor.ext'
    · intro X; simp [SmallAsQuivSubcategory.comp_eq_comp, Quiv.comp_eq_comp]
    · intro X Y f; cases f using recOn_mkHom
      simp only [Function.comp_apply, SmallAsQuivSubcategory.comp_eq_comp,
        NatTrans.comp_app, FunctorToTypes.comp, types_comp_apply, outHom_mkHom, comp_eq_comp,
        Prefunctor.comp_obj, Prefunctor.comp_map]
      apply eq_of_heq
      rw [Quiver.homOfEq_heq_right_iff]
      congr <;> simp

@[simp]
lemma mk_nat {F G : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v, u, w} F] [SmallAsQuiv.{v, u, w} G]
    (μ : F ⟶ G) (X : Vertex F) :
    let μ : ((⟨F, ‹_›⟩ : SmallAsQuivSubcategory.{v, u, w}) ⟶ ⟨G, ‹_›⟩) := μ
    (map (ofFunctor <| SmallAsQuivSubcategory.obj.{v, u, w} ·) μ).obj (mk X)
      = mk (μ.app 0 X) := by
  simp

@[simp]
lemma mkHom_nat {F G : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v, u, w} F] [SmallAsQuiv.{v, u, w} G]
    (μ : F ⟶ G) {S T : Vertex F} (e : Edge F S T) :
    let μ : ((⟨F, ‹_›⟩ : SmallAsQuivSubcategory.{v, u, w}) ⟶ ⟨G, ‹_›⟩) := μ
    (map (ofFunctor <| SmallAsQuivSubcategory.obj.{v, u, w} ·) μ).map (mkHom e)
      = Quiver.homOfEq (mkHom (hom <| μ.app 1 e)) (by simp) (by simp) := by
  simp_rw [homOfEq_mkHom, functorial_map_map, Function.comp_apply, outHom_mkHom]
  congr

/-- `ofFunctor` respects isomorphisms: it maps isomorphic functors to isomorphic quivers. -/
@[simps!]
noncomputable def mapIso {F G : WalkingQuiver ⥤ Type w}
    [SmallAsQuiv.{v, u} F] [SmallAsQuiv.{v, u} G] (η : F ≅ G) : (ofFunctor F) ≅ (ofFunctor G) :=
  Functor.of (ofFunctor <| SmallAsQuivSubcategory.obj.{v, u, w} ·) |>.mapIso <|
     SmallAsQuivSubcategory.isoMk η

@[simp]
lemma mapIso_hom {F G : WalkingQuiver ⥤ Type w}
    [SmallAsQuiv.{v, u, w} F] [SmallAsQuiv.{v, u, w} G] (η : F ≅ G) :
    -- let η' := SmallAsQuivSubcategory.isoMk η
    (mapIso η).hom = { obj := mk ∘ (η.hom.app 0) ∘ out,
                       map := mkHom ∘ (⟨η.hom.app 1 ·.1, by simp, by simp⟩) ∘ outHom } := rfl

@[simp]
lemma mapIso_inv {F G : WalkingQuiver ⥤ Type w}
    [SmallAsQuiv.{v, u, w} F] [SmallAsQuiv.{v, u, w} G] (η : F ≅ G) :
    -- let η' := SmallAsQuivSubcategory.isoMk η
    (mapIso η).inv = { obj := mk ∘ (η.inv.app 0) ∘ out,
                       map := mkHom ∘ (⟨η.inv.app 1 ·.1, by simp, by simp⟩) ∘ outHom } := rfl

end ofFunctor
    -- _
    -- simp [FullSubcategory.l]
end
section universe w' w v u v' u'

variable (F) [SmallAsQuiv.{v, u, max w v u} F]
open ofFunctor SmallAsQuivSubcategory
-- attribute [-simp] Shrink.out


/-- `asFunctor` and `ofFunctor` at the same universe level compose to the identity
(up to isomorphism). -/
@[simps!]
noncomputable def asFunctor_ofFunctor_iso : asFunctor.{w} (ofFunctor F) ≅ F :=
  NatIso.ofComponents
    (fun
      | 0 =>  { hom X := out X.1, inv X := .up <| ofFunctor.mk X }
      | 1 =>  { hom f := (ofFunctor.outHom f.2.2).1,
                inv e := ⟨⟨ofFunctor.mk (src e)⟩, ⟨ofFunctor.mk (tgt e)⟩, ofFunctor.mkHom (hom e)⟩,
                hom_inv_id := by
                  ext ⟨s, t, e⟩
                  apply asFunctor.hom_ext
                  all_goals simp [src, tgt, asHom, types_comp_apply, Quiver.homOfEq]
                inv_hom_id := by ext; simp [asHom, types_comp_apply, edgeOfEq] })


open Functor.essImage in
/-- The essential image of `asFunctor.{w, v, u}` is equivalent to the subcategory of functors
`WalkingQuiver ⥤ Type max w v u` that are `SmallAsQuiv.{v, u}`. -/
@[simps! +simpRhs]
noncomputable def asFunctor.essImageEquiv :
    (Functor.of asFunctor.{w, v, u}).EssImageSubcategory ≌ SmallAsQuivSubcategory.{v, u} :=
  Equivalence.ofFullSubcategory fun Q ↦
    ⟨fun h ↦ prop_of_iso SmallAsQuiv.{v, u} (getIso h) inferInstance,
      fun _ ↦ ⟨ofFunctor Q, ⟨asFunctor_ofFunctor_iso Q⟩⟩⟩



/-- The category of quivers `Quiv.{v, u}` is equivalent to the subcategory of functors
`WalkingQuiver ⥤ Type max w v u` that are `SmallAsQuiv.{v, u}`. -/
-- @[simps!?]
noncomputable def quivEquiv : Quiv.{v, u} ≌ SmallAsQuivSubcategory.{v, u, max w v u} :=
  have : (Functor.of asFunctor.{w, v, u}).toEssImage.IsEquivalence := inferInstance
  let ε := (Functor.of asFunctor.{w, v, u}).toEssImage.asEquivalence.trans asFunctor.essImageEquiv
  let ι : ε.inverse ≅ (Functor.of (ofFunctor.{v, u} <| obj ·)) :=
    let ι' := ε.counitIso ≪≫
      NatIso.ofComponents (isoMk <| asFunctor_ofFunctor_iso ·.1 |>.symm)
      @fun {F G} (η : F.1 ⟶ G.1) ↦ by
        rcases F with ⟨F, hF⟩; rcases G with ⟨G, hG⟩
        change F ⟶ G at η
        simp only [Functor.of, ε]
        ext (z | o) x
        · simp [ULift.map, SmallAsQuivSubcategory.comp_eq_comp]
        · apply asFunctor.hom_ext; rotate_right
          · simp [ULift.map, SmallAsQuivSubcategory.comp_eq_comp, hom]
            congr! 1; rotate_right
            · simp_all [Subtype.heq_iff_coe_eq]
            all_goals simp
          all_goals simp [ULift.map, SmallAsQuivSubcategory.comp_eq_comp]
    (Functor.FullyFaithful.whiskeringRight (ε.fullyFaithfulFunctor) _).preimageIso ι'
  ε.changeInverse ι

@[simp]
lemma quivEquiv_functor :
    quivEquiv.{w, v, u}.functor =
      FullSubcategory.lift SmallAsQuiv.{v, u} (Functor.of asFunctor.{w, v, u}) inferInstance := rfl

@[simp]
lemma quivEquiv_inverse :
    quivEquiv.{w, v, u}.inverse = Functor.of (ofFunctor.{v, u} <| obj ·) := rfl


open SmallAsQuivSubcategory in
@[simps!]
noncomputable def ofFunctor_lift_asFunctor_iso :
    (FullSubcategory.lift SmallAsQuiv.{v, u} (Functor.of asFunctor.{w}) inferInstance) ⋙
      (Functor.of (ofFunctor.{v, u} <| obj ·) (I := ofFunctor.functorial)) ≅ 𝟭 _ :=
  quivEquiv.unitIso.symm


/-- `ofFunctor` and `asFunctor` compose to the identity (up to isomorphism), regardless of
`asFunctor`'s extra universe level. -/
@[simps!?]
noncomputable def ofFunctor_asFunctor_iso (V : Quiv.{v, u}) :
    ofFunctor (asFunctor.{w} V) ≅ V :=
  ofFunctor_lift_asFunctor_iso.{w, v, u}.app V

/-- The category `SmallAsQuivSubcategory.{v, u, max w v u}` is equivalent to the category
`SmallAsQuivSubcategory.{v, u, max w' v u}` for any `w', w`. -/
@[simps!, pp_with_univ] noncomputable def smallAsQuivSubcategoryEquiv :
    SmallAsQuivSubcategory.{v, u, max w v u} ≌ SmallAsQuivSubcategory.{v, u, max w' v u} :=
  quivEquiv.{w, v, u}.symm.trans quivEquiv.{w', v, u}

namespace quivEquiv

/-- `quivEquiv.{w}.functor` as a functor into `WalkingQuiver ⥤ Type w`. -/
@[simp]
noncomputable def inclusion :=
  quivEquiv.{w, v, u}.functor ⋙ fullSubcategoryInclusion SmallAsQuiv.{v, u}


-- In this section, we explicitly define `whiskerOf` and `whiskerAs` ourselves, because
-- `Equivalence.congrFoo` would create functors to and from `SmallAsQuivSubcategory`, not
-- just to `WalkingQuiver ⥤ Type w`.
variable {C : Type v'} [Category.{u'} C]
/-- Lift a functor `F : C ⥤ WalkingQuiver ⥤ Type max w v u` that satisfies
`∀ (X : C), SmallAsQuiv.{v, u} (F.obj X)` to a functor `F' : C ⥤ Quiv.{v, u}`. -/
@[simp]
noncomputable def whiskerOf (F : C ⥤ WalkingQuiver ⥤ Type max w v u)
    [hF : ∀ X, SmallAsQuiv.{v, u} (F.obj X)] : C ⥤ Quiv.{v, u} :=
  FullSubcategory.lift _ F hF ⋙ quivEquiv.{w, v, u}.inverse

/-- Lift a functor `F : C ⥤ Quiv.{v, u}` to a functor `F : C ⥤ WalkingQuiver ⥤ Type max w v u`. -/
@[simp]
noncomputable def whiskerAs
    (F : C ⥤ Quiv.{v, u}) : C ⥤ WalkingQuiver ⥤ Type max w v u :=
  F ⋙ quivEquiv.{w}.functor ⋙ fullSubcategoryInclusion _

/-- `whiskerAs.obj X` is `SmallAsQuiv.{v, u}` for all `X` -/
instance (F : C ⥤ Quiv.{v, u}) (X : C) : SmallAsQuiv.{v, u} (whiskerAs.{w} F |>.obj X) :=
  inferInstanceAs (SmallAsQuiv.{v, u} (quivEquiv.{w}.functor.obj (F.obj X)).obj)

@[simps!]
noncomputable def whiskerAs_whiskerOf
    (F : C ⥤ WalkingQuiver ⥤ Type max w v u) [hF : ∀ X, SmallAsQuiv.{v, u} (F.obj X)] :
    whiskerAs (whiskerOf F) ≅ F :=
  calc
  _ ≅ _ := (isoWhiskerRight (Functor.associator _ quivEquiv.{w}.inverse quivEquiv.{w}.functor).symm
    (fullSubcategoryInclusion _)).symm
  _ ≅ _ := isoWhiskerRight (isoWhiskerLeft (FullSubcategory.lift _ F hF) quivEquiv.{w}.counitIso) _
  _ ≅ _ := isoWhiskerRight (Functor.rightUnitor _) _
  _ ≅ _ := FullSubcategory.lift_comp_inclusion _ F hF

@[simps!]
noncomputable def whiskerOf_whiskerAs (F : C ⥤ Quiv.{v, u}) :
    whiskerOf (whiskerAs F) ≅ F :=
  calc
  _ ≅ _ := isoWhiskerRight (FullSubcategory.lift_inclusion _ (F ⋙ quivEquiv.{w}.functor))
              quivEquiv.{w}.inverse
  _ ≅ _ := Functor.associator _ _ _
  _ ≅ _ := isoWhiskerLeft F quivEquiv.{w}.unitIso.symm


section as
variable {U V : Quiv.{v, u}} (F G : SmallAsQuivSubcategory.{v, u, max w v u})

@[simp]
lemma functor_obj : (quivEquiv.{w}.functor.obj V).obj = V.asFunctor := rfl

@[simp]
lemma functor_map (f : U ⟶ V) : quivEquiv.{w}.functor.map f = map asFunctor f := rfl

@[simp]
lemma functor_vertex : Vertex (quivEquiv.{w}.functor.obj V).1 = ULift.{max w v} V.α := rfl

@[simp]
lemma functor_edge : Edges (quivEquiv.{w}.functor.obj V).1 =
  ((s t : ULift.{max w v} V) × (s.1 ⟶ t.1)) := rfl

#check asFunctor_ofFunctor_iso

@[simps!]
noncomputable def inverse_obj_spec :
    asFunctor (ofFunctor F.1) ≅ F.obj :=
  asFunctor_ofFunctor_iso F.1

variable {F G}

@[simp]
lemma inverse_map_spec (η : F ⟶ G) :
    quivEquiv.{w}.functor.map (quivEquiv.{w}.inverse.map η) =
      (asFunctor_ofFunctor_iso F.1).hom ≫ η ≫ (asFunctor_ofFunctor_iso G.1).inv := by
  ext (z | o) x
  · simp [asFunctor_ofFunctor_iso, Functor.asEquivalence, Functor.of,
      SmallAsQuivSubcategory.comp_eq_comp]; rfl
  · rcases x with ⟨s, t, e⟩
    apply asFunctor.hom_ext
    rotate_right
    · simp [Functor.of, hom]
      congr! <;> simp
    all_goals
      simp [asFunctor_ofFunctor_iso, Functor.asEquivalence, Functor.of,
        SmallAsQuivSubcategory.comp_eq_comp]; rfl

-- @[reassoc]
-- lemma asOfFunctor.unit_naturality_preimage
--     (η : asOfFunctor.{w}.functor.obj U ⟶ asOfFunctor.functor.obj V) :
--     asOfFunctor.unit.app U ≫ ofFunctor.functor.map η =
--       asOfFunctor.functor.preimage η ≫ asOfFunctor.unit.app V := by
--   have := asOfFunctor.functor.map_preimage η
--   set F := asOfFunctor.functor.preimage η
--   simp [← this]

-- @[reassoc]
-- lemma asOfFunctor.unitInv_naturality_preimage
--     (η : asOfFunctor.{w}.functor.obj U ⟶ asOfFunctor.functor.obj V) :
--     ofFunctor.functor.map η ≫ asOfFunctor.unitInv.app V =
--       asOfFunctor.unitInv.app U ≫ asOfFunctor.functor.preimage η := by
--   have := asOfFunctor.functor.map_preimage η
--   set F := asOfFunctor.functor.preimage η
--   simp [← this]

-- @[reassoc]
-- lemma asOfFunctor.counit_naturality_preimage
--     (η : ofFunctor.functor.obj F ⥤q ofFunctor.functor.obj G) :
--     asOfFunctor.functor.map η ≫ asOfFunctor.counit.app G =
--       asOfFunctor.counit.app F ≫ (ofFunctor.functor.preimage η) := by
--   have := ofFunctor.functor.map_preimage η
--   set η := ofFunctor.functor.preimage η
--   simp [← this]

end quivEquiv.as

def smallAsQuiv_ofMono {F G : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v, u, w} G]
    (μ : F ⟶ G) [hμ : Mono μ] : SmallAsQuiv.{v, u, w} F where
  small_vertex := small_of_injective (f := μ.app 0) (hμ' 0)
  small_edge s t :=
    let μ₁ (e : Edge F s t) := natTransEdge μ e
    have μ₁_inj : μ₁.Injective := Subtype.map_injective _ (hμ' 1)
    small_of_injective.{v, w, w} μ₁_inj
where
  hμ' m : (μ.app m).Injective := by
    simp_rw [NatTrans.mono_iff_mono_app, CategoryTheory.mono_iff_injective] at hμ
    exact hμ m

/-- Similarly to **Type**, two vertices are identified in a filtered colimit iff
they are already identified in some quiver in the base of the cone. -/
lemma filteredColimit_inj [UnivLE.{w, v}] {J : Type w} [Category.{w} J] [IsFilteredOrEmpty J]
    (F : J ⥤ WalkingQuiver ⥤ Type v) (c : ColimitCocone F) (q₀ : WalkingQuiver)
    {i j : J} (xᵢ : F.obj i |>.obj q₀) (xⱼ : F.obj j |>.obj q₀) :
    (c.1.ι.app i).app q₀ xᵢ = (c.1.ι.app j).app q₀ xⱼ ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).app q₀ xᵢ = (F.map g).app q₀ xⱼ := by
  rcases c with ⟨c, hc⟩
  have c_nat := c.ι.naturality
  let iso := (Functor.const J).mapIso (hc.coconePointUniqueUpToIso (pointwiseIsColimit F))
  have i_nat := iso.inv.naturality
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
    Cocones.forget_obj, pointwiseCocone_pt, Category.id_comp] at c_nat i_nat
  constructor <;> intro h
  case mpr =>
    obtain ⟨k, f, g, hfg⟩ := h
    simp_rw [← c_nat f, ← c_nat g, NatTrans.comp_app, types_comp_apply, hfg]
  case mp =>
    have h_inj {i q₀} : iso.inv.app i |>.app q₀ |>.Injective :=
      (Function.LeftInverse.injective (g := iso.hom.app i |>.app q₀)
        (fun x ↦ by simp_rw [← types_comp_apply, Iso.inv_hom_id_app_app]; simp))
    have h_iso : c.ι = (pointwiseCocone F).ι ≫ iso.inv := by ext j q₀ x; simp [iso]
    obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs i j
    simpa [h_iso, ← i_nat f, ← i_nat g, h_inj.eq_iff, Types.FilteredColimit.colimit_eq_iff] using h


section variable {F G : WalkingQuiver ⥤ Type w} [SmallAsQuiv.{v, u, w} F]

/-- For an arrow `ε : F ⟶ G` between presheafs `F G : WalkingQuiver ⥤ Type w`,
`Epi ε` is sufficient only to prove that the vertex types of `G` are small, because
the identification of vertices under `ε` may combine a `u`-sized collection of vertices
into a single vertex; if it does not also identify a similar proportion of edges, then
the hom-types of `G` may be as large as `max v u`. Proof that the hom-types are small
must be found separately.

Here, if the identification of vertices under `ε` does not result in any hom-types larger
than `v` even before identifying edges, then we can certainly infer
`SmallAsQuiv.{v, u} G` from `Epi ε` and `SmallAsQuiv.{v, u} F`.

(This is almost just a restatement of the definition in terms of pre-images, but it
underlies the next few theorems.) -/
lemma smallAsQuiv_ofEpi_ofSmallEdges
    (ε : F ⟶ G) [hε₁ : Epi ε] (hε₂ : ∀ (s t : Vertex G), Small.{v}
    (⋃ (s' ∈ ε.app 0 ⁻¹' {s}) (t' ∈ ε.app 0 ⁻¹' {t}), {e.1 | e : Edge F s' t'})) :
    SmallAsQuiv.{v, u, w} G where
  small_vertex := small_of_surjective (f := ε.app 0) (hε' 0)
  small_edge s t :=
    let ε₁ := Set.restrictPreimage {e | src e = s ∧ tgt e = t} (ε.app 1)
    have ε₁_surj : ε₁.Surjective := (hε' 1).restrictPreimage _
    let e_st := (ε.app 1 ⁻¹' {e | src e = s ∧ tgt e = t})
    let e_st' := ⋃ (s' ∈ ε.app 0 ⁻¹' {s}) (t' ∈ ε.app 0 ⁻¹' {t}), {e.1 | e : Edge F s' t'}
    have : Small.{v} e_st := by
      have subset : e_st ⊆ e_st' := by
        intro e he
        simp [e_st] at he
        simp [he, e_st']
      exact small_subset subset
    small_of_surjective.{v, w, w} ε₁_surj
where
  hε' m : (ε.app m).Surjective := by
    simp_rw [NatTrans.epi_iff_epi_app, CategoryTheory.epi_iff_surjective] at hε₁
    exact hε₁ m

/-- For an arrow `ε : F ⟶ G` between presheafs `F G : WalkingQuiver ⥤ Type w`,
`Epi ε` is sufficient only to prove that the vertex types of `G` are small, because
the identification of vertices under `ε` may combine a `u`-sized collection of vertices
into a single vertex; if it does not also identify a similar proportion of edges, then
the hom-types of `G` may be as large as `max v u`. Proof that the hom-types are small
must be found separately.

Here, if the identification of vertices under `ε` does not result in any hom-types larger
than `v` even before identifying edges, then we can certainly can infer
`SmallAsQuiv.{v, u} G` from `Epi ε` and `SmallAsQuiv.{v, u} F`.

(The primed variant uses a subtype instead of a union set, which can be deconstructed
into concrete objects without repeated invocation of choice.) -/
lemma smallAsQuiv_ofEpi_ofSmallEdges'
    (ε : F ⟶ G) [hε₁ : Epi ε] (hε₂ : ∀ (s t : Vertex G), Small.{v}
    ((s' : ε.app 0 ⁻¹' {s}) × (t' : ε.app 0 ⁻¹' {t}) × (Edge F s' t'))) :
    SmallAsQuiv.{v, u, w} G := by
  suffices ∀ s t, ((s' : ε.app 0 ⁻¹' {s}) × (t' : ε.app 0 ⁻¹' {t}) × (Edge F s' t')) ≃
      ⋃ (s' ∈ ε.app 0 ⁻¹' {s}) (t' ∈ ε.app 0 ⁻¹' {t}), {e.1 | e : Edge F s' t'} by
    replace hε₂ s t := small_congr (this s t) |>.mp <| hε₂ s t
    exact smallAsQuiv_ofEpi_ofSmallEdges ε hε₂
  intro s t
  set e_st' := ⋃ (s' ∈ ε.app 0 ⁻¹' {s}) (t' ∈ ε.app 0 ⁻¹' {t}), {e.1 | e : Edge F s' t'}
  have e_st'_prod : e_st' = ⋃ (st' : (ε.app 0 ⁻¹' {s}) × (ε.app 0 ⁻¹' {t})),
    {e.1 | e : Edge F st'.1 st'.2} := by simp [e_st', Set.iUnion_prod']
  rw [e_st'_prod]
  have disjoint (st₁ st₂ : (ε.app 0 ⁻¹' {s}) × (ε.app 0 ⁻¹' {t})) (h : st₁ ≠ st₂) :=
    edge_disjoint (st₁.1.1, st₁.2.1) (st₂.1.1, st₂.2.1) (by contrapose! h; aesop)
  calc
  _ ≃ _ := Equiv.sigmaAssocProd.symm
  _ ≃ _ := by
    convert (Set.unionEqSigmaOfDisjoint disjoint).symm with ⟨s, t⟩
    simp

/-- For an arrow `ε : F ⟶ G` between presheafs `F G : WalkingQuiver ⥤ Type w`,
if the preimage under `ε` of every vertex in `G` is `v`-small, then
we can infer `SmallAsQuiv.{v, u} G` from `Epi ε` and `SmallAsQuiv.{v, u} F`. -/
lemma smallAsQuiv_ofEpi_ofSmallPreimages
    (ε : F ⟶ G) [hε₁ : Epi ε] (hε₂ : ∀ (Y : Vertex G), Small.{v} (ε.app 0 ⁻¹' {Y})) :
    SmallAsQuiv.{v, u, w} G := by
  apply smallAsQuiv_ofEpi_ofSmallEdges' ε
  intro s t
  refine ⟨⟨(s' : Shrink.{v, w} (ε.app 0 ⁻¹' {s})) × (t' : Shrink.{v, w} (ε.app 0 ⁻¹' {t})) ×
    Shrink.{v, w} (Edge F s'.out t'.out), ⟨?h⟩⟩⟩
  let σ x := equivShrink (ε.app 0 ⁻¹' {x}) |>.symm
  calc
  _ ≃ _ := Equiv.sigmaAssocProd.symm
  _ ≃ _ := Equiv.sigmaCongrLeft' <| Equiv.prodCongr (equivShrink _) (equivShrink _)
  _ ≃ (ab : _) × Shrink.{v, w} (Edge F (σ s ab.1) (σ t ab.2)) :=
    Equiv.sigmaCongrRight (fun _ ↦ equivShrink _)
  _ ≃ _ := Equiv.sigmaAssocProd
    (γ := fun s' t' ↦ Shrink.{v, w} <| Edge F (σ s s') (σ t t'))

/-- For an arrow `ε : F ⟶ G` between presheafs `F G : WalkingQuiver ⥤ Type w` with
`SmallAsQuiv.{v, u} F`, if `u ≤ v`, then certainly we can infer `SmallAsQuiv.{v, u} G`
from `Epi ε`. -/
def smallAsQuiv_ofEpi_ofSmall [UnivLE.{u, v}] (ε : F ⟶ G) [hε : Epi ε] : SmallAsQuiv.{v, u, w} G :=
  smallAsQuiv_ofEpi_ofSmallPreimages ε (fun Y ↦ Small.trans_univLE (ε.app 0 ⁻¹' {Y}))

end

/-
section of
universe v u w
variable {F G : SmallAsQuivSubcategory.{v, u, max w v u}}

-- -- @[simps?!]
-- noncomputable def ofFunctor.functor_obj :
--     (ofFunctor.functor.{v, u, w}.obj F) ≅ ofFunctor F.1 :=
--   -- hom := {
--   --   obj X := by
--   --     simp [functor, asOfFunctor, toSmallMax, Functor.asEquivalence, Functor.inv,
--   --     essImageEquivMax, Functor.EssImage.comp_equiv_ofFullyFaithful,
--   --     smallEquivULiftEssImage] at X
--   --     conv at X =>
--   --       enter [1, 1, 2]
--   --       rw [FullSubcategory.lift_comp_map]
--   --     simp [FullSubcategory.lift] at X
--   --     let ε := (asFunctor.toEssImage ⋙ essImageEquivMax.functor).objObjPreimageIso F
--   --   map := _
--   -- }
--   -- inv := _
--   let ι : F ≅ asOfFunctor.functor.obj (asOfFunctor.inverse.obj F) :=
--     asOfFunctor.counitIso.symm.app F
--   -- let ι := asOfFunctor.functor.objObjPreimageIso F |>.symm
--   let V := asOfFunctor.inverse.obj F
--   let ι' := asOfFunctor.inverse.mapIso ι ≪≫ (asOfFunctor.unitIso.app V).symm
--   let ι := ofFunctor.mapIso (fullSubcategoryInclusion _ |>.mapIso ι) |>.symm
--   ι' ≪≫ (ofFunctor_asFunctor_obj_iso _).symm ≪≫ ofFunctor.uliftFunctorIso.symm ≪≫ ι

@[simp]
lemma ofFunctor.functor_obj_hom_obj (X : functor.obj F) :
    functor_obj.hom.obj X =
      ofFunctor.mk ((asOfFunctor.counitIso.hom.app F).app 0
        (Equiv.ulift.symm (Equiv.ulift.symm X))) := by
  simp only [functor_obj, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
  Iso.app_inv, Equivalence.inverse_counitInv_comp, Category.id_comp, Functor.id_obj,
  uliftFunctorIso, isoOfEquiv, Quiv.comp_eq_comp, Prefunctor.comp, mapIso_inv,
  fullSubcategoryInclusion, Function.comp_apply, out, Shrink.mapEquiv, Shrink.out,
  inducedFunctor_obj, asOfFunctor.functor_obj, ofFunctor_asFunctor_obj_iso_inv_obj]
  erw [(equivShrink (Vertex (asFunctor.obj (asOfFunctor.inverse.obj F) ⋙
      uliftFunctor.{w, max u v}))).symm_apply_apply,
    (equivShrink (Vertex (asFunctor.obj (asOfFunctor.inverse.obj F)))).symm_apply_apply]
  simp; rfl

@[simp]
lemma ofFunctor.functor_obj_inv_obj (X : ofFunctor F.1) :
    functor_obj.inv.obj X =
      Equiv.ulift (Equiv.ulift <| (asOfFunctor.counitIso.inv.app F).app 0 (ofFunctor.out X)) := by
  simp only [functor_obj, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
  Iso.symm_inv, Iso.app_hom, Iso.app_inv, Equivalence.unit_inverse_comp, Category.id_comp,
  Functor.id_obj, Quiv.id_obj_eq_id_ext, uliftFunctorIso, isoOfEquiv, Quiv.comp_eq_comp,
  Prefunctor.comp, mapIso_hom, fullSubcategoryInclusion, Function.comp_apply, mk,
  Shrink.mapEquiv, Shrink.out, inducedFunctor_obj, ofFunctor_asFunctor_obj_iso_hom_obj,
  Equiv.trans_apply, asOfFunctor.functor_obj]
  erw [(equivShrink (Vertex (asFunctor.obj (asOfFunctor.inverse.obj F)))).symm_apply_apply,
  (equivShrink (Vertex (asFunctor.obj (asOfFunctor.inverse.obj F) ⋙
    uliftFunctor.{w, max u v}))).symm_apply_apply]
  simp; rfl
  -- simp_rw [← Prefunctor.comp_obj, ← Quiv.comp_eq_comp, asOfFunctor.unitIso.hom_inv_id_app]
  -- simp; rfl


-- example : (fun {X Y} (f : X ⟶ Y) ↦ (@ofFunctor.functor_obj F).hom.map f) = ?_ := by
--   unfold ofFunctor.functor_obj
--   simp only [Iso.trans_hom, Functor.id_obj]
--   simp
--   ext s t e
--   simp only [Quiv.comp_eq_comp, Prefunctor.comp_map]
  -- conv_lhs =>
  --   enter [3, 2, 2, 2]
  --   change (asOfFunctor.unitInv.app (asOfFunctor.inverse.obj F)).map e

  -- checkpoint simp [ofFunctor_asFunctor_obj_iso, ofFunctor.uliftFunctorIso, Quiv.comp_eq_comp,
  -- isoOfEquiv, Prefunctor.comp]
  -- ext X
  -- -- conv_lhs =>
  -- --   enter [X]
  -- erw [(equivShrink (Vertex (asFunctor.obj (asOfFunctor.inverse.obj F)))).symm_apply_apply,
  -- ofFunctor.out, Shrink.out,
  -- (equivShrink (Vertex (asOfFunctor.functor.obj (asOfFunctor.inverse.obj F)).obj)).symm_apply_apply,
  -- ]

  -- erw [asOfFunctor.unit_app_inverse]

-- @[simp]
noncomputable def ofFunctor.functorMk (X : Vertex F.1) : ofFunctor.functor.obj F :=
  ofFunctor.functor_obj.inv.obj <| ofFunctor.mk X

-- @[simp]
noncomputable def ofFunctor.functorMkHom {S T : Vertex F.1} (E : Edge F.1 S T) :
    ofFunctor.functorMk S ⟶ ofFunctor.functorMk T :=
  ofFunctor.functor_obj.inv.map <| ofFunctor.mkHom E

-- @[simp]
noncomputable def ofFunctor.functorOut (X : ofFunctor.functor.obj F) : Vertex F.1 :=
  out (ofFunctor.functor_obj.hom.obj X)

-- @[simp]
noncomputable def ofFunctor.functorOutHom {s t : ofFunctor.functor.obj F}
    (f : s ⟶ t) : Edge F.1 (ofFunctor.functorOut s) (ofFunctor.functorOut t) :=
  outHom (ofFunctor.functor_obj.hom.map f)

@[simp]
lemma ofFunctor.functorMkOut (X : Vertex F.1) :
    ofFunctor.functorOut (ofFunctor.functorMk X) = X := by
  unfold ofFunctor.functorOut ofFunctor.functorMk
  simp

@[simp]
lemma ofFunctor.functorOutMk (X : ofFunctor.functor.obj F) :
    ofFunctor.functorMk (ofFunctor.functorOut X) = X := by
  unfold ofFunctor.functorOut ofFunctor.functorMk
  rw [mk_out, hom_inv_id_obj]

@[simps]
noncomputable def ofFunctor.functorMkEquiv : (Vertex F.1) ≃ (ofFunctor.functor.obj F) where
  toFun := ofFunctor.functorMk
  invFun := ofFunctor.functorOut
  left_inv := functorMkOut
  right_inv := functorOutMk

lemma ofFunctor.functorMk_injective : (@ofFunctor.functorMk F).Injective :=
  ofFunctor.functorMkEquiv.injective

lemma ofFunctor.functorOut_injective : (@ofFunctor.functorOut F).Injective :=
  ofFunctor.functorMkEquiv.symm.injective

@[simp]
lemma ofFunctor.functorMk_inj {X Y : Vertex F.1} :
    ofFunctor.functorMk X = ofFunctor.functorMk Y ↔ X = Y := by
  apply ofFunctor.functorMk_injective.eq_iff

@[simp]
lemma ofFunctor.functorOut_inj {X Y : ofFunctor.functor.obj F} :
    ofFunctor.functorOut X = ofFunctor.functorOut Y ↔ X = Y := by
  apply ofFunctor.functorOut_injective.eq_iff

@[simp]
lemma ofFunctor.functorMkOutHom {S T : Vertex F.1} (E : Edge F.1 S T) :
    functorOutHom (functorMkHom E) =
      edgeOfEq E (functorMkOut _).symm (functorMkOut _).symm := by
    ext
    rcases E with ⟨E, rfl, rfl⟩
    unfold functorOutHom functorMkHom
    simp only [inv_hom_id_map]
    rw [homOfEq_mkHom, outHom_mkHom, edgeOfEq_trans]

@[simp]
lemma ofFunctor.functorOutMkHom {s t : ofFunctor.functor.obj F} (e : s ⟶ t) :
    functorMkHom (functorOutHom e) =
      Quiver.homOfEq e (functorOutMk _).symm (functorOutMk _).symm := by
  unfold functorOutHom functorMkHom
  rw [mkHom_outHom, Prefunctor.homOfEq_map]
  simp

@[simp]
lemma ofFunctor.functorMkHom_edgeOfEq {S S' T T' : Vertex F.1} (E : Edge F.1 S T)
    (hS : S = S') (hT : T = T') :
    functorMkHom (edgeOfEq E hS hT) =
      Quiver.homOfEq (functorMkHom E)
        (congrArg functorMk hS) (congrArg functorMk hT) := by
  unfold functorMkHom
  simp

@[simp]
lemma ofFunctor.homOfEq_functorMkHom {S S' T T' : Vertex F.1} (E : Edge F.1 S T)
    (hs : functorMk S = functorMk S') (ht : functorMk T = functorMk T') :
    Quiver.homOfEq (functorMkHom E) hs ht =
      functorMkHom (edgeOfEq E (functorMk_inj.mp hs) (functorMk_inj.mp ht)) := by
  unfold functorMkHom
  simp

@[simps]
noncomputable def ofFunctor.functorMkHomEquiv {S T : Vertex F.1} :
    (Edge F.1 S T) ≃ (functorMk S ⟶ functorMk T) where
  toFun := ofFunctor.functorMkHom
  invFun f := edgeOfEq (ofFunctor.functorOutHom f) (by simp) (by simp)
  left_inv e := by simp
  right_inv e := by simp

/--Recurse on an `ofFunctor.functor.obj F` using `functorMk`.

This version allows/requires the user to specify their own cast, which may be
more ergonomic in heavily dependent contexts.-/
@[elab_as_elim]
noncomputable def ofFunctor.recOn' {motive : ofFunctor.functor.obj F → Sort*}
    (x : ofFunctor.functor.obj F) (functorMk : ∀ x, motive (ofFunctor.functorMk x))
    (cast : ∀ {x y}, (x = y) → motive x → motive y) : motive x :=
  cast (ofFunctor.functorMkEquiv.right_inv x) <| functorMk (ofFunctor.functorOut x)

/--Recurse on an `ofFunctor.functor.obj F` using `functorMk`, using `_root_.cast`. -/
@[elab_as_elim]
noncomputable def ofFunctor.recOn {motive : ofFunctor.functor.obj F → Sort*}
    (x : ofFunctor.functor.obj F) (functorMk : ∀ X, motive (ofFunctor.functorMk X)) : motive x :=
  ofFunctor.recOn' x functorMk (fun h ↦ cast (congrArg motive h))

/--Recurse on a hom between `ofFunctor.functor.obj F`s using `functorMkHom`.

This version allows/requires the user to specify their own casts, which may be
more ergonomic in heavily dependent contexts.-/
@[elab_as_elim]
noncomputable def ofFunctor.recOnHom'
    {motive : {s t : ofFunctor.functor.obj F} → (s ⟶ t) → Sort*}
    {s t : ofFunctor.functor.obj F} (e : s ⟶ t)
    (functorMkHom : ∀ {s t} (e : Edge F.1 s t), motive (functorMkHom e))
    -- (cast_obj : ∀ {x y}, (x = y) → motive x → motive y)
    (cast : ∀ {s t s' t'} {e : s ⟶ t} {e' : s' ⟶ t'} (hs : s = s') (ht : t = t'),
      (Quiver.homOfEq e hs ht = e') → motive e → motive e') : motive e := by
  cases' s using recOn' with S
  case cast _ rec hx => exact rec hx.symm
  cases' t using recOn' with T
  case cast _ rec hx => exact rec hx.symm
  refine cast ?hs ?ht ?he (functorMkHom (ofFunctor.functorOutHom e)) <;> simp

/--Naturality of `functorMk`. Can't be an actual `NatTrans` due to universe level
mismatch.-/
@[simp]
lemma ofFunctor.functorMk_nat
    (η : F ⟶ G) (X : Vertex F.1) :
    (ofFunctor.functor.map η).obj (functorMk X) = functorMk (η.app 0 X) := by
  unfold functorMk
  simp [functor]
  have nat :=
    congrArg (·.app 0 X) (asOfFunctor.counitInv.naturality η)
  simp_rw [Functor.comp_map, Functor.id_map] at nat
  erw [NatTrans.comp_app, types_comp_apply] at nat
  rw [nat, SmallAsQuivSubcategory.comp_eq_comp, NatTrans.comp_app, types_comp_apply]
  congr

end of
-/
#min_imports
