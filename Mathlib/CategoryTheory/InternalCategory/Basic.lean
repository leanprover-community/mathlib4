/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Internal categories

This file provides a small, standalone record for an **internal category** in a category `C` with
pullbacks.

Mathlib does not currently provide a general internal-category theory (in the sense of “category
objects”). Since *Facets of Descent, II* uses internal categories prominently, we introduce this
minimal structure locally, designed to be upstreamable.

## Convention

We use the pullback `pullback dom cod` as the object of composable pairs. In this convention, an
element of `pullback dom cod` should be thought of as a pair `(f, g)` with `dom f = cod g`, and
`comp` returns the composite `g ≫ f`.
-/

open CategoryTheory

@[expose] public section

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

noncomputable section

/-- An internal category in a category with pullbacks. -/
structure InternalCategory where
  /-- The object of objects. -/
  obj : C
  /-- The object of morphisms. -/
  hom : C
  /-- The domain map `hom ⟶ obj`. -/
  dom : hom ⟶ obj
  /-- The codomain map `hom ⟶ obj`. -/
  cod : hom ⟶ obj
  /-- The identity-assigning map `obj ⟶ hom`. -/
  id : obj ⟶ hom
  /-- The composition map on composable pairs. -/
  comp : Limits.pullback dom cod ⟶ hom
  /-- `dom (id x) = x`. -/
  id_comp_dom : id ≫ dom = 𝟙 obj
  /-- `cod (id x) = x`. -/
  id_comp_cod : id ≫ cod = 𝟙 obj
  /-- `dom (g ≫ f) = dom g`. -/
  comp_comp_dom : comp ≫ dom = Limits.pullback.snd dom cod ≫ dom
  /-- `cod (g ≫ f) = cod f`. -/
  comp_comp_cod : comp ≫ cod = Limits.pullback.fst dom cod ≫ cod
  /-- Right identity: `f ≫ id (cod f) = f`. -/
  comp_id :
      Limits.pullback.lift (cod ≫ id) (𝟙 hom) (by
          simp [Category.assoc, id_comp_dom]) ≫
        comp =
      𝟙 hom
  /-- Left identity: `id (dom f) ≫ f = f`. -/
  id_comp :
      Limits.pullback.lift (𝟙 hom) (dom ≫ id) (by
          simp [Category.assoc, id_comp_cod]) ≫
        comp =
      𝟙 hom
  /-- Associativity of composition. -/
  assoc :
      let compObj := Limits.pullback dom cod
      let assocObj :=
        Limits.pullback (Limits.pullback.snd dom cod) (Limits.pullback.fst dom cod)
      let π12 : assocObj ⟶ compObj := Limits.pullback.fst _ _
      let π23 : assocObj ⟶ compObj := Limits.pullback.snd _ _
      let assocLeft : assocObj ⟶ compObj :=
        Limits.pullback.lift (π12 ≫ comp) (π23 ≫ Limits.pullback.snd dom cod) (by
          have h_assoc :
              π12 ≫ Limits.pullback.snd dom cod =
                π23 ≫ Limits.pullback.fst dom cod := by
            simpa [Category.assoc] using
              (Limits.pullback.condition (f := Limits.pullback.snd dom cod)
                (g := Limits.pullback.fst dom cod))
          have h_comp :
              Limits.pullback.fst dom cod ≫ dom =
                Limits.pullback.snd dom cod ≫ cod := by
            simpa using (Limits.pullback.condition (f := dom) (g := cod))
          calc
            (π12 ≫ comp) ≫ dom = (π12 ≫ Limits.pullback.snd dom cod) ≫ dom := by
              simpa [Category.assoc] using congrArg (fun k => π12 ≫ k) comp_comp_dom
            _ = (π23 ≫ Limits.pullback.fst dom cod) ≫ dom := by
              simpa [Category.assoc] using congrArg (fun k => k ≫ dom) h_assoc
            _ = (π23 ≫ Limits.pullback.snd dom cod) ≫ cod := by
              simpa [Category.assoc] using congrArg (fun k => π23 ≫ k) h_comp)
      let assocRight : assocObj ⟶ compObj :=
        Limits.pullback.lift (π12 ≫ Limits.pullback.fst dom cod) (π23 ≫ comp) (by
          calc
            (π12 ≫ Limits.pullback.fst dom cod) ≫ dom =
                (π12 ≫ Limits.pullback.snd dom cod) ≫ cod := by
              simpa [Category.assoc] using
                congrArg (fun k => π12 ≫ k) (Limits.pullback.condition (f := dom) (g := cod))
            _ = (π23 ≫ Limits.pullback.fst dom cod) ≫ cod := by
              simpa [Category.assoc] using
                congrArg (fun k => k ≫ cod)
                  (Limits.pullback.condition (f := Limits.pullback.snd dom cod)
                    (g := Limits.pullback.fst dom cod))
            _ = (π23 ≫ comp) ≫ cod := by
              simpa [Category.assoc] using congrArg (fun k => π23 ≫ k) comp_comp_cod.symm)
      assocLeft ≫ comp = assocRight ≫ comp

namespace InternalCategory

attribute [simp, reassoc] id_comp_dom id_comp_cod comp_comp_dom comp_comp_cod

end InternalCategory

end

end CategoryTheory
