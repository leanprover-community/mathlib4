/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/

import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Generator.Basic

/-!# Shapes in Quiv

In this file, we define a number of quivers, most of which have corresponding notations:
* The `Empty` quiver, which is initial
* The single-vertex zero-edge quiver `Vert`, with the notation `⋆`
* The single-vertex single-edge quiver `Point`, with the notation `⭮`, which is terminal
* The `Interval` quiver, with the notation `𝕀`

All notations are duplicated: once for when universe levels can be inferred, and once to
allow explicit universe levels to be given.

## TODO
* The subobject classifier in `Quiv`

-/

namespace CategoryTheory.Quiv
universe v u v₁ u₁ v₂ u₂
open Limits

/-- The empty quiver, with no vertices and no edges. -/
def Empty := let _ := PUnit.{v}; PEmpty.{u + 1}

instance : Quiver.{v + 1} Empty.{v} where
  Hom _ _ := PEmpty

instance : IsEmpty Empty where
  false := PEmpty.elim

/-- The single-vertex quiver, with one vertex and no edges. -/
def Vert := let _ := PUnit.{v}; PUnit.{u + 1}

instance : Quiver.{v + 1} Vert.{v} where
  Hom _ _ := PEmpty

@[inherit_doc Vert] scoped notation "⋆" => Vert
set_option quotPrecheck false in
@[inherit_doc Vert] scoped notation "⋆.{" v ", " u "}" => Vert.{v, u}

/-- Prefunctors out of `⋆` are just single objects. -/
def Vert.prefunctor {V : Type u₂} [Quiver.{v₂} V] (v : V) : ⋆.{v₁, u₁} ⥤q V :=
  {obj := fun _ ↦ v, map := nofun}

/-- Prefunctors out of `⋆` are equal if they point to the same object. -/
@[ext]
lemma Vert.prefunctor.ext {V : Type u₂} [Quiver.{v₂} V] {F G : ⋆.{v₁, u₁} ⥤q V}
    (h : F.obj ⟨⟩ = G.obj ⟨⟩) : F = G := by
  rcases F with ⟨F_obj, F_map⟩; rcases G with ⟨G_obj, G_map⟩
  simp at h
  rw [Prefunctor.mk.injEq]
  constructor
  · ext ⟨⟩; exact h
  · apply Function.hfunext rfl
    rintro ⟨⟩ ⟨⟩ -
    apply Function.hfunext rfl
    rintro ⟨⟩ ⟨⟩ -
    apply Function.hfunext rfl
    rintro ⟨⟩

/-- The interval quiver, with two points and a single edge `.left ⟶ .right`. -/
def Interval := let _ := PUnit.{v}; ULift.{u} WalkingPair

instance : Quiver.{v + 1} Interval.{v} where
  Hom
  | .up .left, .up .right => PUnit
  | _, _ => PEmpty

@[inherit_doc Interval] scoped notation "𝕀" => Interval
set_option quotPrecheck false in
@[inherit_doc Interval] scoped notation "𝕀.{" v ", " u "}" => Interval.{v, u}

/-- The left point of `𝕀`. -/
@[match_pattern] def Interval.left : 𝕀 := .up .left
/-- The right point of `𝕀`. -/
@[match_pattern] def Interval.right : 𝕀 := .up .right

@[match_pattern] alias 𝕀.left := Interval.left
@[match_pattern] alias 𝕀.right := Interval.right

@[simps] instance : Zero 𝕀 := ⟨Interval.left⟩
@[simps] instance : One 𝕀 := ⟨Interval.right⟩

/-- The single edge of `𝕀`. -/
@[simp, match_pattern] def Interval.hom : (0 : 𝕀.{v, u}) ⟶ 1 := ⟨⟩

alias 𝕀.hom := Interval.hom

/-- Convenience eliminator for building data on `𝕀.hom`.

Can't be a `cases_eliminator` or Lean will try to use it on every morphism in every quiver. -/
@[elab_as_elim]
def Interval.casesOn_hom {motive : {X Y : 𝕀} → (X ⟶ Y) → Sort*}
    {X Y : 𝕀} (f : X ⟶ Y) (hom : motive Interval.hom) : motive f :=
  match X, Y, f with
  | Interval.left, Interval.right, _ => hom

/-- Prefunctors out of `𝕀` are just single homs. -/
def Interval.prefunctor {V : Type u₂} [Quiver.{v₂} V] {X Y : V} (f : X ⟶ Y) : 𝕀.{u₁, v₁} ⥤q V :=
  { obj := fun | Interval.left => X | Interval.right => Y,
    map := @fun | Interval.left, Interval.right, Interval.hom => f }

/-- Prefunctors out of `𝕀` are equal if they point to the same hom. -/
@[ext (iff := false)]
lemma Interval.prefunctor.ext {V : Type u₂} [Quiver.{v₂} V] {F G : 𝕀.{u₁, v₁} ⥤q V}
    (h₀ : F.obj 0 = G.obj 0) (h₁ : F.obj 1 = G.obj 1)
    (h : F.map Interval.hom = Quiver.homOfEq (G.map Interval.hom) h₀.symm h₁.symm) : F = G := by
  rcases F with ⟨F_obj, F_map⟩; rcases G with ⟨G_obj, G_map⟩
  -- simp at h₀ h₁ h
  rw [Prefunctor.mk.injEq]
  constructor
  · ext (Interval.left | Interval.right) <;> simpa
  · apply Function.hfunext rfl
    rintro X X' ⟨⟩
    apply Function.hfunext rfl
    rintro Y Y' ⟨⟩
    apply Function.hfunext rfl
    simp_rw [heq_eq_eq, forall_eq']
    rintro f
    cases f using Interval.casesOn_hom
    simp at h
    simp [h, Quiver.homOfEq_heq]

lemma Interval.prefunctor.ext_iff {V : Type u₂} [Quiver.{v₂} V] {F G : 𝕀.{u₁, v₁} ⥤q V} :
    F = G ↔ ∃ (h₀ : F.obj 0 = G.obj 0) (h₁ : F.obj 1 = G.obj 1),
      F.map Interval.hom = Quiver.homOfEq (G.map Interval.hom) h₀.symm h₁.symm := by
  refine ⟨fun h => ?_, fun ⟨h₀, h₁, h⟩ => Interval.prefunctor.ext h₀ h₁ h⟩
  subst h; simp

/-- The topos-theory point as a quiver, with a single point (vertex with a self-loop) and no other
vertices or edges. -/
def Point := let _ := PUnit.{v}; PUnit.{u + 1}

instance : Quiver.{v + 1} Point.{v} where
  Hom _ _ := PUnit

@[inherit_doc Point] scoped notation "⭮" => Point
set_option quotPrecheck false in
@[inherit_doc Point] scoped notation "⭮.{" v ", " u "}" => Point.{v, u}

/-- Prefunctors out of `⭮` are just single self-arrows. -/
def Point.prefunctor {V : Type u₂} [Quiver.{v₂} V] {v : V} (α : v ⟶ v) : ⭮.{v₁, u₁} ⥤q V :=
  {obj := fun _ ↦ v, map := fun _ => α}

/-- Prefunctors out of `⭮` are equal if they point to the same self-arrow. -/
@[ext (iff := false)]
lemma Point.prefunctor.ext {V : Type u₂} [Quiver.{v₂} V] {F G : ⭮.{v₁, u₁} ⥤q V}
    (h_obj : F.obj ⟨⟩ = G.obj ⟨⟩)
    (h_map : F.map ⟨⟩ = Quiver.homOfEq (G.map ⟨⟩) h_obj.symm h_obj.symm) : F = G := by
  rcases F with ⟨F_obj, F_map⟩; rcases G with ⟨G_obj, G_map⟩
  rw [Prefunctor.mk.injEq]
  constructor
  · ext ⟨⟩; exact h_obj
  · apply Function.hfunext rfl
    rintro ⟨⟩ ⟨⟩ -
    apply Function.hfunext rfl
    rintro ⟨⟩ ⟨⟩ -
    apply Function.hfunext rfl
    simp only [heq_eq_eq, forall_eq']
    rintro ⟨⟩
    simp at h_map
    simp [h_map, Quiver.homOfEq_heq]

lemma Point.prefunctor.ext_iff {V : Type u₂} [Quiver.{v₂} V] {F G : ⭮.{v₁, u₁} ⥤q V} :
    F = G ↔ ∃ h_obj : F.obj ⟨⟩ = G.obj ⟨⟩,
      F.map ⟨⟩ = Quiver.homOfEq (G.map ⟨⟩) h_obj.symm h_obj.symm := by
  refine ⟨fun h => ?_, fun ⟨h_obj, h_map⟩ => Point.prefunctor.ext h_obj h_map⟩
  subst h; simp

/-- `Empty` is initial in **`Quiv`**. -/
def emptyIsInitial : IsInitial (of Empty) :=
  IsInitial.ofUniqueHom (fun X ↦ Prefunctor.mk PEmpty.elim PEmpty.elim)
    fun X ⟨obj, map⟩ ↦ by
      congr
      · ext ⟨⟩
      · apply Function.hfunext rfl
        rintro ⟨⟩

instance : HasInitial Quiv := emptyIsInitial.hasInitial

/-- The initial object in **Quiv** is `Empty`. -/
noncomputable def initialIsoEmpty : ⊥_ Quiv ≅ of Empty :=
  initialIsoIsInitial emptyIsInitial

/-- `⭮` is terminal in **Quiv**. -/
def pointIsTerminal : IsTerminal (of ⭮) :=
  IsTerminal.ofUniqueHom
    (fun X ↦ Prefunctor.mk (fun _ ↦ ⟨⟩) (fun _ ↦ ⟨⟩))
    fun X ⟨obj, map⟩ ↦ by congr

instance : HasTerminal Quiv := pointIsTerminal.hasTerminal

/-- The terminal object in **Quiv** is ⭮. -/
noncomputable def terminalIsoPoint : ⊤_ Quiv ≅ of ⭮ :=
  terminalIsoIsTerminal pointIsTerminal

end Quiv
end CategoryTheory
