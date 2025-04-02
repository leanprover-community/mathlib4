import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Generator.Basic

namespace CategoryTheory.Quiv
universe v u v₁ u₁ v₂ u₂
open Limits

def Empty : Quiv.{v, u} := ⟨PEmpty, ⟨fun _ _ ↦ PEmpty⟩⟩

instance : IsEmpty Empty where
  false := PEmpty.elim

def Vert : Quiv.{v, u} := ⟨PUnit, ⟨fun _ _ ↦ PEmpty⟩⟩

scoped notation "⋆" => Vert
set_option quotPrecheck false in
scoped notation "⋆.{" v ", " u "}" => Vert.{v, u}

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr in
@[app_delab Bundled.α]
def delab_vert : Delab :=
  whenPPOption getPPNotation <| do
  let #[_, α] := (← getExpr).getAppArgs | failure
  unless α.isConstOf ``Vert do failure
  `(⋆)

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


def Interval : Quiv.{v, u} :=
  ⟨ULift WalkingPair,
    ⟨fun
      | .up .left, .up .right => PUnit
      | _, _ => PEmpty⟩
  ⟩

scoped notation "𝕀" => Interval
set_option quotPrecheck false in
scoped notation "𝕀.{" v ", " u "}" => Interval.{v, u}

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr in
@[app_delab Bundled.α]
def delab_interval : Delab :=
  whenPPOption getPPNotation <| do
  let #[_, α] := (← getExpr).getAppArgs | failure
  unless α.isConstOf ``Interval do failure
  `(𝕀)

@[match_pattern] def Interval.left : 𝕀 := .up .left
@[match_pattern] def Interval.right : 𝕀 := .up .right

@[match_pattern] alias 𝕀.left := Interval.left
@[match_pattern] alias 𝕀.right := Interval.right

@[simps] instance : Zero 𝕀 := ⟨Interval.left⟩
@[simps] instance : One 𝕀 := ⟨Interval.right⟩

@[simp, match_pattern]
def Interval.hom : (0 : 𝕀.{v, u}) ⟶ 1 := ⟨⟩

alias 𝕀.hom := Interval.hom

@[elab_as_elim]
def Interval.casesOn_hom {motive : {X Y : 𝕀} → (X ⟶ Y) → Sort*}
    {X Y : 𝕀} (f : X ⟶ Y) (hom : motive Interval.hom) : motive f :=
  match X, Y, f with
  | Interval.left, Interval.right, _ => hom

/-- Prefunctors out of `𝕀` are just single homs. -/
def Interval.prefunctor {V : Type u₂} [Quiver.{v₂} V] {X Y : V} (f : X ⟶ Y) : 𝕀.{u₁, v₁} ⥤q V :=
  { obj := fun | Interval.left => X | Interval.right => Y,
    map := @fun | Interval.left, Interval.right, Interval.hom => f }

/--Prefunctors out of `𝕀` are equal if they point to the same hom.-/
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
    F = G ↔ ∃ h₀ : F.obj 0 = G.obj 0, ∃ h₁ : F.obj 1 = G.obj 1,
      F.map Interval.hom = Quiver.homOfEq (G.map Interval.hom) h₀.symm h₁.symm := by
  refine ⟨fun h => ?_, fun ⟨h₀, h₁, h⟩ => Interval.prefunctor.ext h₀ h₁ h⟩
  subst h; simp

def Point : Quiv.{v, u} :=
  ⟨PUnit, ⟨fun _ _ ↦ PUnit⟩⟩

scoped notation "⭮" => Point
set_option quotPrecheck false in
scoped notation "⭮.{" v ", " u "}" => Point.{v, u}

/--Prefunctors out of `⭮` are just single self-loops.-/
def Point.prefunctor {V : Type u₂} [Quiver.{v₂} V] {v : V} (α : v ⟶ v) : ⭮.{v₁, u₁} ⥤q V :=
  {obj := fun _ ↦ v, map := fun _ => α}

/--Prefunctors out of `⭮` are equal if they point to the same self-loop.-/
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

def emptyIsInitial : IsInitial Empty := ⟨
    fun ⟨pt, _⟩ ↦ Prefunctor.mk (PEmpty.elim) (PEmpty.elim),
    by simp,
    fun ⟨pt, _⟩ ⟨obj, map⟩ h ↦ by
      congr
      ext ⟨⟩
      apply Function.hfunext rfl
      simp
  ⟩

instance : HasInitial Quiv := emptyIsInitial.hasInitial

noncomputable def initialIsoEmpty : ⊥_ Quiv ≅ Empty :=
  initialIsoIsInitial emptyIsInitial


def pointIsTerminal : IsTerminal Point := ⟨
    fun ⟨pt, _⟩ ↦ Prefunctor.mk (fun _ ↦ PUnit.unit) (fun _ => PUnit.unit),
    by simp,
    fun ⟨pt, _⟩ ⟨obj, map⟩ h ↦ by congr
  ⟩

instance : HasTerminal Quiv := pointIsTerminal.hasTerminal

noncomputable def terminalIsoPoint : ⊤_ Quiv ≅ Point :=
  terminalIsoIsTerminal pointIsTerminal
