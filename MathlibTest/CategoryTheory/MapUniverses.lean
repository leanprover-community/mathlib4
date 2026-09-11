module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.CategoryTheory.Discrete.Basic

open CategoryTheory

namespace Tests.MapUniverses

universe w u v uE vE uD vD

-- Source parameters need not start with the category's universes.
@[map]
lemma extra.{wS, uS, vS} {A : Type wS} (_a : A) {C : Type uS} [Category.{vS} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) : f = g := h

example {A : Type w} (a : A) {C : Type u} [Category.{v} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) : F.map f = F.map g :=
  extra_map.{v, vD, u, uD, w} a f g h F

-- Objects and morphisms can share a universe.
@[map]
lemma shared.{uS} {C : Type uS} [Category.{uS} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) : f = g := h

example {C : Type u} [Category.{u} C] {x y : C} (f g : x ⟶ y) (h : f = g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g :=
  shared_map.{u, vD, uD} f g h F

-- Fresh parameter names must not collide with existing ones.
@[map]
lemma collision.{u_1, u_2} {C : Type u_1} [Category.{u_2} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) : f = g := h

example {C : Type u} [Category.{v} C] {x y : C} (f g : x ⟶ y) (h : f = g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g :=
  collision_map.{v, vD, u, uD} f g h F

-- The source can also have no universe parameters at all.
@[map]
lemma closed {x y : Discrete Unit} (f g : x ⟶ y) (h : f = g) : f = g := h

example {x y : Discrete Unit} (f g : x ⟶ y) (h : f = g)
    {D : Type uD} [Category.{vD} D] (F : Discrete Unit ⥤ D) : F.map f = F.map g :=
  closed_map.{vD, uD} f g h F

-- Classify every category in the source declaration, including abbreviated instance types.
abbrev Cat.{vCat, uCat} (C : Type uCat) := Category.{vCat} C

@[map]
lemma through_functor.{uS₁, vS₁, uS₂, vS₂} {C : Type uS₁} [Cat.{vS₁, uS₁} C]
    {E : Type uS₂} [Cat.{vS₂, uS₂} E] (G : C ⥤ E)
    {x y : C} (f g : x ⟶ y) (h : f = g) : G.map f = G.map g := G.congr_map h

example {C : Type u} [Category.{v} C] {E : Type uE} [Category.{vE} E] (G : C ⥤ E)
    {x y : C} (f g : x ⟶ y) (h : f = g) {D : Type uD} [Category.{vD} D]
    (F : E ⥤ D) : F.map (G.map f) = F.map (G.map g) :=
  through_functor_map.{v, vE, vD, u, uE, uD} G f g h F

-- Classify parameters inside composite levels, putting a shared parameter in the morphism group.
set_option linter.checkUnivs false in
@[map]
lemma composite.{uS, vS, wS} {C : Type (max uS wS)} [Category.{max vS wS} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) : f = g := h

example {C : Type (max u w)} [Category.{max v w} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) : F.map f = F.map g :=
  composite_map.{v, w, vD, u, uD} f g h F

-- Reordering must preserve source parameter names and add exactly two distinct parameters.
open Lean Elab Command in
run_cmd liftTermElabM do
  for src in [``extra, ``shared, ``collision, ``closed, ``through_functor, ``composite] do
    let srcLevels := (← getConstInfo src).levelParams
    let tgtLevels := (← getConstInfo (src.appendAfter "_map")).levelParams
    guard <| srcLevels.all tgtLevels.contains
    guard <| tgtLevels.eraseDups == tgtLevels
    guard <| tgtLevels.length == srcLevels.length + 2

end Tests.MapUniverses
