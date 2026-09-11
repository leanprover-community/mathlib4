module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.CategoryTheory.Discrete.Basic

open CategoryTheory

namespace Tests.MapUniverses

universe w u v uD vD

-- Source parameters need not start with the category's universes.
@[map]
lemma extra.{wS, uS, vS} {A : Type wS} (_a : A) {C : Type uS} [Category.{vS} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) : f = g := h

example {A : Type w} (a : A) {C : Type u} [Category.{v} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) : F.map f = F.map g :=
  extra_map.{w, u, v, uD, vD} a f g h F

-- Objects and morphisms can share a universe.
@[map]
lemma shared.{uS} {C : Type uS} [Category.{uS} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) : f = g := h

example {C : Type u} [Category.{u} C] {x y : C} (f g : x ⟶ y) (h : f = g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g :=
  shared_map.{u, uD, vD} f g h F

-- Fresh parameter names must not collide with existing ones.
@[map]
lemma collision.{u_1, u_2} {C : Type u_1} [Category.{u_2} C]
    {x y : C} (f g : x ⟶ y) (h : f = g) : f = g := h

example {C : Type u} [Category.{v} C] {x y : C} (f g : x ⟶ y) (h : f = g)
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) : F.map f = F.map g :=
  collision_map.{u, v, uD, vD} f g h F

-- The source can also have no universe parameters at all.
@[map]
lemma closed {x y : Discrete Unit} (f g : x ⟶ y) (h : f = g) : f = g := h

example {x y : Discrete Unit} (f g : x ⟶ y) (h : f = g)
    {D : Type uD} [Category.{vD} D] (F : Discrete Unit ⥤ D) : F.map f = F.map g :=
  closed_map.{uD, vD} f g h F

-- Preserve both the order and names of every source universe parameter.
open Lean Elab Command in
run_cmd liftTermElabM do
  for src in [``extra, ``shared, ``collision, ``closed] do
    let srcLevels := (← getConstInfo src).levelParams
    let tgtLevels := (← getConstInfo (src.appendAfter "_map")).levelParams
    guard <| tgtLevels.take srcLevels.length == srcLevels
    guard <| tgtLevels.length == srcLevels.length + 2

end Tests.MapUniverses
