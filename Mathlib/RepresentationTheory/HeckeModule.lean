/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# Induction

This files defines Hecke algebras and Hecke modules.

-/

@[expose] public section

universe u v
variable {k : Type u} [CommRing k]
variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]
variable {W : Type u} [AddCommGroup W] [Module k W]
variable (H : Subgroup G) (σ : Representation k H V) (ρ : Representation k G W)

noncomputable section
namespace Representation

abbrev algebraHecke : Type u := (ind H.subtype σ).IntertwiningMap (ind H.subtype σ)

instance : Ring (algebraHecke H σ) where

abbrev moduleHecke : Type u := (ind H.subtype σ).IntertwiningMap ρ

abbrev algebraHeckeOp := (MulOpposite (algebraHecke H σ))

variable (k)

abbrev algebraHecke₁ := algebraHecke H (trivial k H k)

abbrev algebraHecke₁Op := MulOpposite (algebraHecke₁ k H)

variable {k}

abbrev moduleHecke₁ := (ind H.subtype (trivial k H k)).IntertwiningMap ρ

abbrev bimoduleHecke₁ (H1 H2 : Subgroup G) : Type u :=
  moduleHecke₁ H1 (ind H2.subtype (trivial k H2 k))

namespace Rep

open CategoryTheory

abbrev toHeckeModule (A : Rep k G) : ModuleCat (algebraHeckeOp H σ) :=
  ModuleCat.of (algebraHeckeOp H σ) (moduleHecke H σ A.ρ)

abbrev toHecke₁Module (A : Rep k G) : ModuleCat (algebraHecke₁Op k H) :=
  ModuleCat.of (algebraHecke₁Op k H) (moduleHecke₁ H A.ρ)

abbrev toHeckeModuleMap {A B : Rep k G} (f : A ⟶ B) : toHeckeModule H σ A ⟶ toHeckeModule H σ B :=
  ModuleCat.ofHom {
    toFun g := f.hom.comp g
    map_add' x y := by rw [IntertwiningMap.add_comp]
    map_smul' _ _ := rfl}

abbrev toHecke₁ModuleMap {A B : Rep k G} (f : A ⟶ B) : toHecke₁Module H A ⟶ toHecke₁Module H B :=
  ModuleCat.ofHom {
    toFun g := f.hom.comp g
    map_add' x y := by rw [IntertwiningMap.add_comp]
    map_smul' _ _ := rfl}

abbrev toHeckeModuleFunctor : Rep k G ⥤ ModuleCat (algebraHeckeOp H σ) where
  obj := toHeckeModule H σ
  map := toHeckeModuleMap H σ

abbrev toHecke₁ModuleFunctor : Rep k G ⥤ ModuleCat (algebraHecke₁Op k H) where
  obj := toHecke₁Module H
  map := toHecke₁ModuleMap H

end Rep

end Representation

end
