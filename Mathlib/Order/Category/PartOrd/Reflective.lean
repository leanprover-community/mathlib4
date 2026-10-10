/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Partial orders as a reflective subcategory of preorders

Antisymmetrization exhibits `PartOrd` as a reflective subcategory of `Preord`.
-/

public section

universe u

open CategoryTheory

instance : (forget₂ PartOrd.{u} Preord.{u}).Full where
  map_surjective f := ⟨PartOrd.ofHom f.hom, rfl⟩

instance : Reflective (forget₂ PartOrd.{u} Preord.{u}) where
  L := preordToPartOrd
  adj := preordToPartOrdForgetAdjunction
