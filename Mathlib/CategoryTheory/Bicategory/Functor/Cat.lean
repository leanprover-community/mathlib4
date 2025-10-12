/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctors to Cat

In this file, we state naturality properties of `mapId'` and `mapComp'`
for pseudofunctors to `Cat`.

-/

universe w v v' u u'

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : Pseudofunctor B Cat.{v', u'})

section naturality

variable {b₀ b₁ b₂ : B} {X Y : F.obj b₀}

section

variable (f : b₀ ⟶ b₀) (hf : f = 𝟙 b₀) (a : X ⟶ Y)

@[reassoc]
lemma mapId'_hom_naturality :
    (F.map f).map a ≫ (F.mapId' f hf).hom.app Y = (F.mapId' f hf).hom.app X ≫ a :=
  (F.mapId' f hf).hom.naturality a

@[reassoc]
lemma mapId'_inv_naturality :
    (F.mapId' f hf).inv.app X ≫ (F.map f).map a = a ≫ (F.mapId' f hf).inv.app Y :=
  ((F.mapId' f hf).inv.naturality a).symm

end

section

variable (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  (hfg : f ≫ g = fg) (a : X ⟶ Y)

@[reassoc]
lemma mapComp'_hom_naturality :
    (F.map fg).map a ≫ (F.mapComp' f g fg hfg).hom.app Y =
    (F.mapComp' f g fg hfg).hom.app X ≫ (F.map g).map ((F.map f).map a) :=
  (F.mapComp' f g fg hfg).hom.naturality a

@[reassoc]
lemma mapComp'_inv_naturality :
    (F.map g).map ((F.map f).map a) ≫ (F.mapComp' f g fg hfg).inv.app Y =
    (F.mapComp' f g fg hfg).inv.app X ≫ (F.map fg).map a :=
  (F.mapComp' f g fg hfg).inv.naturality a

@[reassoc]
lemma mapComp'_naturality_1 :
    (F.mapComp' f g fg hfg).inv.app X ≫
      (F.map fg).map a ≫ (F.mapComp' f g fg hfg).hom.app Y =
    (F.map g).map ((F.map f).map a) :=
  NatIso.naturality_1 (F.mapComp' f g fg hfg) a

@[reassoc]
lemma mapComp'_naturality_2 :
    (F.mapComp' f g fg hfg).hom.app X ≫ (F.map g).map ((F.map f).map a) ≫
      (F.mapComp' f g fg hfg).inv.app Y =
    (F.map fg).map a :=
  NatIso.naturality_2 (F.mapComp' f g fg hfg) a

end

end naturality

end Pseudofunctor

end CategoryTheory
