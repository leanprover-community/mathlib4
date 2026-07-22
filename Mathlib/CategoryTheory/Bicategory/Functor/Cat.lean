/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctors to Cat

In this file, we state naturality properties of `mapId'` and `mapComp'`
for pseudofunctors to `Cat`.

-/

public section

universe w v v' u u'

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : B ⥤ᵖ Cat.{v', u'})

section naturality

variable {b₀ b₁ b₂ : B} {X Y : F.obj b₀}

section

variable (f : b₀ ⟶ b₀) (hf : f = 𝟙 b₀) (a : X ⟶ Y)

@[reassoc]
lemma mapId'_hom_naturality :
    (F.map f).toFunctor.map a ≫ (F.mapId' f hf).hom.toNatTrans.app Y =
    (F.mapId' f hf).hom.toNatTrans.app X ≫ a :=
  (F.mapId' f hf).hom.toNatTrans.naturality a

@[reassoc]
lemma mapId'_inv_naturality :
    (F.mapId' f hf).inv.toNatTrans.app X ≫ (F.map f).toFunctor.map a =
    a ≫ (F.mapId' f hf).inv.toNatTrans.app Y :=
  ((F.mapId' f hf).inv.toNatTrans.naturality a).symm

end

section

variable (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  (hfg : f ≫ g = fg) (a : X ⟶ Y)

@[reassoc]
lemma mapComp'_hom_naturality :
    (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y =
    (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.map g).toFunctor.map
      ((F.map f).toFunctor.map a) :=
  (F.mapComp' f g fg hfg).hom.toNatTrans.naturality a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed in Sites/Descent/IsPrestack.lean
@[reassoc (attr := simp)]
lemma mapComp'_inv_naturality :
    (F.map g).toFunctor.map ((F.map f).toFunctor.map a) ≫
    (F.mapComp' f g fg hfg).inv.toNatTrans.app Y =
    (F.mapComp' f g fg hfg).inv.toNatTrans.app X ≫ (F.map fg).toFunctor.map a :=
  (F.mapComp' f g fg hfg).inv.toNatTrans.naturality a

@[reassoc]
lemma mapComp'_naturality_1 :
    (F.mapComp' f g fg hfg).inv.toNatTrans.app X ≫
      (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y =
    (F.map g).toFunctor.map ((F.map f).toFunctor.map a) :=
  NatIso.naturality_1 (Cat.Hom.toNatIso (F.mapComp' f g fg hfg)) a

@[reassoc]
lemma mapComp'_naturality_2 :
    (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫
      (F.map g).toFunctor.map ((F.map f).toFunctor.map a) ≫
        (F.mapComp' f g fg hfg).inv.toNatTrans.app Y =
    (F.map fg).toFunctor.map a :=
  NatIso.naturality_2 (Cat.Hom.toNatIso (F.mapComp' f g fg hfg)) a

end

end naturality

end Pseudofunctor

end CategoryTheory
