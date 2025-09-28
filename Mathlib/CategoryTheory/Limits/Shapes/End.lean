/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Ends and coends

In this file, given a functor `F : Jᵒᵖ ⥤ J ⥤ C`, we define its end `end_ F`,
which is a suitable multiequalizer of the objects `(F.obj (op j)).obj j` for all `j : J`.
For this shape of limits, cones are named wedges: the corresponding type is `Wedge F`.

We also introduce `coend F` as multicoequalizers of
`(F.obj (op j)).obj j` for all `j : J`. In this cases, cocones are named cowedges.

## References
* https://ncatlab.org/nlab/show/end

-/

universe v v' u u'

namespace CategoryTheory

open Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (F : Jᵒᵖ ⥤ J ⥤ C)

variable (J) in
/-- The shape of multiequalizer diagrams involved in the definition of ends. -/
@[simps]
def multicospanShapeEnd : MulticospanShape where
  L := J
  R := Arrow J
  fst f := f.left
  snd f := f.right

variable (J) in
/-- The shape of multicoequalizer diagrams involved in the definition of coends. -/
@[simps]
def multispanShapeCoend : MultispanShape where
  L := Arrow J
  R := J
  fst f := f.left
  snd f := f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multicospan index which shall be used
to define the end of `F`. -/
@[simps]
def multicospanIndexEnd : MulticospanIndex (multicospanShapeEnd J) C where
  left j := (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multispan used to define the coend
of `F`. -/
@[simps]
def multispanIndexCoend : MultispanIndex (multispanShapeCoend J) C where
  left f := (F.obj (op f.right)).obj f.left
  right j := (F.obj (op j)).obj j
  fst f := (F.map f.hom.op).app f.left
  snd f := (F.obj (op f.right)).map f.hom

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, a wedge for `F` is a type of cones (specifically
the type of multiforks for `multicospanIndexEnd F`):
the point of universal of these wedges shall be the end of `F`. -/
abbrev Wedge := Multifork (multicospanIndexEnd F)

namespace Wedge

variable {F}

/-- A variant of `CategoryTheory.Limits.Cones.ext` specialized to produce
isomorphisms of wedges. -/
@[simps!]
def ext {W₁ W₂ : Wedge F} (e : W₁.pt ≅ W₂.pt)
    (he : ∀ j : J, W₁.ι j = e.hom ≫ W₂.ι j := by cat_disch) : W₁ ≅ W₂ :=
  Cones.ext e (fun j =>
    match j with
    | .left _ => he _
    | .right f => by simpa using (he f.left) =≫ _)

section Constructor

variable (pt : C) (π : ∀ (j : J), pt ⟶ (F.obj (op j)).obj j)
  (hπ : ∀ ⦃i j : J⦄ (f : i ⟶ j), π i ≫ (F.obj (op i)).map f = π j ≫ (F.map f.op).app j)

/-- Constructor for wedges. -/
@[simps! pt]
abbrev mk : Wedge F :=
  Multifork.ofι _ pt π (fun f ↦ hπ f.hom)

@[simp]
lemma mk_ι (j : J) : (mk pt π hπ).ι j = π j := rfl

end Constructor

@[reassoc]
lemma condition (c : Wedge F) {i j : J} (f : i ⟶ j) :
    c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j :=
  Multifork.condition c (Arrow.mk f)

namespace IsLimit

variable {c : Wedge F} (hc : IsLimit c)

lemma hom_ext (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : ∀ j, f ≫ c.ι j = g ≫ c.ι j) :
    f = g :=
  Multifork.IsLimit.hom_ext hc h

/-- Construct a morphism to the end from its universal property. -/
def lift (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) :
    X ⟶ c.pt :=
  Multifork.IsLimit.lift hc f (fun _ ↦ hf _)

@[reassoc (attr := simp)]
lemma lift_ι (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) (j : J) :
    lift hc f hf ≫ c.ι j = f j := by
  apply IsLimit.fac


end IsLimit

end Wedge

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, a cowedge for `F` is a type of cocones
(specifically the type of multicoforks for `multispanIndexCoend F`):
the point of a universal cowedge is the coend of `F`. -/
abbrev Cowedge := Multicofork (multispanIndexCoend F)

namespace Cowedge

variable {F}

/-- A variant of `CategoryTheory.Limits.Cocones.ext` specialized to produce
isomorphisms of cowedges. -/
@[simps!]
def ext {W₁ W₂ : Cowedge F} (e : W₁.pt ≅ W₂.pt)
    (he : ∀ j : J, W₁.π j ≫ e.hom  = W₂.π j := by cat_disch) : W₁ ≅ W₂ :=
  Cocones.ext e (fun j =>
    match j with
    | .right _ => he _
    | .left f => by simpa using _ ≫= (he f.left))

section Constructor

variable (pt : C) (ι : ∀ (j : J), (F.obj (op j)).obj j ⟶ pt)
  (hι : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f.op).app i ≫ ι i = (F.obj (op j)).map f ≫ ι j)

/-- Constructor for cowedges. -/
@[simps! pt]
abbrev mk : Cowedge F :=
  Multicofork.ofπ _ pt ι (fun f ↦ hι f.hom)

@[simp]
lemma mk_π (j : J) : (mk pt ι hι).π j = ι j := rfl

end Constructor

@[reassoc]
lemma condition (c : Cowedge F) {i j : J} (f : i ⟶ j) :
    (F.map f.op).app i ≫ c.π i = (F.obj (op j)).map f ≫ c.π j :=
  Multicofork.condition c (Arrow.mk f)

namespace IsColimit

variable {c : Cowedge F} (hc : IsColimit c)

lemma hom_ext (hc : IsColimit c) {X : C} {f g : c.pt ⟶ X} (h : ∀ j, c.π j ≫ f = c.π j ≫ g) :
    f = g :=
  Multicofork.IsColimit.hom_ext hc h

/-- Construct a morphism from the coend using its universal property. -/
def desc (hc : IsColimit c) {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j) :
    c.pt ⟶ X :=
  Multicofork.IsColimit.desc hc f (fun _ ↦ hf _)

@[reassoc (attr := simp)]
lemma π_desc (hc : IsColimit c) {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j) (j : J) :
    c.π j ≫ desc hc f hf = f j := by
  apply IsColimit.fac

end IsColimit

end Cowedge

section End

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this property asserts the existence of the end of `F`. -/
abbrev HasEnd := HasMultiequalizer (multicospanIndexEnd F)

variable [HasEnd F]

/-- The end of a functor `F : Jᵒᵖ ⥤ J ⥤ C`. -/
noncomputable def end_ : C := multiequalizer (multicospanIndexEnd F)

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the projection `end_ F ⟶ (F.obj (op j)).obj j`
for any `j : J`. -/
noncomputable def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := Multiequalizer.ι _ _

@[reassoc]
lemma end_.condition {i j : J} (f : i ⟶ j) :
    π F i ≫ (F.obj (op i)).map f = π F j ≫ (F.map f.op).app j := by
  apply Wedge.condition

variable {F}

@[ext]
lemma end_.hom_ext {X : C} {f g : X ⟶ end_ F} (h : ∀ j, f ≫ end_.π F j = g ≫ end_.π F j) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (fun _ ↦ h _)

@[deprecated (since := "2025-06-06")] alias _root_.CategoryTheory.Limits.hom_ext :=
  end_.hom_ext

section

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/-- Constructor for morphisms to the end of a functor. -/
noncomputable def end_.lift : X ⟶ end_ F :=
  Wedge.IsLimit.lift (limit.isLimit _) f hf

@[reassoc (attr := simp)]
lemma end_.lift_π (j : J) : lift f hf ≫ π F j = f j := by
  apply IsLimit.fac

variable {F' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F'] (f : F ⟶ F')

/-- A natural transformation of functors F ⟶ F' induces a map end_ F ⟶ end_ F'. -/
noncomputable def end_.map : end_ F ⟶ end_ F' :=
  end_.lift (fun x ↦ end_.π _ _ ≫ (f.app (op x)).app x) (fun j j' φ ↦ by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e, reassoc_of% end_.condition F φ]
    simp)

@[reassoc (attr := simp)]
lemma end_.map_π (j : J) :
    end_.map f ≫ end_.π F' j = end_.π _ _ ≫ (f.app (op j)).app j := by
  simp [end_.map]

@[reassoc (attr := simp)]
lemma end_.map_comp {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F''] (g : F' ⟶ F'') :
    end_.map f ≫ end_.map g = end_.map (f ≫ g) := by
  cat_disch

@[simp]
lemma end_.map_id : end_.map (𝟙 F) = 𝟙 _ := by cat_disch

end

variable (J C) in
/-- If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have an end, then the construction
`F ↦ end_ F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`. -/
@[simps]
noncomputable def endFunctor [∀ (F : Jᵒᵖ ⥤ J ⥤ C), HasEnd F] :
    (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := end_ F
  map f := end_.map f

end End

section Coend

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this property asserts the existence of the coend of `F`. -/
abbrev HasCoend := HasMulticoequalizer (multispanIndexCoend F)

variable [HasCoend F]

/-- The end of a functor `F : Jᵒᵖ ⥤ J ⥤ C`. -/
noncomputable def coend : C := multicoequalizer (multispanIndexCoend F)

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the inclusion `(F.obj (op j)).obj j ⟶ coend F`
for any `j : J`. -/
noncomputable def coend.ι (j : J) : (F.obj (op j)).obj j ⟶ coend F :=
  Multicoequalizer.π (multispanIndexCoend F) _

@[reassoc]
lemma coend.condition {i j : J} (f : i ⟶ j) :
     (F.map f.op).app i ≫ ι F i  = (F.obj (op j)).map f ≫ ι F j := by
  apply Cowedge.condition

variable {F}

@[ext]
lemma coend.hom_ext {X : C} {f g : coend F ⟶ X} (h : ∀ j, coend.ι F j ≫ f = coend.ι F j ≫ g) :
    f = g :=
  Multicoequalizer.hom_ext _ _ _ (fun _ ↦ h _)

section

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

/-- Constructor for morphisms to the coend of a functor. -/
noncomputable def coend.desc : coend F ⟶ X :=
  Cowedge.IsColimit.desc (colimit.isColimit _) f hf

@[reassoc (attr := simp)]
lemma coend.ι_desc (j : J) : ι F j ≫ desc f hf = f j := by
  apply IsColimit.fac

variable {F' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F'] (f : F ⟶ F')

/-- A natural transformation of functors F ⟶ F' induces a map coend F ⟶ coend F'. -/
noncomputable def coend.map : coend F ⟶ coend F' :=
  coend.desc (fun x ↦ (f.app (op x)).app x ≫ coend.ι _ _ ) (fun j j' φ ↦ by
    simp [coend.condition])

@[reassoc (attr := simp)]
lemma coend.ι_map (j : J) :
    coend.ι _ _ ≫ coend.map f = (f.app (op j)).app j ≫ coend.ι _ _ := by
  simp [coend.map]

@[reassoc (attr := simp)]
lemma coend.map_comp {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F''] (g : F' ⟶ F'') :
    coend.map f ≫ coend.map g = coend.map (f ≫ g) := by
  cat_disch

@[simp]
lemma coend.map_id : coend.map (𝟙 F) = 𝟙 _ := by cat_disch

end

variable (J C) in
/-- If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have a coend, then the construction
`F ↦ coend F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`. -/
@[simps]
noncomputable def coendFunctor [∀ (F : Jᵒᵖ ⥤ J ⥤ C), HasCoend F] :
    (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := coend F
  map f := coend.map f

end Coend

end Limits

end CategoryTheory
