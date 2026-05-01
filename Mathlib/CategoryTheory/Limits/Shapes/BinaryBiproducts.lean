/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Binary biproducts

We introduce the notion of binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `BinaryBicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `BinaryBicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

-/

@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

/-- A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q` -/
structure BinaryBicone (P Q : C) where
  pt : C
  fst : pt ⟶ P
  snd : pt ⟶ Q
  inl : P ⟶ pt
  inr : Q ⟶ pt
  inl_fst : inl ≫ fst = 𝟙 P := by aesop
  inl_snd : inl ≫ snd = 0 := by aesop
  inr_fst : inr ≫ fst = 0 := by aesop
  inr_snd : inr ≫ snd = 𝟙 Q := by aesop

attribute [inherit_doc BinaryBicone] BinaryBicone.pt BinaryBicone.fst BinaryBicone.snd
  BinaryBicone.inl BinaryBicone.inr BinaryBicone.inl_fst BinaryBicone.inl_snd
  BinaryBicone.inr_fst BinaryBicone.inr_snd

attribute [reassoc (attr := simp)]
  BinaryBicone.inl_fst BinaryBicone.inl_snd BinaryBicone.inr_fst BinaryBicone.inr_snd

/-- A binary bicone morphism between two binary bicones for the same diagram is a morphism of the
binary bicone points which commutes with the cone and cocone legs. -/
structure BinaryBiconeMorphism {P Q : C} (A B : BinaryBicone P Q) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wfst : hom ≫ B.fst = A.fst := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wsnd : hom ≫ B.snd = A.snd := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winl : A.inl ≫ hom = B.inl := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winr : A.inr ≫ hom = B.inr := by cat_disch

attribute [reassoc (attr := simp)] BinaryBiconeMorphism.wfst BinaryBiconeMorphism.wsnd
attribute [reassoc (attr := simp)] BinaryBiconeMorphism.winl BinaryBiconeMorphism.winr

/-- The category of binary bicones on a given diagram. -/
@[simps]
instance BinaryBicone.category {P Q : C} : Category (BinaryBicone P Q) where
  Hom A B := BinaryBiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/- We do not want `simps` automatically generate the lemma for simplifying the `Hom` field of
-- a category. So we need to write the `ext` lemma in terms of the categorical morphism, rather than
the underlying structure. -/
@[ext]
theorem BinaryBiconeMorphism.ext {P Q : C} {c c' : BinaryBicone P Q}
    (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace BinaryBicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt)
    (winl : c.inl ≫ φ.hom = c'.inl := by cat_disch)
    (winr : c.inr ≫ φ.hom = c'.inr := by cat_disch)
    (wfst : φ.hom ≫ c'.fst = c.fst := by cat_disch)
    (wsnd : φ.hom ≫ c'.snd = c.snd := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wfst := φ.inv_comp_eq.mpr wfst.symm
      wsnd := φ.inv_comp_eq.mpr wsnd.symm
      winl := φ.comp_inv_eq.mpr winl.symm
      winr := φ.comp_inv_eq.mpr winr.symm }

variable (P Q : C) (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]

/-- A functor `F : C ⥤ D` sends binary bicones for `P` and `Q`
to binary bicones for `G.obj P` and `G.obj Q` functorially. -/
@[simps]
def functoriality : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where
  obj A :=
    { pt := F.obj A.pt
      fst := F.map A.fst
      snd := F.map A.snd
      inl := F.map A.inl
      inr := F.map A.inr
      inl_fst := by rw [← F.map_comp, A.inl_fst, F.map_id]
      inl_snd := by rw [← F.map_comp, A.inl_snd, F.map_zero]
      inr_fst := by rw [← F.map_comp, A.inr_fst, F.map_zero]
      inr_snd := by rw [← F.map_comp, A.inr_snd, F.map_id] }
  map f :=
    { hom := F.map f.hom
      wfst := by simp [-BinaryBiconeMorphism.wfst, ← f.wfst]
      wsnd := by simp [-BinaryBiconeMorphism.wsnd, ← f.wsnd]
      winl := by simp [-BinaryBiconeMorphism.winl, ← f.winl]
      winr := by simp [-BinaryBiconeMorphism.winr, ← f.winr] }

instance functoriality_full [F.Full] [F.Faithful] : (functoriality P Q F).Full where
  map_surjective t :=
   ⟨{ hom := F.preimage t.hom
      winl := F.map_injective (by simpa using t.winl)
      winr := F.map_injective (by simpa using t.winr)
      wfst := F.map_injective (by simpa using t.wfst)
      wsnd := F.map_injective (by simpa using t.wsnd) }, by cat_disch⟩

instance functoriality_faithful [F.Faithful] : (functoriality P Q F).Faithful where
  map_injective {_X} {_Y} f g h :=
    BinaryBiconeMorphism.ext f g <| F.map_injective <| congr_arg BinaryBiconeMorphism.hom h

end BinaryBicones

namespace BinaryBicone

variable {P Q : C}

/-- Extract the cone from a binary bicone. -/
def toCone (c : BinaryBicone P Q) : Cone (pair P Q) :=
  BinaryFan.mk c.fst c.snd

@[simp]
theorem toCone_pt (c : BinaryBicone P Q) : c.toCone.pt = c.pt := rfl

@[simp]
theorem toCone_π_app_left (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst :=
  rfl

@[simp]
theorem toCone_π_app_right (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd :=
  rfl

@[simp]
theorem binary_fan_fst_toCone (c : BinaryBicone P Q) : BinaryFan.fst c.toCone = c.fst := rfl

@[simp]
theorem binary_fan_snd_toCone (c : BinaryBicone P Q) : BinaryFan.snd c.toCone = c.snd := rfl

/-- Extract the cocone from a binary bicone. -/
def toCocone (c : BinaryBicone P Q) : Cocone (pair P Q) := BinaryCofan.mk c.inl c.inr

@[simp]
theorem toCocone_pt (c : BinaryBicone P Q) : c.toCocone.pt = c.pt := rfl

@[simp]
theorem toCocone_ι_app_left (c : BinaryBicone P Q) : c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl :=
  rfl

@[simp]
theorem toCocone_ι_app_right (c : BinaryBicone P Q) :
    c.toCocone.ι.app ⟨WalkingPair.right⟩ = c.inr := rfl

@[simp]
theorem binary_cofan_inl_toCocone (c : BinaryBicone P Q) : BinaryCofan.inl c.toCocone = c.inl :=
  rfl

@[simp]
theorem binary_cofan_inr_toCocone (c : BinaryBicone P Q) : BinaryCofan.inr c.toCocone = c.inr :=
  rfl

/-- The retract of a binary bicone `c` given by `c.inl` and `c.fst`. -/
def retract_left (c : BinaryBicone P Q) : Retract P c.pt where
  i := c.inl
  r := c.fst

/-- The retract of a binary bicone `c` given by `c.inr` and `c.snd`. -/
def retract_right (c : BinaryBicone P Q) : Retract Q c.pt where
  i := c.inr
  r := c.snd

instance (c : BinaryBicone P Q) : IsSplitMono c.inl := c.retract_left.instIsSplitMonoI

instance (c : BinaryBicone P Q) : IsSplitMono c.inr := c.retract_right.instIsSplitMonoI

instance (c : BinaryBicone P Q) : IsSplitEpi c.fst := c.retract_left.instIsSplitEpiR

instance (c : BinaryBicone P Q) : IsSplitEpi c.snd := c.retract_right.instIsSplitEpiR

set_option backward.isDefEq.respectTransparency false in
/-- Convert a `BinaryBicone` into a `Bicone` over a pair. -/
@[simps]
def toBiconeFunctor {X Y : C} : BinaryBicone X Y ⥤ Bicone (pairFunction X Y) where
  obj b :=
    { pt := b.pt
      π := fun j => WalkingPair.casesOn j b.fst b.snd
      ι := fun j => WalkingPair.casesOn j b.inl b.inr
      ι_π := fun j j' => by
        rcases j with ⟨⟩ <;> rcases j' with ⟨⟩ <;> simp }
  map f := {
    hom := f.hom
    wπ := fun i => WalkingPair.casesOn i f.wfst f.wsnd
    wι := fun i => WalkingPair.casesOn i f.winl f.winr }

/-- A shorthand for `toBiconeFunctor.obj` -/
abbrev toBicone {X Y : C} (b : BinaryBicone X Y) : Bicone (pairFunction X Y) :=
  toBiconeFunctor.obj b

/-- A binary bicone is a limit cone if and only if the corresponding bicone is a limit cone. -/
def toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) :
    IsLimit b.toBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <| Cone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

/-- A binary bicone is a colimit cocone if and only if the corresponding bicone is a colimit
cocone. -/
def toBiconeIsColimit {X Y : C} (b : BinaryBicone X Y) :
    IsColimit b.toBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <| Cocone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

end BinaryBicone

namespace Bicone

set_option backward.isDefEq.respectTransparency false in
/-- Convert a `Bicone` over a function on `WalkingPair` to a BinaryBicone. -/
@[simps]
def toBinaryBiconeFunctor {X Y : C} : Bicone (pairFunction X Y) ⥤ BinaryBicone X Y where
  obj b :=
    { pt := b.pt
      fst := b.π WalkingPair.left
      snd := b.π WalkingPair.right
      inl := b.ι WalkingPair.left
      inr := b.ι WalkingPair.right
      inl_fst := by simp
      inr_fst := by simp
      inl_snd := by simp
      inr_snd := by simp }
  map f :=
    { hom := f.hom }

/-- A shorthand for `toBinaryBiconeFunctor.obj` -/
abbrev toBinaryBicone {X Y : C} (b : Bicone (pairFunction X Y)) : BinaryBicone X Y :=
  toBinaryBiconeFunctor.obj b

/-- A bicone over a pair is a limit cone if and only if the corresponding binary bicone is a limit
cone. -/
def toBinaryBiconeIsLimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsLimit b.toBinaryBicone.toCone ≃ IsLimit b.toCone :=
  IsLimit.equivIsoLimit <| Cone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

/-- A bicone over a pair is a colimit cocone if and only if the corresponding binary bicone is a
colimit cocone. -/
def toBinaryBiconeIsColimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsColimit b.toBinaryBicone.toCocone ≃ IsColimit b.toCocone :=
  IsColimit.equivIsoColimit <| Cocone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

end Bicone

/-- Structure witnessing that a binary bicone is a limit cone and a limit cocone. -/
structure BinaryBicone.IsBilimit {P Q : C} (b : BinaryBicone P Q) where
  isLimit : IsLimit b.toCone
  isColimit : IsColimit b.toCocone

attribute [inherit_doc BinaryBicone.IsBilimit] BinaryBicone.IsBilimit.isLimit
  BinaryBicone.IsBilimit.isColimit

/-- A binary bicone is a bilimit bicone if and only if the corresponding bicone is a bilimit. -/
def BinaryBicone.toBiconeIsBilimit {X Y : C} (b : BinaryBicone X Y) :
    b.toBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBiconeIsLimit h.isLimit, b.toBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBiconeIsLimit.symm h.isLimit, b.toBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/-- A bicone over a pair is a bilimit bicone if and only if the corresponding binary bicone is a
bilimit. -/
def Bicone.toBinaryBiconeIsBilimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    b.toBinaryBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBinaryBiconeIsLimit h.isLimit, b.toBinaryBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBinaryBiconeIsLimit.symm h.isLimit, b.toBinaryBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/-- A bicone over `P Q : C`, which is both a limit cone and a colimit cocone. -/
structure BinaryBiproductData (P Q : C) where
  bicone : BinaryBicone P Q
  isBilimit : bicone.IsBilimit

attribute [inherit_doc BinaryBiproductData] BinaryBiproductData.bicone
  BinaryBiproductData.isBilimit

/-- `HasBinaryBiproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`. -/
class HasBinaryBiproduct (P Q : C) : Prop where mk' ::
  exists_binary_biproduct : Nonempty (BinaryBiproductData P Q)

attribute [inherit_doc HasBinaryBiproduct] HasBinaryBiproduct.exists_binary_biproduct

theorem HasBinaryBiproduct.mk {P Q : C} (d : BinaryBiproductData P Q) : HasBinaryBiproduct P Q :=
  ⟨Nonempty.intro d⟩

/--
Use the axiom of choice to extract explicit `BinaryBiproductData F` from `HasBinaryBiproduct F`.
-/
def getBinaryBiproductData (P Q : C) [HasBinaryBiproduct P Q] : BinaryBiproductData P Q :=
  Classical.choice HasBinaryBiproduct.exists_binary_biproduct

/-- A bicone for `P Q` which is both a limit cone and a colimit cocone. -/
def BinaryBiproduct.bicone (P Q : C) [HasBinaryBiproduct P Q] : BinaryBicone P Q :=
  (getBinaryBiproductData P Q).bicone

/-- `BinaryBiproduct.bicone P Q` is a limit bicone. -/
def BinaryBiproduct.isBilimit (P Q : C) [HasBinaryBiproduct P Q] :
    (BinaryBiproduct.bicone P Q).IsBilimit :=
  (getBinaryBiproductData P Q).isBilimit

/-- `BinaryBiproduct.bicone P Q` is a limit cone. -/
def BinaryBiproduct.isLimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsLimit (BinaryBiproduct.bicone P Q).toCone :=
  (getBinaryBiproductData P Q).isBilimit.isLimit

/-- `BinaryBiproduct.bicone P Q` is a colimit cocone. -/
def BinaryBiproduct.isColimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsColimit (BinaryBiproduct.bicone P Q).toCocone :=
  (getBinaryBiproductData P Q).isBilimit.isColimit

section

variable (C)

/-- `HasBinaryBiproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`. -/
class HasBinaryBiproducts : Prop where
  has_binary_biproduct : ∀ P Q : C, HasBinaryBiproduct P Q

attribute [instance 100] HasBinaryBiproducts.has_binary_biproduct

/-- A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties. -/
theorem hasBinaryBiproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBinaryBiproducts C :=
  { has_binary_biproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { bicone := (biproduct.bicone (pairFunction P Q)).toBinaryBicone
          isBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) } }

end

variable {P Q : C}

instance HasBinaryBiproduct.hasLimit_pair [HasBinaryBiproduct P Q] : HasLimit (pair P Q) :=
  HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩

instance HasBinaryBiproduct.hasColimit_pair [HasBinaryBiproduct P Q] : HasColimit (pair P Q) :=
  HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩

instance (priority := 100) hasBinaryProducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryProducts C where
  has_limit F := hasLimit_of_iso (diagramIsoPair F).symm

instance (priority := 100) hasBinaryCoproducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryCoproducts C where
  has_colimit F := hasColimit_of_iso (diagramIsoPair F)

/-- The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct. -/
def biprodIso (X Y : C) [HasBinaryBiproduct X Y] : Limits.prod X Y ≅ Limits.coprod X Y :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans <|
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

/-- An arbitrary choice of biproduct of a pair of objects. -/
abbrev biprod (X Y : C) [HasBinaryBiproduct X Y] :=
  (BinaryBiproduct.bicone X Y).pt

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
abbrev biprod.fst {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ X :=
  (BinaryBiproduct.bicone X Y).fst

/-- The projection onto the second summand of a binary biproduct. -/
abbrev biprod.snd {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ Y :=
  (BinaryBiproduct.bicone X Y).snd

/-- The inclusion into the first summand of a binary biproduct. -/
abbrev biprod.inl {X Y : C} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inl

/-- The inclusion into the second summand of a binary biproduct. -/
abbrev biprod.inr {X Y : C} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inr

section

variable {X Y : C} [HasBinaryBiproduct X Y]

@[simp] theorem BinaryBiproduct.bicone_fst : (BinaryBiproduct.bicone X Y).fst = biprod.fst := rfl

@[simp] theorem BinaryBiproduct.bicone_snd : (BinaryBiproduct.bicone X Y).snd = biprod.snd := rfl

@[simp] theorem BinaryBiproduct.bicone_inl : (BinaryBiproduct.bicone X Y).inl = biprod.inl := rfl

@[simp] theorem BinaryBiproduct.bicone_inr : (BinaryBiproduct.bicone X Y).inr = biprod.inr := rfl

end

@[reassoc]
theorem biprod.inl_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
  (BinaryBiproduct.bicone X Y).inl_fst

@[reassoc]
theorem biprod.inl_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
  (BinaryBiproduct.bicone X Y).inl_snd

@[reassoc]
theorem biprod.inr_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
  (BinaryBiproduct.bicone X Y).inr_fst

@[reassoc]
theorem biprod.inr_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
  (BinaryBiproduct.bicone X Y).inr_snd

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbrev biprod.lift {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  (BinaryBiproduct.isLimit X Y).lift (BinaryFan.mk f g)

/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbrev biprod.desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  (BinaryBiproduct.isColimit X Y).desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]
theorem biprod.lift_fst {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem biprod.lift_snd {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
theorem biprod.inl_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem biprod.inr_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩

instance biprod.mono_lift_of_mono_left {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_fst _ _

instance biprod.mono_lift_of_mono_right {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_snd _ _

instance biprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inl_desc _ _

instance biprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inr_desc _ _

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbrev biprod.map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z)
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbrev biprod.map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

@[ext]
theorem biprod.hom_ext {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y)
    (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁

@[ext]
theorem biprod.hom_ext' {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z)
    (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biprod.isoProd (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨯ Y :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biprod.isoProd_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).hom = prod.lift biprod.fst biprod.snd := by
      ext <;> simp [biprod.isoProd]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biprod.isoProd_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).inv = biprod.lift prod.fst prod.snd := by
  ext <;> simp [Iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biprod.isoCoprod (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨿ Y :=
  IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biprod.isoCoprod_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).inv = coprod.desc biprod.inl biprod.inr := by
  ext <;> simp [biprod.isoCoprod]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem biprod_isoCoprod_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).hom = biprod.desc coprod.inl coprod.inr := by
  ext <;> simp [← Iso.eq_comp_inv]

set_option backward.isDefEq.respectTransparency false in
theorem biprod.map_eq_map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g := by
  ext
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_right]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_right]
    simp

instance biprod.inl_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inl : X ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.fst }

instance biprod.inr_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inr : Y ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.snd }

instance biprod.fst_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.fst : X ⊞ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := biprod.inl }

instance biprod.snd_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.snd : X ⊞ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := biprod.inr }

@[reassoc (attr := simp)]
theorem biprod.map_fst {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)]
theorem biprod.map_snd {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[reassoc (attr := simp)]
theorem biprod.inl_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inl ≫ biprod.map f g = f ≫ biprod.inl := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem biprod.inr_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inr ≫ biprod.map f g = g ≫ biprod.inr := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.right⟩

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.mapIso {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z where
  hom := biprod.map f.hom g.hom
  inv := biprod.map f.inv g.inv

/-- Auxiliary lemma for `biprod.uniqueUpToIso`. -/
theorem biprod.conePointUniqueUpToIso_hom (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).hom =
      biprod.lift b.fst b.snd := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary lemma for `biprod.uniqueUpToIso`. -/
theorem biprod.conePointUniqueUpToIso_inv (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).inv =
      biprod.desc b.inl b.inr := by
  refine biprod.hom_ext' _ _ (hb.isLimit.hom_ext fun j => ?_) (hb.isLimit.hom_ext fun j => ?_)
  all_goals
    simp only [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals simp

/-- Binary biproducts are unique up to isomorphism. This already follows because bilimits are
limits, but in the case of biproducts we can give an isomorphism with particularly nice
definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc b.inl b.inr`
are inverses of each other. -/
@[simps]
def biprod.uniqueUpToIso (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) : b.pt ≅ X ⊞ Y where
  hom := biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb, ←
      biprod.conePointUniqueUpToIso_inv X Y hb, Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb, ←
      biprod.conePointUniqueUpToIso_inv X Y hb, Iso.inv_hom_id]

-- There are three further variations,
-- about `IsIso biprod.inr`, `IsIso biprod.fst` and `IsIso biprod.snd`,
-- but any one suffices to prove `indecomposable_of_simple`
-- and they are likely not separately useful.
theorem biprod.isIso_inl_iff_id_eq_fst_comp_inl (X Y : C) [HasBinaryBiproduct X Y] :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ 𝟙 (X ⊞ Y) = biprod.fst ≫ biprod.inl := by
  constructor
  · intro h
    have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 <| @biprod.inl_fst _ _ _ X Y _
    rw [IsIso.inv_hom_id_assoc, Category.comp_id] at this
    rw [this, IsIso.inv_hom_id]
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
instance biprod.map_epi {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Epi (biprod.map f g) := by
  rw [show biprod.map f g =
    (biprod.isoCoprod _ _).hom ≫ coprod.map f g ≫ (biprod.isoCoprod _ _).inv by aesop]
  infer_instance

instance prod.map_epi {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Epi (prod.map f g) := by
  rw [show prod.map f g = (biprod.isoProd _ _).inv ≫ biprod.map f g ≫
    (biprod.isoProd _ _).hom by simp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance biprod.map_mono {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Mono (biprod.map f g) := by
  rw [show biprod.map f g = (biprod.isoProd _ _).hom ≫ prod.map f g ≫
    (biprod.isoProd _ _).inv by aesop]
  infer_instance

instance coprod.map_mono {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Mono (coprod.map f g) := by
  rw [show coprod.map f g = (biprod.isoCoprod _ _).inv ≫ biprod.map f g ≫
    (biprod.isoCoprod _ _).hom by simp]
  infer_instance

section BiprodKernel

section BinaryBicone

variable {X Y : C} (c : BinaryBicone X Y)

/-- A kernel fork for the kernel of `BinaryBicone.fst`. It consists of the morphism
`BinaryBicone.inr`. -/
def BinaryBicone.fstKernelFork : KernelFork c.fst :=
  KernelFork.ofι c.inr c.inr_fst

@[simp]
theorem BinaryBicone.fstKernelFork_ι : (BinaryBicone.fstKernelFork c).ι = c.inr := rfl

/-- A kernel fork for the kernel of `BinaryBicone.snd`. It consists of the morphism
`BinaryBicone.inl`. -/
def BinaryBicone.sndKernelFork : KernelFork c.snd :=
  KernelFork.ofι c.inl c.inl_snd

@[simp]
theorem BinaryBicone.sndKernelFork_ι : (BinaryBicone.sndKernelFork c).ι = c.inl := rfl

/-- A cokernel cofork for the cokernel of `BinaryBicone.inl`. It consists of the morphism
`BinaryBicone.snd`. -/
def BinaryBicone.inlCokernelCofork : CokernelCofork c.inl :=
  CokernelCofork.ofπ c.snd c.inl_snd

@[simp]
theorem BinaryBicone.inlCokernelCofork_π : (BinaryBicone.inlCokernelCofork c).π = c.snd := rfl

/-- A cokernel cofork for the cokernel of `BinaryBicone.inr`. It consists of the morphism
`BinaryBicone.fst`. -/
def BinaryBicone.inrCokernelCofork : CokernelCofork c.inr :=
  CokernelCofork.ofπ c.fst c.inr_fst

@[simp]
theorem BinaryBicone.inrCokernelCofork_π : (BinaryBicone.inrCokernelCofork c).π = c.fst := rfl

variable {c}

set_option backward.isDefEq.respectTransparency false in
/-- The fork defined in `BinaryBicone.fstKernelFork` is indeed a kernel. -/
def BinaryBicone.isLimitFstKernelFork (i : IsLimit c.toCone) : IsLimit c.fstKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.snd, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The fork defined in `BinaryBicone.sndKernelFork` is indeed a kernel. -/
def BinaryBicone.isLimitSndKernelFork (i : IsLimit c.toCone) : IsLimit c.sndKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.fst, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The cofork defined in `BinaryBicone.inlCokernelCofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInlCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inlCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inr ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The cofork defined in `BinaryBicone.inrCokernelCofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInrCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inrCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inl ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

end BinaryBicone

section HasBinaryBiproduct

variable (X Y : C) [HasBinaryBiproduct X Y]

/-- A kernel fork for the kernel of `biprod.fst`. It consists of the
morphism `biprod.inr`. -/
def biprod.fstKernelFork : KernelFork (biprod.fst : X ⊞ Y ⟶ X) :=
  BinaryBicone.fstKernelFork _

@[simp]
theorem biprod.fstKernelFork_ι : Fork.ι (biprod.fstKernelFork X Y) = (biprod.inr : Y ⟶ X ⊞ Y) :=
  rfl

/-- The fork `biprod.fstKernelFork` is indeed a limit. -/
def biprod.isKernelFstKernelFork : IsLimit (biprod.fstKernelFork X Y) :=
  BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

/-- A kernel fork for the kernel of `biprod.snd`. It consists of the
morphism `biprod.inl`. -/
def biprod.sndKernelFork : KernelFork (biprod.snd : X ⊞ Y ⟶ Y) :=
  BinaryBicone.sndKernelFork _

@[simp]
theorem biprod.sndKernelFork_ι : Fork.ι (biprod.sndKernelFork X Y) = (biprod.inl : X ⟶ X ⊞ Y) :=
  rfl

/-- The fork `biprod.sndKernelFork` is indeed a limit. -/
def biprod.isKernelSndKernelFork : IsLimit (biprod.sndKernelFork X Y) :=
  BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inl`. It consists of the
morphism `biprod.snd`. -/
def biprod.inlCokernelCofork : CokernelCofork (biprod.inl : X ⟶ X ⊞ Y) :=
  BinaryBicone.inlCokernelCofork _

@[simp]
theorem biprod.inlCokernelCofork_π : Cofork.π (biprod.inlCokernelCofork X Y) = biprod.snd :=
  rfl

/-- The cofork `biprod.inlCokernelFork` is indeed a colimit. -/
def biprod.isCokernelInlCokernelFork : IsColimit (biprod.inlCokernelCofork X Y) :=
  BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inr`. It consists of the
morphism `biprod.fst`. -/
def biprod.inrCokernelCofork : CokernelCofork (biprod.inr : Y ⟶ X ⊞ Y) :=
  BinaryBicone.inrCokernelCofork _

@[simp]
theorem biprod.inrCokernelCofork_π : Cofork.π (biprod.inrCokernelCofork X Y) = biprod.fst :=
  rfl

/-- The cofork `biprod.inrCokernelFork` is indeed a colimit. -/
def biprod.isCokernelInrCokernelFork : IsColimit (biprod.inrCokernelCofork X Y) :=
  BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)

end HasBinaryBiproduct

variable {X Y : C} [HasBinaryBiproduct X Y]

instance : HasKernel (biprod.fst : X ⊞ Y ⟶ X) :=
  HasLimit.mk ⟨_, biprod.isKernelFstKernelFork X Y⟩

/-- The kernel of `biprod.fst : X ⊞ Y ⟶ X` is `Y`. -/
@[simps!]
def kernelBiprodFstIso : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y :=
  limit.isoLimitCone ⟨_, biprod.isKernelFstKernelFork X Y⟩

instance : HasKernel (biprod.snd : X ⊞ Y ⟶ Y) :=
  HasLimit.mk ⟨_, biprod.isKernelSndKernelFork X Y⟩

/-- The kernel of `biprod.snd : X ⊞ Y ⟶ Y` is `X`. -/
@[simps!]
def kernelBiprodSndIso : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X :=
  limit.isoLimitCone ⟨_, biprod.isKernelSndKernelFork X Y⟩

instance : HasCokernel (biprod.inl : X ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

/-- The cokernel of `biprod.inl : X ⟶ X ⊞ Y` is `Y`. -/
@[simps!]
def cokernelBiprodInlIso : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

instance : HasCokernel (biprod.inr : Y ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

/-- The cokernel of `biprod.inr : Y ⟶ X ⊞ Y` is `X`. -/
@[simps!]
def cokernelBiprodInrIso : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

end BiprodKernel

section IsZero

/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps!]
def isoBiprodZero {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ≅ X ⊞ Y where
  hom := biprod.inl
  inv := biprod.fst
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt

/-- If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`. -/
@[simps]
def isoZeroBiprod {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X) : Y ≅ X ⊞ Y where
  hom := biprod.inr
  inv := biprod.snd
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inr_snd, Category.comp_id, Category.id_comp, biprod.inr_fst,
        comp_zero]
    apply hY.eq_of_tgt

@[simp]
lemma biprod_isZero_iff (A B : C) [HasBinaryBiproduct A B] :
    IsZero (biprod A B) ↔ IsZero A ∧ IsZero B := by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    simp only [show 𝟙 A = biprod.inl ≫ 𝟙 (A ⊞ B) ≫ biprod.fst by simp,
      show 𝟙 B = biprod.inr ≫ 𝟙 (A ⊞ B) ≫ biprod.snd by simp, h, zero_comp, comp_zero,
      and_self]
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

end IsZero

section

variable [HasBinaryBiproducts C]

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps]
def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

/-- An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct. -/
@[simps]
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl

theorem biprod.braiding'_eq_braiding {P Q : C} : biprod.braiding' P Q = biprod.braiding P Q := by
  cat_disch

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    biprod.map f g ≫ (biprod.braiding _ _).hom = (biprod.braiding _ _).hom ≫ biprod.map g f := by
  cat_disch

@[reassoc]
theorem biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    (biprod.braiding X W).hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).hom = biprod.map g f := by
  cat_disch

@[reassoc (attr := simp)]
theorem biprod.symmetry' (P Q : C) :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) := by
  cat_disch

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
theorem biprod.symmetry (P Q : C) :
    (biprod.braiding P Q).hom ≫ (biprod.braiding Q P).hom = 𝟙 _ := by simp

/-- The associator isomorphism which associates a binary biproduct. -/
@[simps]
def biprod.associator (P Q R : C) : (P ⊞ Q) ⊞ R ≅ P ⊞ (Q ⊞ R) where
  hom := biprod.lift (biprod.fst ≫ biprod.fst) (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)
  inv := biprod.lift (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst)) (biprod.snd ≫ biprod.snd)

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.associator_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map (biprod.map f g) h ≫ (biprod.associator _ _ _).hom
      = (biprod.associator _ _ _).hom ≫ biprod.map f (biprod.map g h) := by
  cat_disch

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.associator_inv_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map f (biprod.map g h) ≫ (biprod.associator _ _ _).inv
      = (biprod.associator _ _ _).inv ≫ biprod.map (biprod.map f g) h := by
  cat_disch

end

end Limits

open CategoryTheory.Limits

-- TODO:
-- If someone is interested, they could provide the constructions:
--   HasBinaryBiproducts ↔ HasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- An object is indecomposable if it cannot be written as the biproduct of two nonzero objects. -/
def Indecomposable (X : C) : Prop :=
  ¬IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z

/-- If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
theorem isIso_left_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso f :=
  ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t := congrArg (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.hom_inv_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.inl_map_assoc] at t
        simp [t], by
        have t := congrArg (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.inv_hom_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.map_fst] at t
        simp only [Category.assoc]
        simp [t]⟩⟩⟩

/-- If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
theorem isIso_right_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso g :=
  letI : IsIso (biprod.map g f) := by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  isIso_left_of_isIso_biprod_map g f

open Opposite

namespace Limits

variable {P Q : C}

@[simps!]
def BinaryBicone.op (b : BinaryBicone P Q) :
    BinaryBicone (op P) (op Q) where
  pt := Opposite.op b.pt
  fst := b.inl.op
  snd := b.inr.op
  inl := b.fst.op
  inr := b.snd.op
  inl_fst := Quiver.Hom.unop_inj (by simp)
  inr_fst := Quiver.Hom.unop_inj (by simp)
  inl_snd := Quiver.Hom.unop_inj (by simp)
  inr_snd := Quiver.Hom.unop_inj (by simp)

def BinaryBicone.IsBilimit.op {b : BinaryBicone P Q} (h : b.IsBilimit) :
    b.op.IsBilimit where
  isLimit := BinaryCofan.IsColimit.op h.isColimit
  isColimit := BinaryFan.IsLimit.op h.isLimit

def BinaryBiproductData.op (d : BinaryBiproductData P Q) :
    BinaryBiproductData (op P) (op Q) where
  bicone := d.bicone.op
  isBilimit := d.isBilimit.op

instance [HasBinaryBiproduct P Q] :
    HasBinaryBiproduct (op P) (op Q) where
  exists_binary_biproduct := ⟨(getBinaryBiproductData P Q).op⟩

instance [HasBinaryBiproducts C] : HasBinaryBiproducts Cᵒᵖ where
  has_binary_biproduct X Y :=
    inferInstanceAs (HasBinaryBiproduct (op X.unop) (op Y.unop))

end Limits

end CategoryTheory
