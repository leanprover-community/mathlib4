/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Brendan Murphy
-/
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Lax, colax, and 2-commutative squares of functors

Similarly as `CommSq.lean` defines the notion of commutative squares,
this file introduces the notion of 2-commutative squares of functors.

If `T : C₁ ⥤ C₂`, `L : C₁ ⥤ C₃`, `R : C₂ ⥤ C₄`, `B : C₃ ⥤ C₄` are functors,
then `[CatCommSq T L R B]` contains the datum of an isomorphism `T ⋙ R ≅ L ⋙ B`.

We can weaken this by dropping the requirement that this "commutativity constraint" be
invertible. Because of the directed nature of (non-isomorphism) natural
transformations, there are two ways to do this. We call a square with a morphism
`T ⋙ R ⟶ L ⋙ B` a *colax square* and one with a morphism `L ⋙ B ⟶ T ⋙ R` a
*lax square*. Under this naming convention, and the one for oplax natural
transformations already in mathlib, a lax natural transformation has lax
naturality squares and an oplax natural transformation has colax naturality squares.

Future work: Using the notion of a CatCommSq in the development of the localization
of categories (e.g. localization of adjunctions).

-/

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category C₅] [Category C₆]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/-- `CatColaxSq T L R B` expresses that there is a square of functors, where the
functors `T`, `L`, `R` and `B` are respectively the left, top, right and bottom
functors of the square, equipped with a natural transformation from the bottom
left corner to the upper right corner. -/
@[ext]
structure CatColaxSq where
  /-- The 2-cell constraining the square to "colaxly commute". -/
  constraint : T ⋙ R ⟶ L ⋙ B

/-- `CatLaxSq T L R B` expresses that there is a square of functors, where the
functors `T`, `L`, `R` and `B` are respectively the left, top, right and bottom
functors of the square, equipped with a natural transformation from the upper
right corner to the bottom left corner. -/
@[ext]
structure CatLaxSq where
  /-- The 2-cell constraining the square to "laxly commute". -/
  constraint : L ⋙ B ⟶ T ⋙ R

/-- `CatCommSq T L R B` expresses that there is a 2-commutative square of functors, where
the functors `T`, `L`, `R` and `B` are respectively the left, top, right and bottom functors
of the square. -/
@[ext]
class CatCommSq where
  /-- the isomorphism corresponding to a 2-commutative diagram -/
  iso' : T ⋙ R ≅ L ⋙ B

namespace CatColaxSq

/-- Take the opposite of a square of categories and functors, flipping the
direction of the commutativity constraint. -/
@[simps]
def op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (σ : CatColaxSq T L R B) : CatLaxSq T.op L.op R.op B.op where
  constraint := (L.opCompIso B).hom ≫ NatTrans.op σ.constraint ≫ (T.opCompIso R).inv

/-- Take the unopposite of a square of opposite categories and functors,
flipping the direction of the commutativity constraint. -/
@[simps]
def unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ} {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ}
    (σ : CatColaxSq T L R B) : CatLaxSq T.unop L.unop R.unop B.unop where
  constraint :=
    (L.unopCompIso B).inv ≫ NatTrans.unop σ.constraint ≫ (T.unopCompIso R).hom

/-- Horizontal composition of colax squares. -/
@[simps]
def hComp {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅}
    {V₃ : C₃ ⥤ C₆} {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆}
    (s1 : CatColaxSq T₁ V₁ V₂ B₁) (s2 : CatColaxSq T₂ V₂ V₃ B₂) :
    CatColaxSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  constraint := (Functor.associator _ _ _).hom ≫
    whiskerLeft T₁ s2.constraint ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight s1.constraint B₂ ≫ (Functor.associator _ _ _).hom

/-- Vertical composition of colax squares. -/
@[simps]
def vComp {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅}
    {H₃ : C₃ ⥤ C₆} {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆}
    (s1 : CatColaxSq H₁ L₁ R₁ H₂) (s2 : CatColaxSq H₂ L₂ R₂ H₃) :
    CatColaxSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  constraint := (Functor.associator _ _ _).inv ≫
      whiskerRight s1.constraint R₂ ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft L₁ s2.constraint ≫ (Functor.associator _ _ _).inv

variable {T L R B}

/-- Abbreviation for the component of the constraint transformation. -/
@[pp_dot]
abbrev app (σ : CatColaxSq T L R B) (X : C₁) : R.obj (T.obj X) ⟶ B.obj (L.obj X) :=
  σ.constraint.app X

@[reassoc (attr:=simp↓)]
lemma naturality (σ : CatColaxSq T L R B) {X Y : C₁} (f : X ⟶ Y) :
    R.map (T.map f) ≫ σ.app Y = σ.app X ≫ B.map (L.map f) :=
  σ.constraint.naturality f

end CatColaxSq

namespace CatLaxSq

/-- Take the opposite of a square of categories and functors, flipping the
direction of the commutativity constraint. -/
@[simps]
def op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (σ : CatLaxSq T L R B) : CatColaxSq T.op L.op R.op B.op where
  constraint := (T.opCompIso R).inv ≫ NatTrans.op σ.constraint ≫ (L.opCompIso B).hom

/-- Take the unopposite of a square of opposite categories and functors,
flipping the direction of the commutativity constraint. -/
@[simps]
def unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ} {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ}
    (σ : CatLaxSq T L R B) : CatColaxSq T.unop L.unop R.unop B.unop where
  constraint :=
    (T.unopCompIso R).inv ≫ NatTrans.unop σ.constraint ≫ (L.unopCompIso B).hom

/-- Horizontal composition of lax squares. -/
@[simps]
def hComp {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄} {V₂ : C₂ ⥤ C₅}
    {V₃ : C₃ ⥤ C₆} {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆}
    (s1 : CatLaxSq T₁ V₁ V₂ B₁) (s2 : CatLaxSq T₂ V₂ V₃ B₂) :
    CatLaxSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  constraint := (Functor.associator _ _ _).inv ≫
    whiskerRight s1.constraint B₂ ≫ (Functor.associator _ _ _).hom ≫
    whiskerLeft T₁ s2.constraint ≫ (Functor.associator _ _ _).inv

-- should this be `vcomp` for consistency with `NatTrans.vcomp`?
-- Or should `NatTrans.vcomp` be `NatTrans.vComp`?
/-- Vertical composition of lax squares. -/
@[simps]
def vComp {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅}
    {H₃ : C₃ ⥤ C₆} {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆}
    (s1 : CatLaxSq H₁ L₁ R₁ H₂) (s2 : CatLaxSq H₂ L₂ R₂ H₃) :
    CatLaxSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  constraint := (Functor.associator _ _ _).hom ≫
    whiskerLeft L₁ s2.constraint ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight s1.constraint R₂ ≫ (Functor.associator _ _ _).hom

variable {T L R B}

/-- Abbreviation for the component of the constraint transformation. -/
abbrev app (σ : CatLaxSq T L R B) (X : C₁) : B.obj (L.obj X) ⟶ R.obj (T.obj X) :=
  σ.constraint.app X

@[reassoc (attr:=simp↓)]
lemma naturality (σ : CatLaxSq T L R B) {X Y : C₁} (f : X ⟶ Y) :
    B.map (L.map f) ≫ σ.app Y = σ.app X ≫ R.map (T.map f) :=
  σ.constraint.naturality f

end CatLaxSq

section Mates

variable {T L R B}

namespace CatColaxSq

@[simps]
def hMate [IsRightAdjoint T] [IsRightAdjoint B] (σ : CatColaxSq T L R B) :
    CatLaxSq (leftAdjoint T) R L (leftAdjoint B) :=
  ⟨(transferNatTrans (.ofRightAdjoint T) (.ofRightAdjoint B)).symm σ.constraint⟩

@[simps]
def vMate [IsLeftAdjoint L] [IsLeftAdjoint R] (σ : CatColaxSq T L R B) :
    CatLaxSq B (rightAdjoint L) (rightAdjoint R) T :=
  ⟨transferNatTrans (.ofLeftAdjoint L) (.ofLeftAdjoint R) σ.constraint⟩

end CatColaxSq

namespace CatLaxSq

@[simps]
def hMate [IsLeftAdjoint T] [IsLeftAdjoint B] (σ : CatLaxSq T L R B) :
    CatColaxSq (rightAdjoint T) R L (rightAdjoint B) :=
  ⟨transferNatTrans (.ofLeftAdjoint T) (.ofLeftAdjoint B) σ.constraint⟩

@[simps]
def vMate [IsRightAdjoint L] [IsRightAdjoint R] (σ : CatLaxSq T L R B) :
    CatColaxSq B (leftAdjoint L) (leftAdjoint R) T :=
  ⟨(transferNatTrans (.ofRightAdjoint L) (.ofRightAdjoint R)).symm σ.constraint⟩

end CatLaxSq

lemma CatColaxSq.hMate_hMate [IsRightAdjoint T] [IsRightAdjoint B]
    (σ : CatColaxSq T L R B) : σ.hMate.hMate = σ :=
  CatColaxSq.ext _ _ ((transferNatTrans _ _).apply_symm_apply _)

lemma CatColaxSq.vMate_vMate [IsLeftAdjoint L] [IsLeftAdjoint R]
    (σ : CatColaxSq T L R B) : σ.vMate.vMate = σ :=
  CatColaxSq.ext _ _ ((transferNatTrans _ _).symm_apply_apply _)

lemma CatLaxSq.hMate_hMate [IsLeftAdjoint T] [IsLeftAdjoint B]
    (σ : CatLaxSq T L R B) : σ.hMate.hMate = σ :=
  CatLaxSq.ext _ _ ((transferNatTrans _ _).symm_apply_apply _)

lemma CatLaxSq.vMate_vMate [IsRightAdjoint L] [IsRightAdjoint R]
    (σ : CatLaxSq T L R B) : σ.vMate.vMate = σ :=
  CatLaxSq.ext _ _ ((transferNatTrans _ _).apply_symm_apply _)

end Mates

namespace CatCommSq

/-- Assuming `[CatCommSq T L R B]`, `iso T L R B` is the isomorphism `T ⋙ R ≅ L ⋙ B`
given by the 2-commutative square. -/
def iso [CatCommSq T L R B] : T ⋙ R ≅ L ⋙ B := CatCommSq.iso'

variable {T L R B}

/-- Turn a pseudo-commutative square into a colax-commutative square by
forgetting that the constraint 2-cell is invertible. -/
@[simps]
def toColaxSq (h : CatCommSq T L R B) : CatColaxSq T L R B := ⟨h.iso'.hom⟩

/-- Turn a pseudo-commutative square into a lax-commutative square by
forgetting that the constraint 2-cell is invertible (and reversing it). -/
@[simps]
def toLaxSq (h : CatCommSq T L R B) : CatLaxSq T L R B := ⟨h.iso'.inv⟩

lemma toColaxSq_inj :
    Function.Injective (toColaxSq : CatCommSq T L R B → CatColaxSq T L R B) :=
  fun x y h => CatCommSq.ext x y (Iso.ext (congrArg CatColaxSq.constraint h))

lemma toLaxSq_inj :
    Function.Injective (toLaxSq : CatCommSq T L R B → CatLaxSq T L R B) :=
  fun x y h => CatCommSq.ext x y <| Iso.ext <| (Iso.inv_eq_inv _ _).mp <|
    congrArg CatLaxSq.constraint h

/-- Make a pseudo-commutative square out of a colax and a lax square, and a
proof that their constraint 2-cells are inverse. -/
@[simps]
def mkOfColaxOfLax (s1 : CatColaxSq T L R B) (s2 : CatLaxSq T L R B)
    (h1 : s1.constraint ≫ s2.constraint = 𝟙 (T ⋙ R))
    (h2 : s2.constraint ≫ s1.constraint = 𝟙 (L ⋙ B)) : CatCommSq T L R B where
  iso' := ⟨s1.constraint, s2.constraint, h1, h2⟩

@[simps]
def flip (_ : CatCommSq T L R B) : CatCommSq L T B R where
  iso' := (iso T L R B).symm

@[simp] lemma flip_flip (σ : CatCommSq T L R B) : σ.flip.flip = σ := rfl

lemma flip_inj : (flip : CatCommSq T L R B → CatCommSq L T B R).Injective :=
  fun σ τ h => Eq.trans σ.flip_flip.symm (Eq.trans (congrArg _ h) τ.flip_flip)

@[simps]
def op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (σ : CatCommSq T L R B) : CatCommSq T.op L.op R.op B.op where
  iso' := (T.opCompIso R).symm ≪≫ NatIso.op σ.iso'.symm ≪≫ L.opCompIso B

@[simps]
def unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ} {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ}
    (σ : CatCommSq T L R B) : CatCommSq T.unop L.unop R.unop B.unop where
  iso' := (T.unopCompIso R).symm ≪≫ NatIso.unop σ.iso'.symm ≪≫ L.unopCompIso B

variable (T L R B)

/-- Horizontal composition of 2-commutative squares -/
@[simps iso']
def hComp (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
    (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆) [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂] :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  iso' := Functor.associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    Functor.associator _ _ _

/-- Vertical composition of 2-commutative squares -/
@[simps iso']
def vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃] :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  iso' := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (Functor.associator _ _ _).symm

@[simp]
lemma hComp_toColaxSq {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄}
    {V₂ : C₂ ⥤ C₅} {V₃ : C₃ ⥤ C₆} {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆}
    (s1 : CatCommSq T₁ V₁ V₂ B₁) (s2 : CatCommSq T₂ V₂ V₃ B₂) :
    (@hComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2).toColaxSq =
      s1.toColaxSq.hComp s2.toColaxSq := rfl

@[simp]
lemma vComp_toColaxSq {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄}
    {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆} {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆}
    (s1 : CatCommSq H₁ L₁ R₁ H₂) (s2 : CatCommSq H₂ L₂ R₂ H₃) :
    (@vComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2).toColaxSq =
      s1.toColaxSq.vComp s2.toColaxSq := rfl

@[simp]
lemma hComp_toLaxSq {T₁ : C₁ ⥤ C₂} {T₂ : C₂ ⥤ C₃} {V₁ : C₁ ⥤ C₄}
    {V₂ : C₂ ⥤ C₅} {V₃ : C₃ ⥤ C₆} {B₁ : C₄ ⥤ C₅} {B₂ : C₅ ⥤ C₆}
    (s1 : CatCommSq T₁ V₁ V₂ B₁) (s2 : CatCommSq T₂ V₂ V₃ B₂) :
    (@hComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2).toLaxSq =
      s1.toLaxSq.hComp s2.toLaxSq := by aesop_cat

@[simp]
lemma vComp_toLaxSq {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄}
    {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆} {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆}
    (s1 : CatCommSq H₁ L₁ R₁ H₂) (s2 : CatCommSq H₂ L₂ R₂ H₃) :
    (@vComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2).toLaxSq =
      s1.toLaxSq.vComp s2.toLaxSq := by aesop_cat

section

variable (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)

/-- Horizontal inverse of a 2-commutative square -/
@[simps! iso'_hom_app iso'_inv_app]
def hInv (_ : CatCommSq T.functor L R B.functor) : CatCommSq T.inverse R L B.inverse where
  iso' := isoWhiskerLeft _ (L.rightUnitor.symm ≪≫ isoWhiskerLeft L B.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (iso T.functor L R B.functor).symm B.inverse ≪≫
      Functor.associator _ _ _  ) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight T.counitIso _ ≪≫ Functor.leftUnitor _

end

end CatCommSq

section Opposites

lemma CatColaxSq.op_unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ}
    {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ} (σ : CatColaxSq T L R B) : σ.unop.op = σ := by
  aesop_cat

lemma CatColaxSq.unop_op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} (σ : CatColaxSq T L R B) : σ.op.unop = σ := by
  aesop_cat

lemma CatLaxSq.op_unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ}
    {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ} (σ : CatLaxSq T L R B) : σ.unop.op = σ := by
  aesop_cat

lemma CatLaxSq.unop_op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} (σ : CatLaxSq T L R B) : σ.op.unop = σ := by
  aesop_cat

lemma CatCommSq.op_unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ}
    {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ} (σ : CatCommSq T L R B) : σ.unop.op = σ := by
  aesop_cat

lemma CatCommSq.unop_op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} (σ : CatCommSq T L R B) : σ.op.unop = σ := by
  aesop_cat

lemma CatCommSq.flip_unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ}
    {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ} (σ : CatCommSq T L R B) : σ.unop.flip = σ.flip.unop := by
  ext
  dsimp [iso]
  simp

lemma CatCommSq.flip_op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} (σ : CatCommSq T L R B) : σ.op.flip = σ.flip.op := by
  ext
  dsimp [iso]
  simp

lemma CatCommSq.toLaxSq_op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} (σ : CatCommSq T L R B) :
    σ.op.toLaxSq = σ.toColaxSq.op := by
  ext : 1; exact assoc _ _ _

lemma CatCommSq.toColaxSq_op {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} (σ : CatCommSq T L R B) :
    σ.op.toColaxSq = σ.toLaxSq.op := rfl

lemma CatCommSq.toLaxSq_unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ}
    {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ} (σ : CatCommSq T L R B) :
    σ.unop.toLaxSq = σ.toColaxSq.unop := by
  ext : 1; exact assoc _ _ _

lemma CatCommSq.toColaxSq_unop {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ}
    {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ} (σ : CatCommSq T L R B) :
    σ.unop.toColaxSq = σ.toLaxSq.unop := rfl

end Opposites

namespace CatCommSq

section

variable (T : C₁ ⥤ C₂) (L : C₁ ≌ C₃) (R : C₂ ≌ C₄) (B : C₃ ⥤ C₄)

/-- Horizontal inverse of a 2-commutative square -/
@[simps! iso'_hom_app iso'_inv_app]
def vInv (_ : CatCommSq T L.functor R.functor B) : CatCommSq B L.inverse R.inverse T where
  iso' :=
    isoWhiskerRight B.leftUnitor.symm R.inverse ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerRight L.counitIso.symm (B ⋙ R.inverse) ≪≫
        Functor.associator _ _ _ ≪≫
          isoWhiskerLeft L.inverse (Functor.associator _ _ _).symm ≪≫
            isoWhiskerLeft L.inverse (isoWhiskerRight
              (iso T L.functor R.functor B).symm R.inverse) ≪≫
                isoWhiskerLeft L.inverse (Functor.associator _ _ _) ≪≫
                  (Functor.associator _ _ _).symm ≪≫
                    isoWhiskerLeft _ R.unitIso.symm ≪≫ Functor.rightUnitor _

end

section

variable {T : C₁ᵒᵖ ≌ C₂ᵒᵖ} {L : C₁ᵒᵖ ⥤ C₃ᵒᵖ} {R : C₂ᵒᵖ ⥤ C₄ᵒᵖ} {B : C₃ᵒᵖ ≌ C₄ᵒᵖ}

lemma hInv_unop (σ : CatCommSq T.functor L R B.functor) :
    σ.unop.hInv T.unop L.unop R.unop B.unop = (σ.hInv).unop := by
  ext
  dsimp [iso]
  simp

lemma hInv_op (σ : CatCommSq T.functor L R B.functor) :
    σ.op.hInv T.op L.op R.op B.op = (σ.hInv).op := by
  ext
  dsimp [iso]
  simp

variable {T : C₁ ≌ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ≌ C₄}

lemma hInv_flip (σ : CatCommSq T.functor L R B.functor) :
    (σ.hInv).flip = (σ.flip).vInv := by
  ext; dsimp [iso]; simp

lemma hInv_toLaxSq (σ : CatCommSq T.functor L R B.functor) :
    (σ.hInv).toLaxSq = σ.toColaxSq.hMate := by
  ext
  erw [CatColaxSq.hMate_constraint, transferNatTrans_symm_apply]
  dsimp
  simp only [whiskerLeft_twice, id_comp, comp_id, assoc]
  rfl

lemma hInv_toColaxSq (σ : CatCommSq T.functor L R B.functor) :
    (σ.hInv).toColaxSq = σ.toLaxSq.hMate := by
  ext
  erw [CatLaxSq.hMate_constraint, transferNatTrans_apply]
  dsimp
  simp only [whiskerLeft_twice, id_comp, comp_id, assoc, Functor.map_id]
  rfl

lemma hInv_iso_hom_mate_iso_inv (σ : CatCommSq T.functor L R B.functor) :
    (σ.hInv).iso'.hom =
      transferNatTrans T.toAdjunction B.toAdjunction σ.iso'.inv :=
  congrArg CatColaxSq.constraint (hInv_toColaxSq σ)

lemma hInv_iso_inv_mate_iso_hom (σ : CatCommSq T.functor L R B.functor) :
    (σ.hInv).iso'.inv =
      (transferNatTrans T.symm.toAdjunction B.symm.toAdjunction).symm σ.iso'.hom :=
  congrArg CatLaxSq.constraint (hInv_toLaxSq σ)

end

section

variable {T : C₁ᵒᵖ ⥤ C₂ᵒᵖ} {L : C₁ᵒᵖ ≌ C₃ᵒᵖ} {R : C₂ᵒᵖ ≌ C₄ᵒᵖ} {B : C₃ᵒᵖ ⥤ C₄ᵒᵖ}

lemma vInv_unop (σ : CatCommSq T L.functor R.functor B) :
    σ.unop.vInv T.unop L.unop R.unop B.unop = (σ.vInv).unop := by
  ext
  dsimp [iso]
  simp

variable {T : C₁ ⥤ C₂} {L : C₁ ≌ C₃} {R : C₂ ≌ C₄} {B : C₃ ⥤ C₄}

lemma vInv_op (σ : CatCommSq T L.functor R.functor B) :
    σ.op.vInv T.op L.op R.op B.op = (σ.vInv).op := by
  ext
  dsimp [iso]
  simp

lemma vInv_flip (σ : CatCommSq T L.functor R.functor B) :
    (σ.vInv).flip = (σ.flip).hInv := by
  ext; dsimp [iso]; simp

lemma vInv_toLaxSq (σ : CatCommSq T L.functor R.functor B) :
    (σ.vInv).toLaxSq = σ.toColaxSq.vMate := by
  ext
  erw [CatColaxSq.vMate_constraint, transferNatTrans_apply]
  dsimp
  simp only [whiskerLeft_twice, id_comp, comp_id, assoc, Functor.map_id]
  rfl

lemma vInv_toColaxSq (σ : CatCommSq T L.functor R.functor B) :
    (σ.vInv).toColaxSq = σ.toLaxSq.vMate := by
  ext
  erw [CatLaxSq.vMate_constraint, transferNatTrans_symm_apply]
  dsimp
  simp only [whiskerLeft_twice, id_comp, comp_id, assoc, Functor.map_id]
  rfl

lemma vInv_iso_hom_mate_iso_inv (σ : CatCommSq T L.functor R.functor B) :
    (σ.vInv).iso'.hom =
      (transferNatTrans L.symm.toAdjunction R.symm.toAdjunction).symm σ.iso'.inv :=
  congrArg CatColaxSq.constraint (vInv_toColaxSq σ)

lemma vInv_iso_inv_mate_iso_hom (σ : CatCommSq T L.functor R.functor B) :
    (σ.vInv).iso'.inv =
      transferNatTrans L.toAdjunction R.toAdjunction σ.iso'.hom :=
  congrArg CatLaxSq.constraint (vInv_toLaxSq σ)

end

section

variable (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)

lemma hInv_hInv (h : CatCommSq T.functor L R B.functor) :
    hInv T.symm R L B.symm (hInv T L R B h) = h := by
  ext : 2
  rw [hInv_iso_hom_mate_iso_inv, hInv_iso_inv_mate_iso_hom, Equiv.apply_symm_apply]

/-- In a square of categories, when the top and bottom functors are part
of equivalence of categorires, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
def hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  toFun := hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm

end

section

variable (T : C₁ ⥤ C₂) (L : C₁ ≌ C₃) (R : C₂ ≌ C₄) (B : C₃ ⥤ C₄)

lemma vInv_vInv (h : CatCommSq T L.functor R.functor B) :
    vInv B L.symm R.symm T (vInv T L R B h) = h := by
  ext : 2
  erw [vInv_iso_hom_mate_iso_inv, vInv_iso_inv_mate_iso_hom, Equiv.symm_apply_apply]

/-- In a square of categories, when the left and right functors are part
of equivalence of categorires, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
def vInvEquiv : CatCommSq T L.functor R.functor B ≃ CatCommSq B L.inverse R.inverse T where
  toFun := vInv T L R B
  invFun := vInv B L.symm R.symm T
  left_inv := vInv_vInv T L R B
  right_inv := vInv_vInv B L.symm R.symm T

end

instance hInv' [h : CatCommSq T L R B] [IsEquivalence T] [IsEquivalence B] :
    CatCommSq T.inv R L B.inv :=
  hInv T.asEquivalence L R B.asEquivalence h

instance vInv' [h : CatCommSq T L R B] [IsEquivalence L] [IsEquivalence R] :
    CatCommSq B L.inv R.inv T :=
  vInv T L.asEquivalence R.asEquivalence B h

end CatCommSq

end CategoryTheory
