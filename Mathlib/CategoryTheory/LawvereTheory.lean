/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory

universe v v' u u'

/--
TODO
-/
inductive ProdWord (S : Type u) where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

/--
TODO
-/
structure LawvereTheory (S : Type u) where
  /-- TODO -/
  hom : ProdWord S → ProdWord S → Type v
  /-- TODO -/
  id (P : ProdWord S) : hom P P
  /-- TODO -/
  comp {P Q R : ProdWord S} : hom P Q → hom Q R → hom P R
  id_comp {P Q : ProdWord S} (f : hom P Q) : comp (id _) f = f
  comp_id {P Q : ProdWord S} (f : hom P Q) : comp f (id _) = f
  assoc {P Q R W : ProdWord S} (f : hom P Q) (g : hom Q R) (h : hom R W) :
    comp (comp f g) h = comp f (comp g h)
  /-- TODO -/
  fst' (H T : ProdWord S) : hom (H.prod T) H
  /-- TODO -/
  snd' (H T : ProdWord S): hom (H.prod T) T
  /-- TODO -/
  lift' {T X Y : ProdWord S} (f : hom T X) (g : hom T Y) : hom T (X.prod Y)
  lift_fst' {T X Y : ProdWord S} (f : hom T X) (g : hom T Y) :
    comp (lift' f g) (fst' _ _) = f
  lift_snd' {T X Y : ProdWord S} (f : hom T X) (g : hom T Y) :
    comp (lift' f g) (snd' _ _) = g
  lift_unique' {T X Y : ProdWord S} (f g : hom T (X.prod Y)) :
    comp f (fst' _ _) = comp g (fst' _ _) →
    comp f (snd' _ _) = comp g (snd' _ _) →
    f = g
  /-- TODO -/
  toNil (P : ProdWord S) :
    hom P .nil
  toNil_unique {P : ProdWord S} (f g : hom P .nil) :
    f = g

namespace LawvereTheory

variable {S : Type u} (L : LawvereTheory.{v} S)


/--
TODO
-/
structure Carrier (L : LawvereTheory.{v} S) where
  /-- TODO -/
  as : ProdWord S

instance : CoeSort (LawvereTheory.{v} S) (Type u) where
  coe L := L.Carrier

instance (L : LawvereTheory.{v} S) : Category.{v} L where
  Hom X Y := L.hom X.as Y.as
  id _ := L.id _
  comp := L.comp
  id_comp := L.id_comp
  comp_id := L.comp_id
  assoc := L.assoc

instance : ChosenFiniteProducts L where
  product X Y := .mk
    (Limits.BinaryFan.mk (L.fst' X.as Y.as) (L.snd' X.as Y.as))
    (Limits.BinaryFan.isLimitMk
      (fun S => L.lift' S.fst S.snd)
      (fun S => L.lift_fst' _ _)
      (fun S => L.lift_snd' _ _)
      (fun S m h1 h2 => L.lift_unique' _ _
        (by simpa [L.lift_fst'] using h1)
        (by simpa [L.lift_snd'] using h2)))
  terminal := .mk
    (.mk (.mk .nil) <| .mk (fun x => x.as.elim) (fun x => x.as.elim))
    (.mk (fun S => L.toNil _) (fun _ x => x.as.elim) (fun _ _ _ => L.toNil_unique _ _))

abbrev of (X : ProdWord S) : L := .mk X
abbrev singleton (X : S) : L := .mk <| .of X

open ChosenFiniteProducts MonoidalCategory

@[simp]
lemma Carrier.of_nil : L.of .nil = 𝟙_ _ := rfl

@[simp]
lemma Carrier.of_prod (X Y : ProdWord S) : L.of (X.prod Y) = L.of X ⊗ L.of Y := rfl

@[simp]
lemma Carrier.of_of (X : S) : L.of (.of X) = L.singleton X := rfl

structure Algebra (C : Type u') [Category.{v'} C] where
  functor : L ⥤ C
  isLimit (X Y : L) :
    Limits.IsLimit (Limits.BinaryFan.mk
      (functor.map <| fst X Y)
      (functor.map <| snd X Y))
  isTerminal : Limits.IsTerminal (functor.obj <| 𝟙_ _)

def Algebra.toUnit
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) (T : C) :
    T ⟶ A.functor.obj (𝟙_ _) :=
  A.isTerminal.lift <| .mk _ <| .mk (fun j => j.as.elim) (fun j => j.as.elim)

variable {L}

lemma Algebra.toUnit_unique
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C}
    (f g : T ⟶ A.functor.obj (𝟙_ _)) : f = g :=
  A.isTerminal.hom_ext _ _

def Algebra.lift
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f : T ⟶ A.functor.obj X)
    (g : T ⟶ A.functor.obj Y) :
    T ⟶ A.functor.obj (X ⊗ Y) :=
  (A.isLimit _ _).lift <| Limits.BinaryFan.mk f g

@[reassoc (attr := simp)]
lemma Algebra.lift_fst
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f : T ⟶ A.functor.obj X) (g : T ⟶ A.functor.obj Y) :
    A.lift f g ≫ A.functor.map (fst _ _) = f :=
  (A.isLimit _ _).fac _ <| .mk .left

@[reassoc (attr := simp)]
lemma Algebra.lift_snd
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f : T ⟶ A.functor.obj X) (g : T ⟶ A.functor.obj Y) :
    A.lift f g ≫ A.functor.map (snd _ _) = g :=
  (A.isLimit _ _).fac _ <| .mk .right

@[ext 1050]
def Algebra.hom_ext
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f g : T ⟶ A.functor.obj (X ⊗ Y))
    (h_fst : f ≫ A.functor.map (fst _ _) = g ≫ A.functor.map (fst _ _))
    (h_snd : f ≫ A.functor.map (snd _ _) = g ≫ A.functor.map (snd _ _)) : f = g := by
  apply (A.isLimit _ _).hom_ext
  rintro (_|_)
  · exact h_fst
  · exact h_snd

instance (C : Type u') [Category.{v'} C] : Category (L.Algebra C) :=
  InducedCategory.category fun A => A.functor

variable (L) in
@[simps]
def algebraForget (C : Type u') [Category.{v'} C] :
    L.Algebra C ⥤ (S → C) where
  obj A X := A.functor.obj <| L.singleton X
  map f X := f.app _

instance (C : Type u') [Category.{v'} C] : Faithful (L.algebraForget C) where
  map_injective {X Y f g} h := by
    apply NatTrans.ext ; funext ⟨P⟩
    induction P with
    | of T =>
      apply congr_fun h
    | prod U V h1 h2 =>
      dsimp only [Carrier.of_prod]
      apply Y.hom_ext
      · simp only [← NatTrans.naturality, h1]
      · simp only [← NatTrans.naturality, h2]
    | nil => apply Y.isTerminal.hom_ext

@[ext]
lemma Algebra.morphism_ext {C : Type u'} [Category.{v'} C] {X Y : L.Algebra C}
    (f g : X ⟶ Y) (h : ∀ (X : S), f.app (L.singleton X) = g.app (L.singleton X)) :
    f = g :=
  (algebraForget L C).map_injective <| funext h

section free

variable (L) (X : S → Type u')
inductive FreeRep : ProdWord S → Type (max v u u') where
  | of (T : S) : X T → FreeRep (.of T)
  | map (A B : ProdWord S) : L.hom A B → FreeRep A → FreeRep B
  | lift (A B : ProdWord S) : FreeRep A → FreeRep B → FreeRep (A.prod B)
  | unit : FreeRep .nil

inductive FreeRel :
    {A : ProdWord S} → L.FreeRep X A → L.FreeRep X A → Prop where
  | rfl {A : ProdWord S} (f : L.FreeRep X A) : FreeRel f f
  | symm {A : ProdWord S} {f g : L.FreeRep X A} : FreeRel f g → FreeRel g f
  | trans {A : ProdWord S} {f g h : L.FreeRep X A} :
    FreeRel f g → FreeRel g h → FreeRel f h
  | map_congr (A B : ProdWord S) {x y : L.FreeRep X A} {f : L.hom A B} :
      FreeRel x y → FreeRel (x.map _ _ f) (y.map _ _ f)
  | map_id (A : ProdWord S) (x : L.FreeRep X A) :
      FreeRel (x.map _ _ <| L.id A) x
  | map_comp (A B C : ProdWord S) (f : L.hom A B) (g : L.hom B C) (x : L.FreeRep X A) :
      FreeRel (x.map _ _ <| L.comp f g) ((x.map _ _ f).map _ _ g)
  | lift_fst (A B : ProdWord S) (x : L.FreeRep X A) (y : L.FreeRep X B) :
      FreeRel ((FreeRep.lift _ _ x y).map _ _ <| L.fst' _ _) x
  | lift_snd (A B : ProdWord S) (x : L.FreeRep X A) (y : L.FreeRep X B) :
      FreeRel ((FreeRep.lift _ _ x y).map _ _ <| L.snd' _ _) y
  | lift_unique (A B : ProdWord S) (x y : L.FreeRep X (A.prod B)) :
      FreeRel (x.map _ _ <| L.fst' _ _) (y.map _ _ <| L.fst' _ _) →
      FreeRel (x.map _ _ <| L.snd' _ _) (y.map _ _ <| L.snd' _ _) →
      FreeRel x y
  | lift_congr (A B : ProdWord S)
      (x x' : L.FreeRep X A)
      (y y' : L.FreeRep X B) :
      FreeRel x x' →
      FreeRel y y' →
      FreeRel (x.lift _ _ y) (x'.lift _ _ y')
  | unit_unique (x y : L.FreeRep X .nil) : FreeRel x y

def freeSetoid (A : ProdWord S) :
    Setoid (L.FreeRep X A) where
  r := L.FreeRel _
  iseqv := ⟨.rfl, .symm, .trans⟩

def free (A : ProdWord S) : Type _ :=
  Quotient <| L.freeSetoid X A

variable {L X}
def free.fst {A B : ProdWord S} :
    L.free X (A.prod B) → L.free X A :=
  Quotient.lift (fun a => Quotient.mk _ <| a.map _ _ <| L.fst' _ _)
  fun _ _ h => Quotient.sound <| .map_congr _ _ h

def free.snd {A B : ProdWord S} :
    L.free X (A.prod B) → L.free X B :=
  Quotient.lift (fun a => Quotient.mk _ <| a.map _ _ <| L.snd' _ _)
  fun _ _ h => Quotient.sound <| .map_congr _ _ h

def free.lift {A B : ProdWord S}
    (x : L.free X A) (y : L.free X B) :
    L.free X (A.prod B) :=
  Quotient.liftOn₂ x y (fun a b => Quotient.mk _ <| .lift _ _ a b)
  fun _ _ _ _ h₁ h₂ => Quotient.sound <| .lift_congr _ _ _ _ _ _ h₁ h₂

lemma free.lift_fst {A B : ProdWord S}
    (x : L.free X A) (y :  L.free X B) :
    (x.lift y).fst = x := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  apply Quotient.sound
  apply FreeRel.lift_fst

lemma free.lift_snd {A B : ProdWord S}
    (x : L.free X A) (y :  L.free X B) :
    (x.lift y).snd = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  apply Quotient.sound
  apply FreeRel.lift_snd

lemma free.lift_ext {A B : ProdWord S}
    (x y : L.free X (A.prod B))
    (h_fst : x.fst = y.fst)
    (h_snd : x.snd = y.snd) :
    x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  apply Quotient.sound
  apply FreeRel.lift_unique
  exact Quotient.exact h_fst
  exact Quotient.exact h_snd

lemma free.unit_ext
    (x y : L.free X .nil) : x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨x⟩
  apply Quotient.sound
  apply FreeRel.unit_unique

variable (L X)
def freeAlgebra : L.Algebra (Type (max v u u')) where
  functor := {
    obj := fun A => L.free X A.as
    map := fun f =>
      Quotient.lift
      (fun r => Quotient.mk _ <| FreeRep.map _ _ f r)
      fun a b h => Quotient.sound <| .map_congr _ _ h
    map_id := by
      rintro ⟨A⟩
      ext ⟨T⟩
      apply Quotient.sound
      apply FreeRel.map_id
    map_comp := by
      rintro ⟨A⟩ ⟨B⟩ ⟨C⟩ f g
      ext ⟨T⟩
      apply Quotient.sound
      apply FreeRel.map_comp }
  isLimit := fun ⟨A⟩ ⟨B⟩ => Limits.BinaryFan.isLimitMk
    (fun S x => free.lift _ _)
    (fun S => funext fun x => free.lift_fst _ _)
    (fun S => funext fun x => free.lift_snd _ _)
    (fun S m h1 h2 => funext fun x => free.lift_ext _ _
      (by simp only [free.lift_fst] ; exact congr_fun h1 _)
      (by simp only [free.lift_snd] ; exact congr_fun h2 _))
  isTerminal := .mk
    (fun S _ => Quotient.mk _ <| .unit)
    (fun S j => j.as.elim)
    (fun S _ _ => funext fun _ => free.unit_ext _ _)

variable {L X} {Y : S → Type u'} (f : X ⟶ Y)

def liftRep
    (Y : L.Algebra (Type max v u u'))
    (f : (A : S) → X A → Y.functor.obj (L.singleton A)) :
    (A : ProdWord S) → L.FreeRep X A ⟶ Y.functor.obj (L.of A)
  | .of _, .of _ x => f _ x
  | .of _, .map _ _ e x => Y.functor.map e (liftRep _ f _ x)
  | .prod _ _, .map _ _ e x => Y.functor.map e (liftRep _ f _ x)
  | .prod _ _, .lift _ _ x y =>
    Y.lift (fun t => t.fst) (fun t => t.snd) (liftRep Y f _ x, liftRep Y f _ y)
  | .nil, .map _ _ e x => Y.functor.map e (liftRep _ f _ x)
  | .nil, .unit => Y.toUnit _ _ PUnit.unit

def liftAppAux
    (Y : L.Algebra (Type max v u u'))
    (f : (A : S) → X A → Y.functor.obj (L.singleton A)) (A : ProdWord S) :
    L.free X A → Y.functor.obj (L.of A) :=
  Quotient.lift
    (liftRep _ f _)
    fun a b h => by
      induction h with
      | rfl f => rfl
      | symm _ h => exact h.symm
      | trans _ _ h1 h2 => exact h1.trans h2
      | map_congr _ B _ h => cases B <;> simp [liftRep, h]
      | map_id A x => cases A <;> { change Y.functor.map (𝟙 _) _ = _ ; simp }
      | map_comp A B C f g x =>
        cases C <;> {
          show Y.functor.map (_ ≫ _) _ = _
          simp only [Carrier.of_of, FunctorToTypes.map_comp_apply, liftRep]
          cases B with
          | of _ => simp [liftRep]
          | prod _ _ => simp [liftRep]
          | nil => simp [liftRep] }
      | lift_fst A B x y =>
        cases A <;> {
          show (Y.lift _ _ ≫ Y.functor.map (fst _ _)) _ = _
          rw [Y.lift_fst] }
      | lift_snd A B x y =>
        cases B <;> {
          show (Y.lift _ _ ≫ Y.functor.map (snd _ _)) _ = _
          rw [Y.lift_snd] }
      | lift_unique A B x y _ _ h1 h2 =>
        dsimp [liftRep]
        let ex : PUnit ⟶ Y.functor.obj (L.of A ⊗ L.of B) := fun _ =>
          liftRep Y f (ProdWord.prod A B) x
        let ey : PUnit ⟶ Y.functor.obj (L.of A ⊗ L.of B) := fun _ =>
          liftRep Y f (ProdWord.prod A B) y
        suffices ex = ey from congr_fun this .unit
        apply Y.hom_ext
        · funext ; cases A <;> exact h1
        · funext ; cases B <;> exact h2
      | lift_congr A B x x' y y' _ _ h1 h2 => simp [liftRep, h1,h2]
      | unit_unique x y =>
        let ex : PUnit ⟶ Y.functor.obj (𝟙_ _) := fun _ => liftRep Y f ProdWord.nil x
        let ey : PUnit ⟶ Y.functor.obj (𝟙_ _) := fun _ => liftRep Y f ProdWord.nil y
        have : ex = ey := Y.toUnit_unique _ _
        change ex .unit = ey .unit
        rw [this]

def lift
    (Y : L.Algebra (Type max v u u'))
    (f : (A : S) → X A → Y.functor.obj (L.singleton A)) :
    L.freeAlgebra X ⟶ Y where
  app := fun ⟨A⟩ => liftAppAux Y f A
  naturality := by
    rintro ⟨A⟩ ⟨B⟩ f
    apply funext
    rintro ⟨x⟩
    dsimp [freeAlgebra] at x ⊢
    cases x with
    | of _ => cases B <;> rfl
    | map _ => cases B <;> rfl
    | lift _ _ => cases B <;> rfl
    | unit => cases B <;> rfl

variable (X) in
def incl (A : S) : X A → L.free X (.of A) :=
  fun x => Quotient.mk _ <| .of _ x

def inclHom (L : LawvereTheory.{u} S) (X : S → Type u) :
  X ⟶ (L.algebraForget _).obj (L.freeAlgebra X) := L.incl _

@[simp]
lemma incl_lift
    (Y : L.Algebra (Type max v u u'))
    (f : (A : S) → X A → Y.functor.obj (L.singleton A))
    (A : S)
    (x : X A) :
    (lift Y f).app (L.singleton A) (incl X _ x) = f _ x :=
  rfl

lemma lift_unique
    (Y : L.Algebra (Type max v u u'))
    (f g : L.freeAlgebra X ⟶ Y)
    (h : ∀ (A : S) (x : X A),
      f.app (L.singleton A) (incl _ _ x) = g.app (L.singleton A) (incl _ _ x)) :
    f = g := by
  apply NatTrans.ext ; funext ⟨A⟩
  apply funext ; rintro ⟨x⟩
  dsimp at x
  induction x with
  | of _ => apply h
  | map A B e x h =>
    dsimp [freeAlgebra] at h
    specialize h (Quotient.mk _ x)
    let FA := L.freeAlgebra X
    change
      (FA.functor.map e ≫ f.app (.mk B)) (Quotient.mk _ x) =
      (FA.functor.map e ≫ g.app (.mk B)) (Quotient.mk _ x)
    simp_rw [NatTrans.naturality]
    change f.app ⟨A⟩ ⟦x⟧ = _ at h
    simp [h]
    rfl
  | lift A B x y h1 h2 =>
    let FA := L.freeAlgebra X
    let x' : FA.functor.obj (L.of A) := Quotient.mk _ x
    let y' : FA.functor.obj (L.of B) := Quotient.mk _ y
    let π1 : FA.functor.obj (L.of A) × FA.functor.obj (L.of B) ⟶ FA.functor.obj (L.of A) :=
      _root_.Prod.fst
    let π2 : FA.functor.obj (L.of A) × FA.functor.obj (L.of B) ⟶ FA.functor.obj (L.of B) :=
      _root_.Prod.snd
    specialize h1 x'
    specialize h2 y'
    change (FA.lift π1 π2 ≫ f.app _) (x',y') = (FA.lift π1 π2 ≫ g.app _) (x',y')
    have hf : FA.lift π1 π2 ≫ f.app _ =
      Y.lift (_root_.Prod.fst ≫ f.app _) (_root_.Prod.snd ≫ f.app _) := by
      apply Algebra.hom_ext
      · simp only [Category.assoc, Algebra.lift_fst, ← f.naturality]
        apply Algebra.lift_fst_assoc
      · simp only [Category.assoc, Algebra.lift_snd, ← f.naturality]
        apply Algebra.lift_snd_assoc
    have hg : FA.lift π1 π2 ≫ g.app _ =
      Y.lift (_root_.Prod.fst ≫ g.app _) (_root_.Prod.snd ≫ g.app _) := by
      apply Algebra.hom_ext
      · simp only [Category.assoc, Algebra.lift_fst, ← g.naturality]
        apply Algebra.lift_fst_assoc
      · simp only [Category.assoc, Algebra.lift_snd, ← g.naturality]
        apply Algebra.lift_snd_assoc
    rw [hf, hg]
    let ee : PUnit ⟶ (FA.functor.obj (L.of A) × FA.functor.obj (L.of B)) :=
      fun _ => (x', y')
    suffices
      ee ≫ Y.lift (_root_.Prod.fst ≫ f.app _) (_root_.Prod.snd ≫ f.app _) =
      ee ≫ Y.lift (_root_.Prod.fst ≫ g.app _) (_root_.Prod.snd ≫ g.app _) from
      congr_fun this .unit
    apply Algebra.hom_ext
    · simp only [Category.assoc, Algebra.lift_fst]
      funext
      exact h1
    · simp only [Category.assoc, Algebra.lift_snd]
      funext
      exact h2
  | unit =>
    let FA := L.freeAlgebra X
    let u : FA.functor.obj (𝟙_ _) := Quotient.mk _ .unit
    let e : PUnit ⟶ FA.functor.obj (𝟙_ _) := fun _ => u
    suffices e ≫ f.app _ = e ≫ g.app _ from congr_fun this .unit
    apply Algebra.toUnit_unique

end free

variable (L) in
def freeFunctor : (S → Type u) ⥤ L.Algebra (Type (max v u)) where
  obj X := L.freeAlgebra X
  map f := L.lift _ fun T x => L.incl _ T <| f _ x
  map_id := by
    intro X
    apply L.lift_unique
    intro T x
    rfl
  map_comp := by
    intro X Y Z f g
    apply L.lift_unique
    intro A x
    rfl

def adjunction (L : LawvereTheory.{u} S) :
    L.freeFunctor ⊣ L.algebraForget _ := Adjunction.mkOfHomEquiv {
  homEquiv := fun _ _ => {
    toFun := fun f _ x => f.app _ <| L.incl _ _ x
    invFun := fun f => L.lift _ fun _ x => f _ x
    left_inv := fun _ => L.lift_unique _ _ _ fun _ _ => rfl
    right_inv := fun _ => rfl }
  homEquiv_naturality_left_symm := fun _ _ => L.lift_unique _ _ _ fun _ _ => rfl
  homEquiv_naturality_right := fun _ _ => rfl }

@[simp]
lemma adjunction_homEquiv_apply
  {L : LawvereTheory.{u} S} {X : S → Type u} {Y : L.Algebra (Type u)} (f : L.freeAlgebra X ⟶ Y)  :
  L.adjunction.homEquiv _ _ f = L.inclHom _ ≫ (L.algebraForget _).map f := rfl

@[simp]
lemma adjunction_homEquiv_symm_apply
  {L : LawvereTheory.{u} S} {X : S → Type u} {Y : L.Algebra (Type u)} (f : X ⟶ (L.algebraForget _).obj Y) :
  (L.adjunction.homEquiv _ _).symm f = L.lift _ f := rfl

@[simp]
lemma adjunction_unit_app
  {L : LawvereTheory.{u} S} (X : S → Type u) :
  L.adjunction.unit.app X = L.inclHom _ := rfl

@[simp]
lemma adjunction_counit_app
  {L : LawvereTheory.{u} S} (X : L.Algebra (Type u)) :
  L.adjunction.counit.app X = L.lift _ (𝟙 ((L.algebraForget _).obj X)) := rfl

end LawvereTheory
end CategoryTheory
