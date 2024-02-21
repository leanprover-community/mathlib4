import Mathlib.UniversalAlgebra.LawvereTheory

universe u u' v v'

inductive LawvereWord {S : Type u} (op : ProdWord S → ProdWord S → Type v) :
    ProdWord S → ProdWord S → Type (max v u) where
  | of {P T : ProdWord S} (f : op P T) :
      LawvereWord op P T
  | id (P : ProdWord S) :
      LawvereWord op P P
  | comp {P Q R : ProdWord S} :
      LawvereWord op P Q →
      LawvereWord op Q R →
      LawvereWord op P R
  | fst (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) P
  | snd (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) Q
  | lift {T P Q : ProdWord S} :
      LawvereWord op T P →
      LawvereWord op T Q →
      LawvereWord op T (P.prod Q)
  | toNil (P : ProdWord S) :
      LawvereWord op P .nil

/-
open Lean Qq in
instance {S : Type} [ToExpr S] {op : List S → S → Type} [∀ X Y, ToExpr (op X Y)] (X Y) :
    ToExpr (LawvereWord.{0, 0} op X Y) where
  toExpr := aux X Y
  toTypeExpr :=
    mkApp4 (.const ``LawvereWord [0,0]) (toTypeExpr S) _ (toExpr X) (toExpr Y)
where aux := fun
  | _, _, .of f => .app (.const ``LawvereWord.of [0,0]) (toExpr f)
  | _, _, .id P => .app (.const ``LawvereWord.id [0,0]) (toExpr P)
  | _, _, .comp f g => mkApp2 (.const ``LawvereWord.comp [0,0]) (aux _ _ f) (aux _ _ g)
  | _, _, .fst P Q => mkApp2 (.const ``LawvereWord.fst [0,0]) (toExpr P) (toExpr Q)
  | _, _, .snd P Q => mkApp2 (.const ``LawvereWord.snd [0,0]) (toExpr P) (toExpr Q)
  | _, _, .lift f g => mkApp2 (.const ``LawvereWord.lift [0,0]) (aux _ _ f) (aux _ _ g)
  | _, _, .toNil P => .app (.const ``LawvereWord.toNil [0,0]) (toExpr P)
-/

inductive LawvereRel {S : Type u} (op : ProdWord S → ProdWord S → Type v) :
    {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop where
  --| of {X Y : ProdWord S} {f g : LawvereWord op X Y} : rel f g → LawvereRel rel f g
  | rfl {X Y : ProdWord S} (f : LawvereWord op X Y) : LawvereRel op f f
  | symm {X Y : ProdWord S} {f g : LawvereWord op X Y} :
      LawvereRel op f g → LawvereRel op g f
  | trans {X Y : ProdWord S} {f g h : LawvereWord op X Y} :
      LawvereRel op f g → LawvereRel op g h → LawvereRel op f h
  | comp_congr {X Y Z : ProdWord S}
      {f f' : LawvereWord op X Y}
      {g g' : LawvereWord op Y Z} :
      LawvereRel op f f' → LawvereRel op g g' → LawvereRel op (f.comp g) (f'.comp g')
  | id_comp {X Y : ProdWord S} (f : LawvereWord op X Y) :
      LawvereRel op (LawvereWord.id _ |>.comp f) f
  | comp_id {X Y : ProdWord S} (f : LawvereWord op X Y) :
      LawvereRel op (f.comp <| .id _) f
  | assoc {X Y Z W : ProdWord S}
      (f : LawvereWord op X Y)
      (g : LawvereWord op Y Z)
      (h : LawvereWord op Z W) :
      LawvereRel op ((f.comp g).comp h) (f.comp (g.comp h))
  | lift_congr
      {T P Q : ProdWord S}
      {f f' : LawvereWord op T P}
      {g g' : LawvereWord op T Q} :
      LawvereRel op f f' →
      LawvereRel op g g' →
      LawvereRel op (.lift f g) (.lift f' g')
  | lift_fst
      {T P Q : ProdWord S}
      (f : LawvereWord op T P)
      (g : LawvereWord op T Q) :
      LawvereRel op ((LawvereWord.lift f g).comp <| .fst _ _) f
  | lift_snd
      {T P Q : ProdWord S}
      (f : LawvereWord op T P)
      (g : LawvereWord op T Q) :
      LawvereRel op ((LawvereWord.lift f g).comp <| .snd _ _) g
  | lift_unique
      {T P Q : ProdWord S}
      (f g : LawvereWord op T (P.prod Q)) :
      LawvereRel op (f.comp <| .fst _ _) (g.comp <| .fst _ _) →
      LawvereRel op (f.comp <| .snd _ _) (g.comp <| .snd _ _) →
      LawvereRel op f g
  | toNil_unique {P : ProdWord S} (f g : LawvereWord op P .nil) : LawvereRel op f g

def LawvereSetoid {S : Type u} (op : ProdWord S → ProdWord S → Type v)
    --(rel : {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop)
    (X Y : ProdWord S) :
    Setoid (LawvereWord op X Y) where
  r := LawvereRel op
  iseqv := ⟨LawvereRel.rfl, LawvereRel.symm, LawvereRel.trans⟩

def freeLawvereTheory {S : Type u} (op : ProdWord S → ProdWord S → Type v) : LawvereTheory S where
  hom X Y := Quotient <| LawvereSetoid op X Y
  id X := Quotient.mk _ <| LawvereWord.id X
  comp := fun f g => Quotient.liftOn₂ f g
    (fun F G => Quotient.mk _ (F.comp G))
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Quotient.sound <| LawvereRel.comp_congr h₁ h₂)
  id_comp {_ _} := by rintro ⟨f⟩ ; apply Quotient.sound ; apply LawvereRel.id_comp
  comp_id {_ _} := by rintro ⟨f⟩ ; apply Quotient.sound ; apply LawvereRel.comp_id
  assoc {_ _ _ _} := by rintro ⟨f⟩ ⟨g⟩ ⟨h⟩ ; apply Quotient.sound ; apply LawvereRel.assoc
  fst _ _ := Quotient.mk _ <| .fst _ _
  snd _ _ := Quotient.mk _ <| .snd _ _
  lift := fun f g => Quotient.liftOn₂ f g
    (fun F G => Quotient.mk _ <| .lift F G)
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Quotient.sound <| LawvereRel.lift_congr h₁ h₂)
  lift_fst {_ _ _} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.lift_fst
  lift_snd {_ _ _} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.lift_snd
  lift_unique {_ _ _} := by
    rintro ⟨f⟩ ⟨g⟩ hfst hsnd
    apply Quotient.sound
    apply LawvereRel.lift_unique
    · exact Quotient.exact hfst
    · exact Quotient.exact hsnd
  toNil _ := Quotient.mk _ <| .toNil _
  toNil_unique {_} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.toNil_unique

def LawvereWord.liftFun {S : Type u} {S' : Type u'}
    {op : ProdWord S → ProdWord S → Type v}
    {P : LawvereTheory.{v'} S'}
    (obj : ProdWord S → ProdWord S')
    (map : {X Y : ProdWord S} → op X Y → P.hom (obj X) (obj Y))
    (fst : (X Y : ProdWord S) → P.hom (obj <| X.prod Y) (obj X))
    (snd : (X Y : ProdWord S) → P.hom (obj <| X.prod Y) (obj Y))
    (lift : {X Y : ProdWord S} → {T : ProdWord S'} → P.hom T (obj X) → P.hom T (obj Y) → P.hom T (obj <| X.prod Y))
    (toNil : (X : ProdWord S') → P.hom X (obj .nil)) :
    (X Y : ProdWord S) → LawvereWord op X Y → P.hom (obj X) (obj Y)
  | _, _, .of f => map f
  | _, _, .id _ => P.id _
  | _, _, .comp f g => P.comp
      (LawvereWord.liftFun _ @map fst snd lift toNil _ _ f)
      (LawvereWord.liftFun _ @map fst snd lift toNil _ _ g)
  | _, _, .fst _ _ => fst _ _
  | _, _, .snd _ _ => snd _ _
  | _, _, .toNil _ => toNil _
  | _, _, .lift f g => lift
      (LawvereWord.liftFun _ @map fst snd lift toNil _ _ f)
      (LawvereWord.liftFun _ @map fst snd lift toNil _ _ g)

def freeLawvereTheory.lift {S : Type u} {S' : Type u'}
    (op : ProdWord S → ProdWord S → Type v)
    (P : LawvereTheory.{v'} S')
    (obj : ProdWord S → ProdWord S')
    (map : {X Y : ProdWord S} → op X Y → P.hom (obj X) (obj Y))
    (fst : (X Y : ProdWord S) → P.hom (obj <| X.prod Y) (obj X))
    (snd : (X Y : ProdWord S) → P.hom (obj <| X.prod Y) (obj Y))
    (lift : {X Y : ProdWord S} → {T : ProdWord S'} → P.hom T (obj X) → P.hom T (obj Y) → P.hom T (obj <| X.prod Y))
    (toNil : (X : ProdWord S') → P.hom X (obj .nil)) :
    freeLawvereTheory op |>.Morphism P where
  obj := obj
  map {A B} := Quotient.lift (LawvereWord.liftFun obj map fst snd lift toNil _ _) <| by
    intros f g h
    induction h with
    | rfl f => rfl
    | symm _ h => exact h.symm
    | trans _ _ h1 h2 => exact h1.trans h2
    | comp_congr _ _ h1 h2 =>
      show P.comp _ _ = P.comp _ _
      simp [h1,h2]
    | id_comp f =>
      show P.comp (P.id _) _ = _
      simp [P.id_comp]
    | comp_id f =>
      show P.comp _ (P.id _) = _
      simp [P.comp_id]
    | assoc f g h =>
      show P.comp (P.comp _ _) _ = P.comp _ (P.comp _ _)
      simp [P.assoc]
    | lift_congr _ _ h1 h2 =>
      sorry
    | lift_fst f g => sorry
    | lift_snd f g => sorry
    | lift_unique f g _ _ _ _ => sorry
    | toNil_unique f g => sorry
  map_id P := by rfl
  map_comp := sorry
  toNil := toNil
  toNil_unique := sorry
  fst := fst
  snd := snd
  lift := lift
  lift_fst := sorry
  lift_snd := sorry
  lift_unique := sorry

/-
structure LawverePresentation (S : Type u) where
  hom : ProdWord S → ProdWord S → Type v
  rel : {X Y : ProdWord S} → LawvereWord hom X Y → LawvereWord hom X Y → Prop

namespace LawverePresentation

variable {S S' : Type*} (P : LawverePresentation S) (P' : LawverePresentation S')

def lawvereTheory : LawvereTheory S where
  hom X Y := Quotient (LawvereSetoid P.rel X Y)
  id X := Quotient.mk _ <| LawvereWord.id X
  comp := fun f g => Quotient.liftOn₂ f g
    (fun F G => Quotient.mk _ (F.comp G))
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Quotient.sound <| LawvereRel.comp_congr h₁ h₂)
  id_comp {_ _} := by rintro ⟨f⟩ ; apply Quotient.sound ; apply LawvereRel.id_comp
  comp_id {_ _} := by rintro ⟨f⟩ ; apply Quotient.sound ; apply LawvereRel.comp_id
  assoc {_ _ _ _} := by rintro ⟨f⟩ ⟨g⟩ ⟨h⟩ ; apply Quotient.sound ; apply LawvereRel.assoc
  fst _ _ := Quotient.mk _ <| .fst _ _
  snd _ _ := Quotient.mk _ <| .snd _ _
  lift := fun f g => Quotient.liftOn₂ f g
    (fun F G => Quotient.mk _ <| .lift F G)
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Quotient.sound <| LawvereRel.lift_congr h₁ h₂)
  lift_fst {_ _ _} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.lift_fst
  lift_snd {_ _ _} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.lift_snd
  lift_unique {_ _ _} := by
    rintro ⟨f⟩ ⟨g⟩ hfst hsnd
    apply Quotient.sound
    apply LawvereRel.lift_unique
    · exact Quotient.exact hfst
    · exact Quotient.exact hsnd
  toNil _ := Quotient.mk _ <| .toNil _
  toNil_unique {_} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.toNil_unique

end LawverePresentation
-/
