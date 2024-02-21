import Mathlib.UniversalAlgebra.LawvereTheory

universe u v

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

inductive LawvereRel {S : Type u} {op : ProdWord S → ProdWord S → Type v}
    (rel : {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop) :
    {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop where
  | of {X Y : ProdWord S} {f g : LawvereWord op X Y} : rel f g → LawvereRel rel f g
  | rfl {X Y : ProdWord S} (f : LawvereWord op X Y) : LawvereRel rel f f
  | symm {X Y : ProdWord S} {f g : LawvereWord op X Y} :
      LawvereRel rel f g → LawvereRel rel g f
  | trans {X Y : ProdWord S} {f g h : LawvereWord op X Y} :
      LawvereRel rel f g → LawvereRel rel g h → LawvereRel rel f h
  | comp_congr {X Y Z : ProdWord S}
      {f f' : LawvereWord op X Y}
      {g g' : LawvereWord op Y Z} :
      LawvereRel rel f f' → LawvereRel rel g g' → LawvereRel rel (f.comp g) (f'.comp g')
  | id_comp {X Y : ProdWord S} (f : LawvereWord op X Y) :
      LawvereRel rel (LawvereWord.id _ |>.comp f) f
  | comp_id {X Y : ProdWord S} (f : LawvereWord op X Y) :
      LawvereRel rel (f.comp <| .id _) f
  | assoc {X Y Z W : ProdWord S}
      (f : LawvereWord op X Y)
      (g : LawvereWord op Y Z)
      (h : LawvereWord op Z W) :
      LawvereRel rel ((f.comp g).comp h) (f.comp (g.comp h))
  | lift_congr
      {T P Q : ProdWord S}
      {f f' : LawvereWord op T P}
      {g g' : LawvereWord op T Q} :
      LawvereRel rel f f' →
      LawvereRel rel g g' →
      LawvereRel rel (.lift f g) (.lift f' g')
  | lift_fst
      {T P Q : ProdWord S}
      (f : LawvereWord op T P)
      (g : LawvereWord op T Q) :
      LawvereRel rel ((LawvereWord.lift f g).comp <| .fst _ _) f
  | lift_snd
      {T P Q : ProdWord S}
      (f : LawvereWord op T P)
      (g : LawvereWord op T Q) :
      LawvereRel rel ((LawvereWord.lift f g).comp <| .snd _ _) g
  | lift_unique
      {T P Q : ProdWord S}
      (f g : LawvereWord op T (P.prod Q)) :
      LawvereRel rel (f.comp <| .fst _ _) (g.comp <| .fst _ _) →
      LawvereRel rel (f.comp <| .snd _ _) (g.comp <| .snd _ _) →
      LawvereRel rel f g
  | toNil_unique {P : ProdWord S} (f g : LawvereWord op P .nil) : LawvereRel rel f g

def LawvereSetoid {S : Type u} {op : ProdWord S → ProdWord S → Type v}
    (rel : {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop)
    (X Y : ProdWord S) :
    Setoid (LawvereWord op X Y) where
  r := LawvereRel rel
  iseqv := ⟨LawvereRel.rfl, LawvereRel.symm, LawvereRel.trans⟩

structure LawverePresentation (S : Type u) where
  hom : ProdWord S → ProdWord S → Type v
  rel : {X Y : ProdWord S} → LawvereWord hom X Y → LawvereWord hom X Y → Prop

namespace LawverePresentation

variable {S : Type*} (P : LawverePresentation S)

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
