import Mathlib.UniversalAlgebra.LawvereTheory

universe u v

structure LawverePresentation where
  S : Type u
  hom : ProdWord S → S → Type v
  rel : {X Y : ProdWord S} → LawvereWord hom X Y → LawvereWord hom X Y → Prop

namespace LawverePresentation

variable (P : LawverePresentation)

def lawvereTheory : LawvereTheory where
  S := P.S
  hom X Y := Quotient (LawvereSetoid P.rel X Y)
  id X := Quotient.mk _ <| LawvereWord.id X
  comp := fun f g => Quotient.liftOn₂ f g
    (fun F G => Quotient.mk _ (F.comp G))
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Quotient.sound <| LawvereRel.comp_congr h₁ h₂)
  id_comp {_ _} := by rintro ⟨f⟩ ; apply Quotient.sound ; apply LawvereRel.id_comp
  comp_id {_ _} := by rintro ⟨f⟩ ; apply Quotient.sound ; apply LawvereRel.comp_id
  assoc {_ _ _ _} := by rintro ⟨f⟩ ⟨g⟩ ⟨h⟩ ; apply Quotient.sound ; apply LawvereRel.assoc
  fst' _ _ := Quotient.mk _ <| .fst _ _
  snd' _ _ := Quotient.mk _ <| .snd _ _
  lift' := fun f g => Quotient.liftOn₂ f g
    (fun F G => Quotient.mk _ <| .lift F G)
    (fun a₁ a₂ b₁ b₂ h₁ h₂ => Quotient.sound <| LawvereRel.lift_congr h₁ h₂)
  lift'_fst' {_ _ _} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.lift_fst
  lift'_snd' {_ _ _} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.lift_snd
  lift'_unique {_ _ _} := by
    rintro ⟨f⟩ ⟨g⟩ hfst hsnd
    apply Quotient.sound
    apply LawvereRel.lift_unique
    · exact Quotient.exact hfst
    · exact Quotient.exact hsnd
  toNil' _ := Quotient.mk _ <| .toNil _
  toNil'_unique {_} := by rintro ⟨f⟩ ⟨g⟩ ; apply Quotient.sound ; apply LawvereRel.toNil_unique

def lift
    {L : LawvereTheory}
    (obj : P.S → ProdWord L.S)
    (map : {X : ProdWord P.S} → {Y : P.S} → P.hom X Y →
      L.hom (ProdWord.recOn X obj (fun _ _ => .prod) .nil) (obj Y)) :
    P.lawvereTheory.Morphism L where
  obj X := .mk <| X.as.recOn obj (fun _ _ => .prod) .nil
  map := _
  map_id := _
  map_comp := _
  toNil := _
  toNil_unique := _
  fst := _
  snd := _
  lift := _
  lift_fst := _
  lift_snd := _
  lift_unique := _

end LawverePresentation
