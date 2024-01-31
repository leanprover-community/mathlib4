import Mathlib.UniversalAlgebra.LawvereTheory

structure FiniteLawverePresentation where
  numSort : ℕ
  sortName (S : Fin numSort) :
    String := s!"X_{S}"
  numOps (P : List (Fin numSort)) (Q : Fin numSort) :
    ℕ
  opName (P : List (Fin numSort)) (S : Fin numSort) (op : Fin (numOps P S)) :
    String := s!"op_{op}"
  rels {P Q : ProdWord (Fin numSort)} :
    List (String × LawvereWord (fun a b => Fin (numOps a.unpack b)) P Q ×
      LawvereWord (fun a b => Fin (numOps a.unpack b)) P Q)

namespace FiniteLawverePresentation

variable (P : FiniteLawverePresentation)

def lawvereTheory : LawvereTheory where
  S := Fin P.numSort
  hom X Y := Quotient (LawvereSetoid (fun f g => ∃ n, (n, f, g) ∈ P.rels) X Y)
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

/-
syntax sort := str
syntax op := (str ":" sort) <|> (str ":" sepBy1(sort,"→") "→" sort)
syntax rel := term

syntax "`[FLP|"
  ("SORTS:\n" sepBy(sort, ";"))
  ("OPS:\n" sepBy(op, ";"))
  ("RELS:\n" sepBy(rel,";"))
  "]" : term
-/

end FiniteLawverePresentation
