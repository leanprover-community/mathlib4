import Mathlib.UniversalAlgebra.LawvereTheory

structure FiniteLawverePresentation where
  sortNames : Array String
  opNames (P : Array (Fin sortNames.size)) (Q : Fin sortNames.size) :
    Array String
  rels {P Q : ProdWord (Fin sortNames.size)} :
    List (String × LawvereWord (fun a b => Fin ((opNames a.unpack b).size)) P Q ×
      LawvereWord (fun a b => Fin ((opNames a.unpack b).size)) P Q)

syntax sortName := str
syntax sortDescr := sortName ";"
syntax opName := str
syntax opDescr := opName ":" sepBy(sortName,",") " → " sortName

syntax (name := flpStx) "`[FLP|"
  ("SORTS:" sepBy(sortName,","))?
  ("OPS:" sepBy(opDescr,","))?
"]" : term

open Qq Lean Elab Term

def elabSortName (nm : TSyntax `sortName) : TermElabM String :=
  match nm with
  | `(sortName|$s:str) => return s.getString
  | _ => throwUnsupportedSyntax

def elabOpName (nm : TSyntax `opName) : TermElabM String :=
  match nm with
  | `(opName|$s:str) => return s.getString
  | _ => throwUnsupportedSyntax

def elabOpDescr (descr : TSyntax `opDescr) : TermElabM (String × Array String × String) :=
  match descr with
  | `(opDescr|$nm : $nms,* → $out) => do
    let nm ← elabOpName nm
    let nms ← nms.getElems.mapM elabSortName
    let out ← elabSortName out
    return (nm, nms, out)
  | _ => throwUnsupportedSyntax

@[term_elab flpStx]
def elabFlp : TermElab := fun stx tp =>
  match stx with
  | `(`[FLP| $[SORTS: $sorts,*]? $[OPS: $ops,*]?]) => do
    let sorts ← match sorts with
      | some sorts => sorts.getElems.mapM elabSortName
      | none => pure #[]
    let ops ← match ops with
      | some ops => ops.getElems.mapM elabOpDescr
      | none => pure #[]
    logInfo m!"{sorts}"
    logInfo m!"{ops}"
    return q(0)
  | _ => throwUnsupportedSyntax

#check `[FLP|
  SORTS:
    "a" ,
    "b"
  OPS:
    "a" : "a", "b" → "c",
    "a" : "b" → "c"
]

namespace FiniteLawverePresentation

variable (P : FiniteLawverePresentation)

/-
def lawvereTheory : LawvereTheory (Fin P.numSort) where
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
-/

end FiniteLawverePresentation
