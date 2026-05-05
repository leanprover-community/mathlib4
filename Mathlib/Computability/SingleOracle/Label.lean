import Lean.LabelAttribute
import Lean
register_label_attr cp
register_simp_attr evp_simps
register_simp_attr ev_simps

open Lean

macro "apply_cp":tactic =>
  `(tactic|
    apply_rules
      (config := { maxDepth := 30
                 , symm := false
                 , exfalso := false
                 , transparency := .reducible })
      only [*] using $(mkIdent `cp)
  )

macro "apply_cp" n:num:tactic =>
  `(tactic|
    apply_rules
      (config := { maxDepth := $n
                 , symm := false
                 , exfalso := false
                 , transparency := .reducible })
      only [*] using $(mkIdent `cp)
  )
