import Mathlib.Util.InfoTree

open Lean Elab Meta

-- #eval do (← moduleInfoTrees `Mathlib.Data.Subtype).mapM fun t => InfoTree.format t

-- #eval moduleDeclInfoTrees' `Mathlib.Data.Subtype

-- #eval allTacticsInModule' `Mathlib.Data.Subtype
-- /-
-- [(Subtype.prop, []),
--  (Subtype.forall', []),
--  (Subtype.exists', []),
--  (Subtype.ext_iff, []),
--  (Subtype.heq_iff_coe_eq, []),
--  (Subtype.ext_val, []),
--  (Subtype.ext_iff_val, []),
--  (Subtype.coe_mk, []),
--  (Subtype.mk_eq_mk, []),
--  (Subtype.coe_eq_of_eq_mk, []),
--  (Subtype.coe_eq_iff, []),
--  (Subtype.coe_injective, []),
--  (Subtype.val_injective, []),
--  (Subtype.coe_inj, []),
--  (Subtype.val_inj, []),
--  (Subtype.restrict, []),
--  (Subtype.restrict_apply, [((Tactic.tacticRfl "rfl"), rfl), ((Tactic.refl "eq_refl"), eq_refl)]),
--  (Subtype.restrict_def, []),
--  (Subtype.restrict_injective, []),
--  (Subtype.surjective_restrict, [((Std.Tactic.tacticLetI_ "letI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decPred [`p])))), letI := Classical.decPred p), ((Tactic.tacticRefine_lift_
--  "refine_lift"
--  (Std.Tactic.letI
--   "letI"
--   (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decPred [`p])))
--   ";"
--   (Term.syntheticHole "?" (Term.hole "_")))), refine_lift
--   letI := Classical.decPred p;
--   ?_), ((Tactic.focus
--  "focus"
--  (Tactic.tacticSeq
--   (Tactic.tacticSeq1Indented
--    [(Tactic.paren
--      "("
--      (Tactic.tacticSeq
--       (Tactic.tacticSeq1Indented
--        [(Tactic.refine
--          "refine"
--          (Term.noImplicitLambda
--           "no_implicit_lambda%"
--           (Std.Tactic.letI
--            "letI"
--            (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decPred [`p])))
--            ";"
--            (Term.syntheticHole "?" (Term.hole "_")))))
--         ";"
--         (Tactic.rotateRight "rotate_right" [])]))
--      ")")]))), focus
--   (refine
--       no_implicit_lambda%
--         letI := Classical.decPred p;
--         ?_;
--     rotate_right)), ((Tactic.refine
--  "refine"
--  (Term.noImplicitLambda
--   "no_implicit_lambda%"
--   (Std.Tactic.letI
--    "letI"
--    (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decPred [`p])))
--    ";"
--    (Term.syntheticHole "?" (Term.hole "_"))))), refine
--   no_implicit_lambda%
--     letI := Classical.decPred p;
--     ?_), ((Tactic.rotateRight "rotate_right" []), rotate_right), ((Tactic.refine'
--  "refine'"
--  (Term.fun
--   "fun"
--   (Term.basicFun
--    [`f]
--    []
--    "↦"
--    (Term.anonymousCtor
--     "⟨"
--     [(Term.fun
--       "fun"
--       (Term.basicFun
--        [`x]
--        []
--        "↦"
--        (termDepIfThenElse
--         "if"
--         (Lean.binderIdent `h)
--         ":"
--         (Term.app `p [`x])
--         "then"
--         (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")])
--         "else"
--         (Term.app `Nonempty.some [(Term.paren "(" (Term.app `ne [`x]) ")")]))))
--      ","
--      («term_<|_» `funext "<|" (Term.hole "_"))]
--     "⟩")))), refine' fun f ↦ ⟨fun x ↦ if h : p x then f ⟨x, h⟩ else Nonempty.some (ne x), funext <| _⟩), ((Std.Tactic.rintro
--  "rintro"
--  [(Std.Tactic.RCases.rintroPat.one
--    (Std.Tactic.RCases.rcasesPat.tuple
--     "⟨"
--     [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)]) [])
--      ","
--      (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)]) [])]
--     "⟩"))]
--  []), rintro ⟨x, hx⟩), ((Tactic.exact "exact" (Term.app `dif_pos [`hx])), exact dif_pos hx)]),
--  (Subtype.coind_injective, [((Tactic.apply "apply" (Term.app `congr_arg [`Subtype.val `hxy])), apply congr_arg Subtype.val hxy)]),
--  (Subtype.coind_surjective, []),
--  (Subtype.coind_bijective, []),
--  (Subtype.map_comp, []),
--  (Subtype.map_id, []),
--  (Subtype.map_injective, []),
--  (Subtype.map_involutive, []),
--  (Subtype.equiv_iff, []),
--  (Subtype.refl, []),
--  (Subtype.symm, []),
--  (Subtype.trans, []),
--  (Subtype.equivalence, []),
--  (Subtype.val_prop, [])]
-- -/


#eval reflInDecl_format `Mathlib.Data.Subtype `Subtype.restrict_apply
-- [restrict p f x = f ↑x]

-- #eval exactInDecl_format `Mathlib.Data.Subtype `Subtype.surjective_restrict
-- -- [((fun f => restrict p f) (fun x => if h : p x then f { val := x, property := h } else Nonempty.some (_ : Nonempty (β x)))
-- --     { val := x, property := hx } =
-- --   f { val := x, property := hx }, dif_pos hx)]

-- #eval applyInDecl_format `Mathlib.Data.Subtype `Subtype.coind_injective
-- -- [(f x = f y, congr_arg val hxy)]

-- #eval show MetaM _ from do
--   for (goal, tactic) in ← tacticsInDecl_format `Mathlib.Data.Subtype `Subtype.surjective_restrict do
--     IO.println goal
--     IO.println ("· " ++ tactic)
--     IO.println "----"
-- -- α✝ : Sort ?u.6818
-- -- β✝ : Sort ?u.6821
-- -- γ : Sort ?u.6824
-- -- p✝ q : α✝ → Prop
-- -- α : Sort u_1
-- -- β : α → Type u_2
-- -- ne : ∀ (a : α), Nonempty (β a)
-- -- p : α → Prop
-- -- ⊢ Surjective fun f => restrict p f
-- -- · letI := Classical.decPred p
-- -- ----
-- -- α✝ : Sort ?u.6818
-- -- β✝ : Sort ?u.6821
-- -- γ : Sort ?u.6824
-- -- p✝ q : α✝ → Prop
-- -- α : Sort u_1
-- -- β : α → Type u_2
-- -- ne : ∀ (a : α), Nonempty (β a)
-- -- p : α → Prop
-- -- this : DecidablePred p := Classical.decPred p
-- -- ⊢ Surjective fun f => restrict p f
-- -- · refine' fun f ↦ ⟨fun x ↦ if h : p x then f ⟨x, h⟩ else Nonempty.some (ne x), funext <| _⟩
-- -- ----
-- -- α✝ : Sort ?u.6818
-- -- β✝ : Sort ?u.6821
-- -- γ : Sort ?u.6824
-- -- p✝ q : α✝ → Prop
-- -- α : Sort u_1
-- -- β : α → Type u_2
-- -- ne : ∀ (a : α), Nonempty (β a)
-- -- p : α → Prop
-- -- this : DecidablePred p := Classical.decPred p
-- -- f : (x : Subtype p) → β ↑x
-- -- ⊢ ∀ (x : Subtype p),
-- --     (fun f => restrict p f)
-- --         (fun x => if h : p x then f { val := x, property := h } else Nonempty.some (_ : Nonempty (β x))) x =
-- --       f x
-- -- · rintro ⟨x, hx⟩
-- -- ----
-- -- case mk
-- -- α✝ : Sort ?u.6818
-- -- β✝ : Sort ?u.6821
-- -- γ : Sort ?u.6824
-- -- p✝ q : α✝ → Prop
-- -- α : Sort u_1
-- -- β : α → Type u_2
-- -- ne : ∀ (a : α), Nonempty (β a)
-- -- p : α → Prop
-- -- this : DecidablePred p := Classical.decPred p
-- -- f : (x : Subtype p) → β ↑x
-- -- x : α
-- -- hx : p x
-- -- ⊢ (fun f => restrict p f)
-- --       (fun x => if h : p x then f { val := x, property := h } else Nonempty.some (_ : Nonempty (β x)))
-- --       { val := x, property := hx } =
-- --     f { val := x, property := hx }
-- -- · exact dif_pos hx
-- -- ----

-- #eval show MetaM _ from do
--   for (decl, tactics) in ← tacticsInModule_format `Mathlib.Data.Subtype do
--     IO.println "===="
--     IO.println decl
--     for (goal, tactic) in tactics do
--       IO.println goal
      -- IO.println "----"
--       IO.println tactic
--       IO.println "----"

#eval show MetaM _ from do
  for (decl, tactics) in ← tacticsInModule_format `Mathlib.LinearAlgebra.Lagrange do
    IO.println "===="
    IO.println decl
    for (goal, tactic) in tactics do
      IO.println goal
      IO.println "----"
      IO.println tactic
      IO.println "----"

#eval show MetaM _ from do return (← compilationCache.get).toList.map (fun x => x.2.2.2.length)
