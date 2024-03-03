/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Tactic.Basic

/-!
# `rsuffices` tactic

The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
on the expression, and then `rotate_left`.
-/

-- /--
-- The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
-- of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
-- on the expression, and then `rotate_left`.
-- -/
-- syntax (name := rsuffices) "rsuffices"
--   (ppSpace Std.Tactic.RCases.rcasesPatMed)? (" : " term)? : tactic

-- open Lean.Parser Term in
-- def rsufficesDecl := leading_parser
--   (atomic (group (binderIdent >> " : ")) <|> hygieneInfo) >> termParser >> ppSpace >> showRhs

-- macro_rules
-- | `(tactic| rsuffices $[$pred]? $[: $foo]? $[:= $bar]?) =>
-- `(tactic | (obtain $[$pred]? $[: $foo]? $[:= $bar]?; rotate_left))

-- macro_rules
--   | `(tactic| rsuffices $[$pred]? $[: $foo]? "from" $val; $body)            => `(have%$tk $x : $type := $body; $val)
--   | `(tactic| rsuffices%$tk _%$x          : $type from $val; $body)            => `(have%$tk _%$x : $type := $body; $val)
--   | `(tactic| rsuffices%$tk $hy:hygieneInfo $type from $val; $body)            => `(have%$tk $hy:hygieneInfo : $type := $body; $val)
--   | `(tactic| rsuffices%$tk $x:ident      : $type by%$b $tac:tacticSeq; $body) => `(have%$tk $x : $type := $body; by%$b $tac)
--   | `(tactic| rsuffices%$tk _%$x          : $type by%$b $tac:tacticSeq; $body) => `(have%$tk _%$x : $type := $body; by%$b $tac)
--   | `(tactic| rsuffices%$tk $hy:hygieneInfo $type by%$b $tac:tacticSeq; $body) => `(have%$tk $hy:hygieneInfo : $type := $body; by%$b $tac)


#check Lean.Parser.Tactic.tacticRefine_lift_
-- macro "refine_lift " e:term : tactic =>
-- `(tactic| focus (refine no_implicit_lambda% $e; rotate_right))

-- macro "rsuffices " d:sufficesDecl : tactic => `(tactic| refine_lift suffices $d; ?_)

section
-- namespace Lean.Elab.Term
#check Std.Tactic.RCases.rcasesPatMed
#check Lean.ParserDescr
open Lean.Parser Term
def rsufficesDecl := leading_parser
  (atomic Std.Tactic.RCases.rcasesPatMed) >> termParser >> ppSpace >> showRhs
@[builtin_term_parser] def «rsuffices» := leading_parser:leadPrec
  withPosition ("rsuffices " >> rsufficesDecl) >> optSemicolon termParser

-- end Lean.Elab.Term
end

open Lean in
@[builtin_macro Lean.Parser.Term.rsuffices]
def expandRSuffices : Macro
  | `(rsuffices%$tk $x:ident      : $type from $val; $body)            => `(have%$tk $x : $type := $body; $val)
  | `(rsuffices%$tk _%$x          : $type from $val; $body)            => `(have%$tk _%$x : $type := $body; $val)
  | `(rsuffices%$tk $hy:hygieneInfo $type from $val; $body)            => `(have%$tk $hy:hygieneInfo : $type := $body; $val)
  | `(rsuffices%$tk $x:ident      : $type by%$b $tac:tacticSeq; $body) => `(have%$tk $x : $type := $body; by%$b $tac)
  | `(rsuffices%$tk _%$x          : $type by%$b $tac:tacticSeq; $body) => `(have%$tk _%$x : $type := $body; by%$b $tac)
  | `(rsuffices%$tk $hy:hygieneInfo $type by%$b $tac:tacticSeq; $body) => `(have%$tk $hy:hygieneInfo : $type := $body; by%$b $tac)
  | _                                                                 => Macro.throwUnsupported


macro "rsuffices " d:rsufficesDecl : tactic => `(tactic| refine_lift rsuffices $d; ?_)
