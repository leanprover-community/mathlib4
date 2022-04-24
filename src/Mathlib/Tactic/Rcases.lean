/-!
# Stub for the `rcases` tactic.

The `rcases` tactic has not been implemented yet.
This file contains the syntax definition for `rcases` patterns,
as they are used in several places.

-/

namespace Lean.Parser.Tactic

declare_syntax_cat rcasesPat
syntax rcasesPatMed := sepBy1(rcasesPat, " | ")
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.ignore) "_" : rcasesPat
syntax (name := rcasesPat.clear) "-" : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat

declare_syntax_cat rintroPat
syntax (name := rintroPat.one) rcasesPat : rintroPat
syntax (name := rintroPat.binder) "(" rintroPat+ (" : " term)? ")" : rintroPat

end Lean.Parser.Tactic
