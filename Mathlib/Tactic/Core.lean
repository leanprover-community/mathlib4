/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue
-/

import Lean.Expr

namespace Lean.Parser.Tactic

-- syntax simpArg := simpStar <|> simpErase <|> simpLemma
def simpArg := simpStar.binary `orelse (simpErase.binary `orelse simpLemma)

end Lean.Parser.Tactic
