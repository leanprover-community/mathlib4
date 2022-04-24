/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Attributes

namespace Lean.Attr

initialize reflAttr : TagAttribute ← registerTagAttribute `refl "reflexive relation"
initialize symmAttr : TagAttribute ← registerTagAttribute `symm "symmetric relation"
initialize transAttr : TagAttribute ← registerTagAttribute `trans "transitive relation"
initialize substAttr : TagAttribute ← registerTagAttribute `subst "substitution"

initialize hintTacticAttr : TagAttribute ←
  registerTagAttribute `hintTactic "A tactic that should be tried by `hint`."
