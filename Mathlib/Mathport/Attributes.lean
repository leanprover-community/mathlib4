/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Attributes

namespace Lean.Attr

initialize substAttr : TagAttribute ← registerTagAttribute `subst "substitution"
