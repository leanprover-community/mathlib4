/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace Option

def get {α : Type u} : ∀ {o : Option α}, isSome o → α
| some x, h => x
