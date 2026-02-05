/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Thomas R. Murrills
-/
module

public import Lean.Message

public section

namespace Lean.MessageData

/-- Renders an expression `Foo` as an instance binder `[]`, taking care to group and nest
appropriately. This is mostly a synonym for `MessageData.sbracket` for discoverability. -/
def ofInstanceBinderType (e : Expr) : MessageData := m!"{e}".sbracket

end Lean.MessageData
