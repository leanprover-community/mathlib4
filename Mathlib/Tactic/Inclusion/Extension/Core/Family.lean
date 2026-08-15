/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Extensions

/-!
# Core extension family for the `inclusion` tactic

This file registers the extension family containing rules that are independent of the represented
set implementation.
-/

public meta section

namespace Inclusion

initialize coreFamily : InclusionFamily ← registerInclusionFamily `core

end Inclusion
