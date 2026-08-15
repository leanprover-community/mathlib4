/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Extensions

/-!
# Dyadic real extension family for the `inclusion` tactic

This file registers the family using dyadic intervals to enclose real expressions.
-/

public meta section

namespace Inclusion

initialize realDyadicFamily : InclusionFamily ← registerInclusionFamily `real.dyadic

end Inclusion
