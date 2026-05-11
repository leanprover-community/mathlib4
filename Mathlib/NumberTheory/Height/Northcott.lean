/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.Order.Northcott

/-!
# Results on the Northcott property for heights

We provide instances showing, assuming a field `K` with a family of admissible absolute values
satisfies the Northcott property for `mulHeight₁`, that `K` also satisfies the Northcott
property
* for `logHeight₁`,
* (TODO) for `Projectivization.mulHeight`,
* (TODO) for `Projectivization.logHeight`.

## TODO

Add instances for heights on projectivizations.
-/

namespace Height

public section

open Real Northcott

variable {K : Type*} [Field K]

/-- A field that satisfies the Northcott property for `mulHeight₁` also does for `logHeight₁`. -/
instance instNorthcottLogHeight₁ [AdmissibleAbsValues K] [Northcott (mulHeight₁ (K := K))] :
    Northcott (logHeight₁ (K := K)) :=
  comp_of_bddAbove mulHeight₁ log fun B ↦ bddAbove_def.mpr ⟨exp B, fun _ ↦ le_exp_of_log_le⟩

end

end Height
