/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
module

public import Plausible.Testable
public meta import Mathlib.Logic.Basic
public import Mathlib.Tactic.Basic
public import Plausible.Gen
public meta import Plausible.Testable

/-!
This module contains `Plausible.Testable` and `Plausible.PrintableProb` instances for mathlib types.
-/

public section

namespace Plausible

namespace Testable

open TestResult

meta instance factTestable {p : Prop} [Testable p] : Testable (Fact p) where
  run cfg min := do
    let h ← runProp p cfg min
    pure <| iff fact_iff h

end Testable

section PrintableProp

meta instance Fact.printableProp {p : Prop} [PrintableProp p] : PrintableProp (Fact p) where
  printProp := printProp p

end PrintableProp

end Plausible
