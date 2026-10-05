/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

import Mathlib.Init
meta import Mathlib.Init


   public meta   import Mathlib.Init

public import Mathlib.Init
import Lean.Elab.Command

/--
warning: Imports can be reformatted:
  i̵m̵p̵o̵r̵t̵ ̵M̵a̵t̵h̵l̵i̵b̵.̵I̵n̵i̵t̵p̲u̲b̲l̲i̲c̲ meta import Mathlib.Init
  public i̲m̲p̲o̲r̲t̲ ̲M̲a̲t̲h̲l̲i̲b̲.̲I̲n̲i̲t̲
  ̲
  ̲meta  ̵ ̵import Mathlib.Init
  p̵u̵b̵l̵i̵c̵ ̵import Mathlib.Init
  import Lean.Elab.Command
-/
#guard_msgs in
set_option linter.style.header true in
/-! -/
