import Mathlib.Tactic.FunProp.Attr
import Mathlib.Tactic.FunProp.Core
import Mathlib.Tactic.FunProp.Decl
import Mathlib.Tactic.FunProp.Elab
import Mathlib.Tactic.FunProp.FunctionData
import Mathlib.Tactic.FunProp.Mor
import Mathlib.Tactic.FunProp.RefinedDiscrTree
import Mathlib.Tactic.FunProp.StateList
import Mathlib.Tactic.FunProp.Theorems
import Mathlib.Tactic.FunProp.ToBatteries
import Mathlib.Tactic.FunProp.Types


/-!
# Tactic `fun_prop` for proving function properties like `Continuous f`, `Differentiable ℝ f`, ...

Using `fun_prop` tactic should be as simple as
```lean
example : Continuous (fun x : ℝ => x * sin x) := by fun_prop
```
Mathlib sets up `fun_prop` for many different properties like `Continuous`, `Measurable`,
`Differentiable`, `ContDiff`, etc.

For `At/On/Within`



###


basic setup and using the tactic

### Type of theorems

  - lambda theorems
  - function theorems - compositional form vs simple
  - morphism theorems
  - transition theorems

- checking theorems is correctly recognized

### Dischargning subgoals and `ContinuousAt/On` variants

### Local hypothesis

### Bundled Morphisms

#### Transition theorems

-- the need for transition theorems and how they are used
-- between different properties
-- between different data

### Debugging


### Tactic design
-/
