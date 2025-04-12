import Mathlib.Tactic.Linter.DeprecatedModule
import Mathlib.Tactic.Basic

deprecated_module since 2025-04-10

/--
info: Deprecated modules

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DeprecatedModule, Mathlib.Tactic.Basic]
-/
#guard_msgs in
#show_deprecated_modules

-- Deprecating the current module twice is a no-op (hence makes no sense).
deprecated_module since 2025-02-31

/--
info: Deprecated modules

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DeprecatedModule, Mathlib.Tactic.Basic]
-/
#guard_msgs in
#show_deprecated_modules
