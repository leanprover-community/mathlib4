import Lean
import Std
import Qq
import Batteries
import Aesop
import ProofWidgets
import Mathlib
import Plausible

/-!
Verify that Mathlib and all its upstream dependencies can be simultaneously imported.

We don't `import Cli` or `import ImportGraph` here as these are only used by scripts,
and may not have been built during CI when we run the tests.
-/
