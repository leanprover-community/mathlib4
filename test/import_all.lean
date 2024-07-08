import Lean
import Std
import Qq
import Batteries
import Aesop
import ProofWidgets
import ImportGraph
import Mathlib

/-!
Verify that Mathlib and all its upstream dependencies can be simultaneously imported.

We don't `import Cli` here as that is only used by scripts,
and it need to have been built during CI when we run the tests.
-/
