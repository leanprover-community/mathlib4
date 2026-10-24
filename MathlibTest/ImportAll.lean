module

public import Aesop
public import Batteries
public import Lean
public import Mathlib
public import Plausible
public import ProofWidgets
public import Qq
public import Std

/-!
Verify that Mathlib and all its upstream dependencies can be simultaneously imported.

We don't `import Cli` or `import ImportGraph` here as these are only used by scripts,
and may not have been built during CI when we run the tests.
-/
