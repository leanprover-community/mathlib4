import Mathlib.Tactic.Autolabels.EnvExtension

add_label algebra dirs: Algebra Data.Algebra
add_label analysis
add_label linter dirs: Tactic.Linter
add_label meta dirs: Tactic exclusions: Tactic.Linter

/--
info: label: t-algebra
dirs: [Mathlib/Algebra/, Mathlib/Data/Algebra/]
exclusions: []
---
info: label: t-analysis
dirs: [Mathlib/Analysis/]
exclusions: []
---
info: label: t-linter
dirs: [Mathlib/Tactic/Linter/]
exclusions: []
---
info: label: t-meta
dirs: [Mathlib/Tactic/]
exclusions: [Mathlib/Tactic/Linter/]
-/
#guard_msgs in
check_labels "t-"

/--
info: label: t-meta
dirs: [Mathlib/Tactic/]
exclusions: [Mathlib/Tactic/Linter/]
-/
#guard_msgs in
check_labels "t-met"

/-- info: No applicable label. -/
#guard_msgs in
-- non-existing label
produce_labels "Mathlib/SetTheory/Ordinals/Basic.lean"

/-- info: Applicable labels: t-algebra -/
#guard_msgs in
produce_labels "Mathlib/Algebra/Ordinals/Basic.lean"

/-- info: Applicable labels: t-algebra -/
#guard_msgs in
produce_labels "Mathlib/Data/Algebra/Defs.lean"

/-- info: Applicable labels: t-algebra -/
#guard_msgs in
produce_labels "Mathlib/Algebra/Ordinals/Basic.lean
Mathlib/Data/Algebra/Defs.lean"

/-- info: Applicable labels: t-linter,t-meta -/
#guard_msgs in
-- both `dirs` paths get found, even with `exclusions`
produce_labels "Mathlib/Tactic/Linarith/Basic.lean
Mathlib/Tactic/Linter/Basic.lean"

/-- info: Applicable labels: t-linter -/
#guard_msgs in
-- find only `linter`
produce_labels "Mathlib/Tactic/Linter/Basic.lean"


/-- info: Applicable labels: t-meta -/
#guard_msgs in
-- find only `meta`
produce_labels "Mathlib/Tactic/Linarith/Basic.lean"
