import Mathlib.autolabel

namespace AutoLabel.Label

/-- The `t-algebra` label. -/
def algebra : Label where
  dirs := #["Algebra", "FieldTheory", "RingTheory", "GroupTheory", "RepresentationTheory",
            "LinearAlgebra"]

/-- The `t-algebraic-geometry` label. -/
def algebraic_geometry : Label where dirs := #["AlgebraicGeometry", "Geometry/RingedSpace" ]

/-- The `t-analysis` label. -/
def analysis : Label where

/-- The `t-category-theory` label. -/
def category_theory : Label where

/-- The `t-combinatorics` label. -/
def combinatorics : Label where

/-- The `t-computability` label. -/
def computability : Label where

/-- The `t-condensed` label. -/
def condensed : Label where

/-- The `t-data` label. -/
def data : Label where

/-- The `t-differential-geometry` label. -/
def differential_geometry : Label where dirs := #["Geometry/Manifold"]

/-- The `t-dynamics` label. -/
def dynamics : Label where

/-- The `t-euclidean-geometry` label. -/
def euclidean_geometry : Label where dirs := #["Geometry/Euclidean"]

/-- The `t-linter` label. -/
def linter : Label where dirs := #["Tactic/Linter"]

/-- The `t-logic` label. -/
def logic : Label where dirs := #["Logic", "ModelTheory"]

/-- The `t-measure-probability` label. -/
def measure_probability : Label where dirs := #["MeasureTheory", "Probability", "InformationTheory"]

/-- The `t-meta` label. -/
def meta : Label where dirs := #["Tactic", "Lean", "Util", "Mathport", "Control", "Testing"]

/-- The `t-number-theory` label. -/
def number_theory : Label where

/-- The `t-order` label. -/
def order : Label where

/-- The `t-set-theory` label. -/
def set_theory : Label where

/-- The `t-topology` label. -/
def topology : Label where dirs := #["Topology", "AlgebraicTopology"]

add_label algebra dirs: Algebra FieldTheory RingTheory GroupTheory RepresentationTheory LinearAlgebra
add_label algebraic_geometry dirs: AlgebraicGeometry Geometry.RingedSpace
add_label analysis
add_label category_theory
add_label combinatorics
add_label computability
add_label condensed
add_label data
add_label differential_geometry dirs: Geometry.Manifold
add_label dynamics
add_label euclidean_geometry dirs: Geometry.Euclidean
add_label linter dirs: Tactic.Linter
add_label logic dirs: Logic ModelTheory
add_label measure_probability dirs: MeasureTheory Probability InformationTheory
add_label meta dirs: Tactic exclusions: Tactic.Linter
add_label number_theory
add_label order
add_label set_theory
add_label topology dirs: Topology AlgebraicTopology

check_labels

#exit

def gd : String := "SetTheory/Ordinals/Basic.lean"

/-
open Lean Elab Command
run_cmd
  let le := labelsExt.getState (← getEnv)
  let newEnv := labelsExt.addEntry (← getEnv) `algebra
  setEnv newEnv
  let le := labelsExt.getState (← getEnv)
  let gle ← liftCoreM do getLabel `algebra `AutoLabel.Label.algebra
  dbg_trace (gle.name, gle.declName)
  --_
-/

/-- info: #["t-set-theory"] -/
#guard_msgs in
#eval findLabels #[order, set_theory] gd

/-- info: #["t-set-theory", "t-order"] -/
#guard_msgs in
#eval getLabels #[meta, order, set_theory] #["SetTheory/Ordinals/Basic.lean", "Order/Min/Sup.lean"]
def labeling : HashMap String String := HashMap.empty
  |>.insert "Algebra"              "t-algebra"
  |>.insert "FieldTheory"          "t-algebra"
  |>.insert "RingTheory"           "t-algebra"
  |>.insert "GroupTheory"          "t-algebra"
  |>.insert "RepresentationTheory" "t-algebra"
  |>.insert "LinearAlgebra"        "t-algebra"

  |>.insert "AlgebraicGeometry"    "t-algebraic-geometry"
  |>.insert "Geometry/RingedSpace" "t-algebraic-geometry"

  |>.insert "Geometry/Euclidean" "t-euclidean-geometry"

  |>.insert "Geometry/Manifold" "t-differential-geometry"

  |>.insert "Analysis" "t-analysis"

  |>.insert "CategoryTheory" "t-category-theory"

  |>.insert "Combinatorics" "t-combinatorics"

  |>.insert "Computability" "t-computability"

  |>.insert "Condensed" "t-condensed"

  |>.insert "Data" "t-data"

  |>.insert "Dynamics" "t-dynamics"

  |>.insert "Tactic/Linter" "t-linter"

  |>.insert "Logic" "t-logic"
  |>.insert "ModelTheory" "t-logic"

  |>.insert "MeasureTheory" "t-measure-probability"
  |>.insert "Probability" "t-measure-probability"
  |>.insert "InformationTheory" "t-measure-probability"

  |>.insert "Tactic" "t-meta"
  |>.insert "Lean" "t-meta"
  |>.insert "Util" "t-meta"
  |>.insert "Mathport" "t-meta"
  |>.insert "Control" "t-meta"
  |>.insert "Testing" "t-meta"

  |>.insert "NumberTheory" "t-number-theory"

  |>.insert "Order" "t-order"

  |>.insert "Topology" "t-topology"
  |>.insert "AlgebraicTopology" "t-topology"
  |>.insert "SetTheory" "t-set-theory"
