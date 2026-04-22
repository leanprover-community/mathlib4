import Mathlib.Tactic.StacksAttribute
import Mathlib.Util.ParseCommand

/-- info: No tags found. -/
#guard_msgs in
#zbmath_concepts

namespace X

@[zbmath "my concept"]
theorem tagged : True := .intro

@[zbmath "another concept" "with a comment"]
theorem tagged' : True := .intro

end X

/--
info:
ZBMath concept "another concept" corresponds to declaration 'X.tagged''. (with a comment)
ZBMath concept "my concept" corresponds to declaration 'X.tagged'.
-/
#guard_msgs in
#zbmath_concepts

@[zbmath "concept1", zbmath "another concept"]
theorem twice : True := .intro

/--
info:
ZBMath concept "another concept" corresponds to declaration 'X.tagged''. (with a comment)
ZBMath concept "another concept" corresponds to declaration 'twice'.
ZBMath concept "concept1" corresponds to declaration 'twice'.
ZBMath concept "my concept" corresponds to declaration 'X.tagged'.
-/
#guard_msgs in
#zbmath_concepts
