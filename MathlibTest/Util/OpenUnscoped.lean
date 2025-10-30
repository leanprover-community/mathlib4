import Mathlib.Util.OpenUnscoped

namespace Nat

def pi : Nat := 3
scoped notation "π" => pi

end Nat

section Test1

open unscoped Nat

/-- info: Nat.pi : Nat -/
#guard_msgs in
#check pi

/-- error: Unknown identifier `π` -/
#guard_msgs in
#check π -- error

end Test1
