@[deprecated (since := "2025-09-01")] example : True := trivial

example := 0

-- A comment for a result that should disappear
set_option pp.all true in
open Nat in
variable {j : Int} in
@[deprecated Nat (since := "2025-08-01")] example : True := trivial

-- A comment for `example := 1`
example := 1

-- A comment for `I_should_be_kept`
@[deprecated (since := "2025-07-01")] theorem I_should_be_kept : True := trivial

@[deprecated (since := "2025-07-01")] example : True := trivial
