import Mathlib.Util.FormatTable

open Lean

/--
The `#logAsInfo foo` command logs a message `foo` as info directly.
This circumvents calling repr on strings, meaning instead of `"\\"`,
the message becomes `\`. This makes it easier to use `#guard_msgs` to verify
pure string-producing functions.
-/
macro "#logAsInfo" t:term : command =>
  `(command|#eval (logInfo <| $t : Lean.Elab.Command.CommandElabM Unit))

/--
info:
| first           | second header   | third_header   |
| :-------------- | :-------------: | -------------: |
| item number one |    item two     |         item c |
| the fourth item | the fourth item | escape \| this |
| align left      |  align center   |    align right |
-/
#guard_msgs in
#logAsInfo "\n" ++ formatTable
  #["first","second header","third_header"]
  #[#["item number one","item two", "item c"],
    #["the fourth item","the fourth item", "escape | this"],
    #["align left","align center","align right"]]
  (.some #[.left,.center,.right])
