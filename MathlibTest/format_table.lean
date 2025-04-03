import Mathlib.Util.FormatTable

/--
info:
| first           | second header   | third \| header |
| :-------------- | :-------------: | --------------: |
| item number one |    item two     |          item c |
| the fourth item | the fourth item |  escape \| this |
| align left      |  align center   |     align right |
-/
#guard_msgs in
run_cmd Lean.logInfo ("\n" ++ formatTable
  #["first", "second header", "third | header"]
  #[#["item number one", "item two", "item c"],
    #["the fourth item", "the fourth item", "escape | this"],
    #["align left", "align center", "align right"]]
  (.some #[.left, .center, .right]))
