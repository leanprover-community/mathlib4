
/-!
# Aesop rule set for finsets

This file defines `finsetNonempty`, an aesop rule set to prove that a given finset is nonempty.
-/

public section

-- `finsetNonempty` rules try to prove that a given finset is nonempty,
-- for use in positivity extensions.
declare_aesop_rule_sets [finsetNonempty] (default := true)
