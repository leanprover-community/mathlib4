/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Lean
import LeanSearchClient.Syntax

/-!
# Lean Search Examples

Examples of using the leansearch API.
The search is triggered when the sentence ends with a full stop (period) or a question mark.

This file is mainly for testing during the PR review. It may be removed later.
-/
section leansearch

/--
warning: Lean search query should end with a full stop (period) or a question mark. Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

/--
warning: Lean search query should end with a full stop (period) or a question mark. Note this command sends your query to an external service at https://leansearch.net/.
-/
#guard_msgs in
example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

set_option leansearch.queries 8

/--
warning: Lean search query should end with a full stop (period) or a question mark. Note this command sends your query to an external service at https://leansearch.net/.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"
  sorry

end leansearch
