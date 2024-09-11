/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Lean
import LeanSearchClient.Basic

/-!
# Lean Search Examples

Examples of using the leansearch API. The search is triggered when the sentence ends with a full stop (period) or a question mark.

This file is mainly for testing during the PR review. It may be removed later.
-/

#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"

set_option leansearch.queries 8

example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m"
  sorry
