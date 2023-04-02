/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
-- TODO move all these

/-- Extract from a string all lines satisfying a predicate,
along with all lines not satisfying that predicate. -/
def String.partitionLines (p : String → Bool) (s : String) : String × String :=
s.splitOn "\n" |>.partition p |>.map (String.intercalate "\n") (String.intercalate "\n")
