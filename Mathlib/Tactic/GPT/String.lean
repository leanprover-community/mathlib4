/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
-- TODO move all these

def String.stripPrefix (s p : String) :=
if s.startsWith p then
  s.drop p.length
else
  s

def String.stripSuffix (s p : String) :=
if s.endsWith p then
  s.dropRight p.length
else
  s

def String.partitionLines (p : String → Bool) (s : String) : String × String :=
s.splitOn "\n" |>.partition p |>.map (String.intercalate "\n") (String.intercalate "\n")

def String.count (s : String) (c : Char) : Nat :=
s.foldl (fun n d => if d = c then n + 1 else n) 0
