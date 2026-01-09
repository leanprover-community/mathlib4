/-
Copyright (c) 2025 Joscha Mennicken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joscha Mennicken
-/
import Lean.Data.Json
open Lean

/-!
# `structure`s for the https://radar.lean-lang.org/ API
-/

namespace RadarAPI

structure JsonMetricComparison where
  metric : String
  first : Option Float
  second : Option Float
  firstSource : Option String
  secondSource : Option String
  unit : Option String
  direction : Int
  -- significance : Option JsonSignificance
deriving ToJson, FromJson

structure JsonCommitComparison where
  significant : Bool
  -- runs : List JsonRunAnalysis
  metrics : List JsonMetricComparison
deriving ToJson, FromJson

/--
Response to `https://radar.lean-lang.org/api/compare/{repo}/{first}/{second}/`.

See also the [radar source code][0].

[0]: https://github.com/leanprover/radar/blob/9df5fb34d2345b41ad2647e52fc91c0c0a6d0bc2/radar/src/main/java/org/leanlang/radar/server/api/ResCompare.java
-/
structure JsonGet where
  chashFirst : Option String
  chashSecond : Option String
  comparison : JsonCommitComparison
deriving ToJson, FromJson

end RadarAPI
