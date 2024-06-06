/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.Json
open Lean

/-!
# `structure`s for the http://speed.lean-fro.org/ API
-/

namespace SpeedCenterAPI

structure CommitSource where
  repo_id : String
  hash : String
deriving ToJson, FromJson

structure Source where
  source : CommitSource
deriving ToJson, FromJson

structure Dimension where
  benchmark : String
  metric : String
  unit : String
deriving ToJson, FromJson

structure Measurement where
  dimension : Dimension
  value : Float
deriving ToJson, FromJson

structure Result where
  measurements : List Measurement
deriving ToJson, FromJson

structure Run where
  id : String
  source : Source
  result : Result
deriving ToJson, FromJson

/-- The top-level API response for `http://speed.lean-fro.org/{repo}/api/run/{guid}?hash={sha}`. -/
structure RunResponse where
  run : Run
deriving ToJson, FromJson

/-- The error response-/
structure ErrorMessage where
  repo_id : String
  message : String
  commit_hash : String
deriving ToJson, FromJson

end SpeedCenterAPI
