/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Lean.Util.Trace

/-!
# Trace classes for differential geometry elaborators
TODO: add a more complete doc-string
-/
open Lean

initialize registerTraceClass `TotalSpaceMk
initialize registerTraceClass `MDiffElab
