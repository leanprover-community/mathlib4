/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Lean.Util.Trace

/-!
# Trace classes for differential geometry elaborators

This file defines custom trace classes for the differential geometry elaborators in
`Mathlib.Geometry.Manifold.Elaborators.lean`. These need to be in a different file for technical
reasons.

The `TotalSpaceMk` trace class is associated to the `T%` elaborator, which converts a section
of a vector bundle as a dependent function to a non-dependent function into the total space.

The `MDiffElab` trace class corresponds to the elaborators `CMDiff` and friends, and provides
tracing information about inferring a model with corners on the domain (resp. codomain) of the
map in question.
-/
open Lean

initialize registerTraceClass `TotalSpaceMk
initialize registerTraceClass `MDiffElab
