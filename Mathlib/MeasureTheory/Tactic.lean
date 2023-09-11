/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
! This file was ported from Lean 3 source module measure_theory.tactic
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Measurability

/-!
# Tactics for measure theory

Currently we have one domain-specific tactic for topology: `measurability`.
It is implemented in `Mathlib.Tactic.Measurability`.

Porting note: the sole purpose of this file is to mark it as "ported".
This file seems to be tripping up the porting dashboard.

-/
