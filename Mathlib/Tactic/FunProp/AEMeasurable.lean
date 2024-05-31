/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Constructions.Prod.Basic

import Mathlib.Tactic.FunProp.Measurable

/-!
## `fun_prop` minimal setup for AEMeasurable
-/


section missing

open MeasureTheory

variable {ι α β γ δ R : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] {f g : α → β} {μ ν : Measure α}

theorem AEMeasurable.comp_aemeasurable' {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (fun x => g (f x)) μ := comp_aemeasurable hg hf

end missing

open Mathlib

-- mark definition
attribute [fun_prop]
  AEMeasurable

-- lambda rules
attribute [fun_prop]
  aemeasurable_id'
  aemeasurable_const
  AEMeasurable.comp_aemeasurable'
  -- Measurable.comp_aemeasurable'
  -- AEMeasurable_apply -- is this somewhere?
  -- AEMeasurable_pi -- is this somewhere?

-- product
attribute [fun_prop]
  AEMeasurable.prod_mk
  -- AEMeasurable.fst
  -- AEMeasurable.snd

-- algebra
attribute [fun_prop]
  AEMeasurable.add
  AEMeasurable.sub
  AEMeasurable.mul
  AEMeasurable.neg
  AEMeasurable.div
  AEMeasurable.inv
  AEMeasurable.smul

-- transitions
attribute [fun_prop]
  AEMeasurable.mono'
  Measurable.aemeasurable


attribute [fun_prop]
  AEMeasurable.mono'
  Measurable.aemeasurable
