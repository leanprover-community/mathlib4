import Mathlib

theorem a : True := .intro
--#print IsCyclotomicExtension.Rat.five_pid

theorem IsCyclotomicExtension.Rat.five_pid' (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {5} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  IsCyclotomicExtension.Rat.five_pid K

theorem IsCyclotomicExtension.Rat.five_pid'' (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {5} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  IsCyclotomicExtension.Rat.five_pid' K

open Lean
#eval show CoreM _ from do
  dbg_trace (Tips.tips (← getEnv)).toList
