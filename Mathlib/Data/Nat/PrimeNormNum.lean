/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

/-!
# Primality prover

This file provides a `norm_num` extension to prove that natural numbers are prime.

Porting note: the sole purpose of this file is to mark it as "ported".
This file seems to be tripping up the porting dashboard.

-/
