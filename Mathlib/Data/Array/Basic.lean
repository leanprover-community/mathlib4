/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.Alias

-- This file is not imported in Mathlib, and I would like to delete its contents after checking
-- that is unused downstream.
@[deprecated (since := "2024-06-07")] alias List.toArray_data := Array.data_toArray
