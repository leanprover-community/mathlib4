/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Tactic.Alias

attribute [simp] Array.toArrayAux_eq

alias List.toArray_data := Array.data_toArray

namespace Array
