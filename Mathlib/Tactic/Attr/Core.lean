/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Tactic.Attr.Register
import Batteries.Logic

/-!
# Simp tags for core lemmas

In Lean 4, an attribute declared with `register_simp_attr` cannot be used in the same file. So, we
declare all `simp` attributes used in `Mathlib` in `Mathlib/Tactic/Attr/Register` and tag lemmas
from the core library and the `Batteries` library with these attributes in this file.
-/

attribute [simp] id_map'
attribute [functor_norm, monad_norm] seq_assoc pure_seq pure_bind bind_assoc bind_pure map_pure
attribute [monad_norm] seq_eq_bind_map

-- Porting note: changed some `iff` lemmas to `eq` lemmas
attribute [mfld_simps] id and_true true_and Function.comp_apply and_self eq_self not_false
  true_or or_true heq_eq_eq forall_const and_imp

-- Porting note: until we change the default induction principle on `Nat`:
attribute [ghost_simps] Nat.zero_eq

attribute [nontriviality] eq_iff_true_of_subsingleton
