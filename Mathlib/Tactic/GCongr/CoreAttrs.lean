/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Tactic.GCongr.Core

/-!
# gcongr attributes for lemmas up in the import chain

In this file we add `gcongr` attribute to lemmas in `Lean.Init`.
We may add lemmas from other files imported by `Mathlib/Tactic/GCongr/Core` later.
-/

-- `imp_trans` doesn't exist in lean core??
lemma imp_trans {a b c : Prop} (h : a → b) : (b → c) → a → c := fun g ha => g (h ha)

lemma imp_trans' {a b c : Prop} (h : b → c) : (a → b) → a → c := fun g ha => h (g ha)

attribute [gcongr] mt
  Or.imp Or.imp_left Or.imp_right
  And.imp And.imp_left And.imp_right
  imp_imp_imp imp_trans imp_trans'
  forall_imp Exists.imp
  Nat.succ_le_succ
  List.Sublist.append List.Sublist.append_left List.Sublist.append_right
  List.Sublist.reverse List.drop_sublist_drop_left List.Sublist.drop
  List.Perm.append_left List.Perm.append_right List.Perm.append List.Perm.map
