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

variable {a b c : Prop}

lemma GCongr.imp_trans (h : a → b) : (b → c) → a → c := fun g ha => g (h ha)

lemma GCongr.imp_right_mono (h : a → b → c) : (a → b) → a → c :=
  fun h' ha => h ha (h' ha)

lemma GCongr.and_right_mono (h : a → b → c) : (a ∧ b) → a ∧ c :=
  fun ⟨ha, hb⟩ => ⟨ha, h ha hb⟩

attribute [gcongr] mt
  Or.imp Or.imp_left Or.imp_right
  And.imp And.imp_left GCongr.and_right_mono
  imp_imp_imp GCongr.imp_trans GCongr.imp_right_mono
  forall_imp Exists.imp
  List.Sublist.append List.Sublist.append_left List.Sublist.append_right
  List.Sublist.reverse List.drop_sublist_drop_left List.Sublist.drop
  List.Perm.append_left List.Perm.append_right List.Perm.append List.Perm.map
