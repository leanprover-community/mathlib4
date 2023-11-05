/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Mario Carneiro
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Logic
import Mathlib.Tactic.Relation.Symm
import Mathlib.Tactic.Relation.Trans

/-!
# Realignments from lean 3 `init`

These are collected in one place only for ease of maintenance of a bunch of files that would
otherwise be nothing but `#align`s. Please use the respective files in `Mathlib.Init` if there are
actual theorems in the files.
-/

-- Implementation detail
set_option align.precheck false in #align _sorry_placeholder_ _sorry_placeholder_

/-! ## `init.algebra.classes` -/

/-! ## `init.cc_lemmas` -/

/-! ## `init.classical` -/


/-! ## `init.coe` -/





/-! ## `init.control.alternative` -/

/-! ## `init.control.applicative` -/


/-! ## `init.control.except` -/


/-! ## `init.control.functor` -/

/-! ## `init.control.lift` -/

/-! ## `init.control.monad` -/


/-! ## `init.data.array.default` -/

-- These are TODOs, but we need to avoid aligning to `Array` which is significantly different
set_option align.precheck false in #align array Array'
set_option align.precheck false in #align mk_array mkArray'

/-! ## `init.data.char.basic` -/

/-! ## `init.data.char.classes` -/

/-! ## `init.data.char.default` -/

/-! ## `init.data.default` -/

/-! ## `init.data.fin.basic` -/


/-! ## `init.data.int.comp_lemmas` -/

/-! ## `init.data.int.default` -/

/-! ## `init.data.list.basic` -/


/-! ## `init.data.nat.basic` -/


/-! ## `init.data.nat.div` -/

/-! ## `init.data.nat.lemmas` -/

#noalign nat.discriminate

/-! ## `init.data.option.instances` -/


/-! ## `init.data.ordering.basic` -/

/-! ## `init.data.prod` -/

/-! ## `init.data.punit` -/


/-! ## `init.data.quot` -/

/-! ## `init.data.random` -/


/-! ## `init.data.repr` -/

set_option align.precheck false in #align nat.to_digits Nat.toDigits'

/-! ## `init.data.setoid` -/

attribute [refl] Setoid.refl
attribute [symm] Setoid.symm
attribute [trans] Setoid.trans

/-! ## `init.data.sigma.basic` -/

/-! ## `init.data.string.basic` -/

/-! ## `init.data.subtype.basic` -/

/-! ## `init.data.sum.basic` -/

/-! ## `init.data.sum.default` -/

/-! ## `init.data.to_string` -/


/-! ## `init.data.unsigned.basic` -/

/-! ## `init.data.unsigned.default` -/

/-! ## `init.default` -/

/-! ## `init.function` -/

/-! ## `init.funext` -/

/-! ## `init.meta.exceptional` -/

/-! ## `init.meta.feature_search` -/

/-! ## `init.meta.float` -/

/-! ## `init.meta.format` -/

/-! ## `init.meta.json` -/

/-! ## `init.meta.level` -/

/-! ## `init.meta.name` -/


/-! ## `init.meta.options` -/

/-! ## `init.meta.rb_map` -/

/-! ## `init.meta.task` -/

/-! ## `init.meta.widget.basic` -/

/-! ## `init.meta.widget.default` -/

/-! ## `init.meta.widget.html_cmd` -/

/-! ## `init.meta.widget.interactive_expr` -/

/-! ## `init.meta.widget.replace_save_info` -/

/-! ## `init.meta.widget.tactic_component` -/

/-! ## `init.prelude` -/





/-! ## `init.propext` -/

/-! ## `init.util` -/

/-! ## `init.version` -/

/-! ## `init.wf` -/
