/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

Porting note:
As the parsing framework has completely changed in Lean 4
there is no point porting these files directly.
They can be rewritten from scratch as needed, just as for tactics.
-/

import Mathlib.Init.Align

#align_import data.buffer.basic from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-! # Empty placeholder for Mathlib3's `buffer` -/

#noalign buffer.ext
#noalign buffer.ext_iff
#noalign buffer.size_eq_zero_iff
#noalign buffer.size_nil
#noalign buffer.to_list_nil
#noalign buffer.to_list_append_list
#noalign buffer.append_list_mk_buffer
#noalign buffer.to_buffer_to_list
#noalign buffer.to_list_to_buffer
#noalign buffer.to_list_to_array
#noalign buffer.append_list_nil
#noalign buffer.to_buffer_cons
#noalign buffer.size_push_back
#noalign buffer.size_append_list
#noalign buffer.size_to_buffer
#noalign buffer.length_to_list
#noalign buffer.size_singleton
#noalign buffer.read_push_back_left
#noalign buffer.read_push_back_right
#noalign buffer.read_append_list_left'
#noalign buffer.read_append_list_left
#noalign buffer.read_append_list_right
#noalign buffer.read_to_buffer'
#noalign buffer.read_to_buffer
#noalign buffer.nth_le_to_list'
#noalign buffer.nth_le_to_list
#noalign buffer.read_eq_nth_le_to_list
#noalign buffer.read_singleton
#noalign buffer.list_equiv_buffer
#noalign buffer.read_t
