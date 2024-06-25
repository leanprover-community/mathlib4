/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Batteries.Data.Option.Lemmas
import Mathlib.Mathport.Rename

/-!
# Align statements for declarations from Batteries
-/

#align option.mem_iff Option.mem_iff
#align option.some_ne_none Option.some_ne_none
#align option.forall Option.forall
#align option.exists Option.exists
#align option.get_mem Option.get_mem
#align option.get_of_mem Option.get_of_mem
#align option.not_mem_none Option.not_mem_none
#align option.some_get Option.some_get
#align option.get_some Option.get_some
#align option.mem_unique Option.mem_unique
#align option.ext Option.ext
#align option.eq_none_iff_forall_not_mem Option.eq_none_iff_forall_not_mem
#align option.eq_some_iff_get_eq Option.eq_some_iff_get_eq
#align option.ne_none_iff_exists Option.ne_none_iff_exists
#align option.ne_none_iff_exists' Option.ne_none_iff_exists'
#align option.bex_ne_none Option.bex_ne_none
#align option.ball_ne_none Option.ball_ne_none
#align option.bind_some Option.bind_some
#align option.bind_eq_some Option.bind_eq_some
#align option.bind_eq_none Option.bind_eq_none
#align option.bind_comm Option.bind_comm
#align option.bind_assoc Option.bind_assoc
#align option.join_eq_some Option.join_eq_some
#align option.join_ne_none Option.join_ne_none
#align option.join_ne_none' Option.join_ne_none'
#align option.join_eq_none Option.join_eq_none
#align option.bind_id_eq_join Option.bind_id_eq_join
#align option.map_eq_map Option.map_eq_map
#align option.map_none Option.map_none
#align option.map_some Option.map_some
#align option.map_eq_some' Option.map_eq_some'
#align option.map_eq_some Option.map_eq_some
#align option.map_eq_none' Option.map_eq_none'
#align option.map_eq_none Option.map_eq_none
#align option.map_congr Option.map_congr
#align option.map_map Option.map_map
#align option.comp_map Option.comp_map
#align option.map_comp_map Option.map_comp_map
#align option.mem_map_of_mem Option.mem_map_of_mem
#align option.bind_map_comm Option.bind_map_comm
#align option.join_map_eq_map_join Option.join_map_eq_map_join
#align option.join_join Option.join_join
#align option.mem_of_mem_join Option.mem_of_mem_join
#align option.guard_eq_some Option.guard_eq_some
#align option.choice Option.choice
#align option.choice_eq Option.choice_eq
#align option.to_list_some Option.to_list_some
#align option.to_list_none Option.to_list_none
#align option.get_or_else Option.getD
#align option.get_or_else_coe Option.getD_some
#align option.get_or_else_some Option.getD_some
#align option.get_or_else_none Option.getD_none
#align option.get_or_else_of_ne_none Option.getD_of_ne_none
#align option.get_or_else_map Option.getD_map
