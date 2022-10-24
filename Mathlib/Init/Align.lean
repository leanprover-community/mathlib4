/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Mario Carneiro
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Logic

/-!
# Realignments from lean 3 `init`

These are collected in one place only for ease of maintenance of a bunch of files that would
otherwise be nothing but `#align`s. Please use the respective files in `Mathlib.Init` if there are
actual theorems in the files.
-/

-- Implementation detail
#align _sorry_placeholder_ _sorry_placeholder_

/-! ## `init.algebra.classes` -/

/-! ## `init.algebra.order` -/

#align preorder.to_has_le Preorder.toLE
#align preorder.to_has_lt Preorder.toLT

/-! ## `init.cc_lemmas` -/

/-! ## `init.classical` -/

#align classical.some Classical.choose
#align classical.some_spec Classical.choose_spec

/-! ## `init.coe` -/

#align has_coe Coe
#align has_coe.coe Coe.coe

#align has_coe_t CoeTCₓ -- universe level mismatch
#align has_coe_t.coe CoeTCₓ.coe

#align has_coe_to_fun CoeFun
#align has_coe_to_fun.coe CoeFun.coe

#align has_coe_to_sort CoeSort
#align has_coe_to_sort.coe CoeSort.coe

#align coe_trans coeTransₓ
#align coe_base coeBaseₓ

/-! ## `init.control.alternative` -/

/-! ## `init.control.applicative` -/

#align has_pure Pure
#align has_seq Seq
#align has_seq_left SeqLeft
#align has_seq_right SeqRight

/-! ## `init.control.except` -/

#align except.map Except.mapₓ
#align except.map_error Except.mapErrorₓ
#align except.bind Except.bindₓ

/-! ## `init.control.functor` -/

/-! ## `init.control.lawful` -/

#align is_lawful_applicative LawfulApplicative
#align is_lawful_monad LawfulMonad

/-! ## `init.control.lift` -/

/-! ## `init.control.monad` -/

#align has_bind Bind

/-! ## `init.data.array.default` -/

#align array Array'
#align mk_array mkArray'

/-! ## `init.data.bool.basic` -/

#align bor or
#align band and
#align bnot not
#align bxor xor

/-! ## `init.data.char.basic` -/

/-! ## `init.data.char.classes` -/

/-! ## `init.data.char.default` -/

/-! ## `init.data.default` -/

/-! ## `init.data.fin.basic` -/

#align fin.elim0 Fin.elim0ₓ

/-! ## `init.data.int.basic` -/

-- TODO: backport?
#align int.neg_succ_of_nat Int.negSucc

/-! ## `init.data.int.order` -/

#align int.nonneg Int.NonNeg
#align int.le Int.le
#align int.lt Int.lt

/-! ## `init.data.int.comp_lemmas` -/

/-! ## `init.data.int.default` -/

/-! ## `init.data.list.basic` -/

#align list.erase List.erase'
#align list.bag_inter List.bagInter'
#align list.diff List.diff'
#align list.head List.head'
#align list.filter List.filter'
#align list.partition List.partition'
#align list.drop_while List.dropWhile'
#align list.after List.after'
#align list.span List.span'
#align list.index_of List.indexOf'
#align list.remove_all List.removeAll'
#align list.is_prefix_of List.isPrefixOf'
#align list.is_suffix_of List.isSuffixOf'
#align list.lt List.lt

/-! ## `init.data.nat.basic` -/

#align nat.nat_zero_eq_zero Nat.zero_eq
#align nat.less_than_or_equal Nat.le
#align nat.le Nat.le
#align nat.lt Nat.lt
#align nat.repeat Nat.repeat'

/-! ## `init.data.nat.div` -/

/-! ## `init.data.nat.lemmas` -/

#align nat.le_of_add_le_add_right Nat.le_of_add_le_add_rightₓ
#align nat.mul_lt_mul Nat.mul_lt_mulₓ
#align nat.mul_lt_mul' Nat.mul_lt_mul'ₓ
#align nat.discriminate Nat.discriminateₓ
#align nat.sub_one_sub_lt Nat.sub_one_sub_ltₓ
#align nat.div_eq_sub_div Nat.div_eq_sub_divₓ
#align nat.div_eq_of_eq_mul_left Nat.div_eq_of_eq_mul_leftₓ
#align nat.div_eq_of_eq_mul_right Nat.div_eq_of_eq_mul_rightₓ
#align nat.div_eq_of_lt_le Nat.div_eq_of_lt_leₓ
#align nat.mul_div_cancel' Nat.mul_div_cancel'ₓ
#align nat.div_mul_cancel Nat.div_mul_cancelₓ
#align nat.mul_div_assoc Nat.mul_div_assocₓ
#align nat.dvd_of_mul_dvd_mul_left Nat.dvd_of_mul_dvd_mul_leftₓ
#align nat.dvd_of_mul_dvd_mul_right Nat.dvd_of_mul_dvd_mul_rightₓ

/-! ## `init.data.option.instances` -/

#align option.eq_none_of_is_none Option.eq_none_of_isNone
#align option.eq_some_of_is_some Option.eq_some_of_isSome

/-! ## `init.data.ordering.basic` -/

/-! ## `init.data.prod` -/

/-! ## `init.data.punit` -/

#align punit_eq PUnit.subsingleton
#align punit_eq_star PUnit.eq_punit

/-! ## `init.data.quot` -/

/-! ## `init.data.repr` -/

#align has_repr Repr
#align nat.to_digits Nat.toDigits'

/-! ## `init.data.setoid` -/

-- attribute [refl] Setoid.refl
-- attribute [symm] Setoid.symm
-- attribute [trans] Setoid.trans

/-! ## `init.data.sigma.basic` -/

/-! ## `init.data.string.basic` -/

/-! ## `init.data.subtype.basic` -/

/-! ## `init.data.sum.basic` -/

/-! ## `init.data.sum.default` -/

/-! ## `init.data.to_string` -/

#align has_to_string ToString

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

#align auto_param autoParam'

/-! ## `init.meta.options` -/

/-! ## `init.meta.rb_map` -/

/-! ## `init.meta.task` -/

/-! ## `init.meta.widget.basic` -/

/-! ## `init.meta.widget.default` -/

/-! ## `init.meta.widget.html_cmd` -/

/-! ## `init.meta.widget.interactive_expr` -/

/-! ## `init.meta.widget.replace_save_info` -/

/-! ## `init.meta.widget.tactic_component` -/

/-! ## `init.propext` -/

/-! ## `init.util` -/

/-! ## `init.version` -/

/-! ## `init.wf` -/

#align subrelation.accessible Subrelation.accessibleₓ
#align inv_image.accessible InvImage.accessibleₓ
