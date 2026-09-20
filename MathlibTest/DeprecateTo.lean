import Mathlib.Tactic.DeprecateTo
import Mathlib.Tactic.ToAdditive

set_option linter.translateRedundant false in
-- TODO: fix weird trailing whitespace between original theorem and deprecated aliases
/--
info: * Pairings:
#[(new_name_mul, mul_easy_deprecated), (new_name_add, add_easy_deprecated)]

Try this:

  [apply] /-- I also have a doc-string -/
  @[to_additive /-- With its additive doc-string -/]
  theorem new_name_mul : True := .intro
  ⏎
  ⏎
  ⏎
  @[deprecated (since := "YYYY-MM-DD")]
  alias mul_easy_deprecated := new_name_mul
  ⏎
  @[deprecated (since := "YYYY-MM-DD")]
  alias add_easy_deprecated := new_name_add
-/
#guard_msgs (whitespace := exact) in
deprecate to new_name_mul new_name_add "YYYY-MM-DD"
/-- I also have a doc-string -/
@[to_additive /-- With its additive doc-string -/]
theorem mul_easy_deprecated : True := .intro

/--
info: * Pairings:
#[(add_even_theorem, add_odd_theorem)]

Try this:

  [apply] theorem add_even_theorem {n m : Nat} (hn : ∃ k, n = k + k) (hm : ∃ k, m = k + k) :
      ∃ k, n + m = k + k := by
    obtain ⟨n, rfl⟩ := /- have a comment here (to test preserving whitespace) -/ hn;
        -- and some weird indentation
      obtain ⟨m, rfl⟩ := hm
    refine ⟨n + m, ?_⟩
    calc -- manually aligned `calc` block
      n   +   n   +  (m   +   m)
    = n   + ( n   +  (m   +   m)) := by rw [Nat.add_assoc]
      n   +  (n   +  (m   +   m))
    = n   + ((n   +   m)  +   m)  := by rw [Nat.add_assoc]
      n   + ((n   +   m)  +   m)
    = n   + ((m   +   n)  +   m)  := by rw [Nat.add_comm n m]
      n   + ((m   +   n)  +   m)
    = n   + ( m   +  (n   +   m)) := by rw [Nat.add_assoc]
      n   + ( m   +  (n   +   m))
    = n   +   m   +  (n   +   m)  := by rw [Nat.add_assoc]
  ⏎
  ⏎
  ⏎
  @[deprecated (since := "YYYY-MM-DD")]
  alias add_odd_theorem := add_even_theorem
-/
#guard_msgs (whitespace := exact) in
deprecate to add_even_theorem "YYYY-MM-DD"
theorem add_odd_theorem {n m : Nat} (hn : ∃ k, n = k + k) (hm : ∃ k, m = k + k) :
    ∃ k, n + m = k + k := by
  obtain ⟨n, rfl /- have a comment here (to test preserving whitespace) -/⟩ := hn;
      -- and some weird indentation
    obtain ⟨m, rfl⟩ := hm
  refine ⟨n + m, ?_⟩
  calc -- manually aligned `calc` block
    n   +   n   +  (m   +   m)
  = n   + ( n   +  (m   +   m)) := by rw [Nat.add_assoc]
    n   +  (n   +  (m   +   m))
  = n   + ((n   +   m)  +   m)  := by rw [Nat.add_assoc]
    n   + ((n   +   m)  +   m)
  = n   + ((m   +   n)  +   m)  := by rw [Nat.add_comm n m]
    n   + ((m   +   n)  +   m)
  = n   + ( m   +  (n   +   m)) := by rw [Nat.add_assoc]
    n   + ( m   +  (n   +   m))
  = n   +   m   +  (n   +   m)  := by rw [Nat.add_assoc]

/--
info: * Pairings:
#[(a_very_long_replacement_theorem_name_to_make_sure_the_original_whitespace_is_preserved, originally_a_short_name)]

Try this:

  [apply] theorem a_very_long_replacement_theorem_name_to_make_sure_the_original_whitespace_is_preserved.{has, some, univ, parameters} :
      ∀ (u : Type has) (v : Type some) (w : Type univ) (x : Type parameters),
        u → v → w → x → True := fun _ _ _ _ _ _ _ _ => trivial
  ⏎
  ⏎
  @[deprecated (since := "YYYY-MM-DD")]
  alias originally_a_short_name :=
    a_very_long_replacement_theorem_name_to_make_sure_the_original_whitespace_is_preserved
-/
#guard_msgs (whitespace := exact) in
deprecate to a_very_long_replacement_theorem_name_to_make_sure_the_original_whitespace_is_preserved
  "YYYY-MM-DD"
theorem originally_a_short_name.{has, some, univ, parameters} :
    ∀ (u : Type has) (v : Type some) (w : Type univ) (x : Type parameters),
      u → v → w → x → True := fun _ _ _ _ _ _ _ _ => trivial
