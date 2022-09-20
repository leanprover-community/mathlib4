import Std.Data.List.Basic
import Mathlib.Init.Logic
import Mathlib.Data.List.Pairwise

namespace List

@[simp]
theorem chain_cons {a b : α} {l : List α} : Chain R a (b :: l) ↔ R a b ∧ Chain R b l :=
  ⟨fun p => by cases p with | cons n p => exact ⟨n, p⟩,
   fun ⟨n, p⟩ => p.cons n⟩

theorem Chain.imp' {R S : α → α → Prop} (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α}
    (Hab : ∀ ⦃c⦄, R a c → S b c) {l : List α} (p : Chain R a l) : Chain S b l := by
  induction p generalizing b with
  | nil => constructor
  | cons r _ ih =>
      constructor
      · exact Hab r
      · exact ih (@HRS _)

theorem Chain.imp {R S : α → α → Prop} (H : ∀ a b, R a b → S a b) {a : α} {l : List α}
    (p : Chain R a l) : Chain S a l :=
  p.imp' H (H a)

protected theorem Pairwise.chain (p : Pairwise R (a :: l)) : Chain R a l := by
  rcases Pairwise_cons.1 p with ⟨r,p'⟩
  clear p
  induction p' generalizing a with
  | nil => exact Chain.nil
  | cons r' _ ih =>
      simp only [chain_cons, forall_mem_cons] at r
      exact chain_cons.2 ⟨r.1, ih r'⟩

protected theorem Chain.pairwise {R : α → α → Prop} [Trans R R R] : ∀ {a : α} {l : List α}, Chain R a l → Pairwise R (a :: l)
  | a, [], .nil => pairwise_singleton _ _
  | a, _, .cons h hb =>
    hb.pairwise.cons
      (by
        simp only [mem_cons, forall_eq_or_imp, h, true_and]
        exact fun c hc => trans h (rel_of_pairwise_cons hb.pairwise hc))

theorem chain_iff_pairwise {R : α → α → Prop} [Trans R R R] {a : α} {l : List α} : Chain R a l ↔ Pairwise R (a :: l) :=
  ⟨Chain.pairwise, Pairwise.chain⟩
