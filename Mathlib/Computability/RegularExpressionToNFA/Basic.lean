/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
-/
import Mathlib.Computability.RegularExpressionToNFA.Defs
import Mathlib.Computability.RegularExpressionToNFA.Star

#align_import computability.regular_expression_to_NFA.basic

/-!
# Proof That Converting Regular Expressions to NFA's is Correct

Inductively proves that `regular_expression.to_NFA` converts a regular expression to an NFA with
the same accepting language.

TODO: 
 * possibly merge the files into computability/regular_expression? or change filenames?
 * mark things as @simp?
 * clean up things
-/


universe u

variable {α : Type u}

namespace RegularExpression

theorem zero_toNFA_correct : (zero : RegularExpression α).matches' = zero.toNFA.accepts :=
  by
  ext
  constructor
  · intro hx; cases hx
  · intro hx
    rcases hx with ⟨q, accept, eval⟩
    cases accept

theorem epsilon_toNFA_correct : (epsilon : RegularExpression α).matches' = epsilon.toNFA.accepts :=
  by
  ext x
  constructor
  · rintro ⟨⟨⟩⟩; repeat' fconstructor
  · rintro ⟨q, accept, eval⟩
    cases accept
    revert eval
    rw [← x.reverse_reverse]
    induction x.reverse
    case nil => simp
    case cons a as ih =>
      intro hx
      rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at hx
      rcases hx with ⟨q, mem, step⟩
      cases step

theorem char_toNFA_correct {a : α} : (char a).matches' = (char a).toNFA.accepts :=
  by
  ext x
  constructor
  · rintro ⟨⟨⟩⟩
    refine' ⟨true, rfl, _⟩
    simp only [NFA.eval, NFA.evalFrom, List.foldl]
    rw [NFA.mem_stepSet]
    repeat' fconstructor
  · rintro ⟨q, accept, eval⟩
    cases q
    case false => contradiction
    clear accept
    revert eval
    rw [← x.reverse_reverse]
    cases' x.reverse with c as
    case nil => intro hx; contradiction
    intro hx
    unfold NFA.eval NFA.evalFrom at hx
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, Set.mem_singleton_iff,
      RegularExpression.matches'_char, List.foldl_nil] at *
    rw [NFA.mem_stepSet] at hx
    rcases hx with ⟨p, mem, step⟩
    cases p
    case true => rcases step with ⟨_, _, _⟩; contradiction
    revert mem
    cases' as with b as
    case nil =>
      intro _
      rcases step with ⟨_, eq, _⟩
      rw [eq]
      exact rfl
    intro h
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.append_assoc, List.singleton_append] at *
    rcases h with ⟨S, ⟨q, range⟩, mem⟩
    rw [← range] at mem
    simp only [exists_prop, Set.mem_iUnion] at mem
    rcases mem with ⟨_, _, _, _⟩
    contradiction

theorem plus_toNFA_correct {r₁ r₂ : RegularExpression α} (hr₁ : r₁.matches' = r₁.toNFA.accepts)
    (hr₂ : r₂.matches' = r₂.toNFA.accepts) : (r₁.plus r₂).matches' = (r₁.plus r₂).toNFA.accepts :=
  by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    case inl =>
      rw [hr₁] at hx; clear hr₁ hr₂
      rw [Set.mem_def] at *
      unfold NFA.accepts NFA.eval NFA.evalFrom at *
      rcases hx with ⟨q, accept, eval⟩
      refine' ⟨Sum.inl q, accept, _⟩; clear accept
      revert eval
      rw [← x.reverse_reverse]
      induction' x.reverse with a as ih generalizing q
      case nil => exact id
      intro mem
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
      rcases mem with ⟨S, ⟨p, range⟩, mem⟩
      rw [← range, Set.mem_iUnion, exists_prop] at mem
      rcases mem with ⟨mem, step⟩
      rw [NFA.mem_stepSet]
      exact ⟨Sum.inl p, ih p mem, step⟩
    case inr =>
      rw [hr₂] at hx; clear hr₁ hr₂
      rw [Set.mem_def] at *
      unfold NFA.accepts NFA.eval NFA.evalFrom at *
      rcases hx with ⟨q, accept, eval⟩
      refine' ⟨Sum.inr q, accept, _⟩; clear accept
      revert eval
      rw [← x.reverse_reverse]
      induction' x.reverse with a as ih generalizing q
      case nil => exact id
      intro mem
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
      rcases mem with ⟨S, ⟨p, range⟩, mem⟩
      rw [← range, Set.mem_iUnion, exists_prop] at mem
      rcases mem with ⟨mem, step⟩
      rw [NFA.mem_stepSet]
      exact ⟨Sum.inr p, ih p mem, step⟩
  · rintro ⟨q, accept, eval⟩
    rcases q with q | q
    case inl =>
      left
      rw [hr₁]; clear hr₁ hr₂
      refine' ⟨q, accept, _⟩; clear accept
      revert eval
      rw [← x.reverse_reverse]
      induction' x.reverse with a as ih generalizing q
      case nil => exact id
      intro h
      unfold NFA.eval NFA.evalFrom at *
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
      rcases h with ⟨S, ⟨p, range⟩, mem⟩
      rw [← range] at mem
      rw [Set.mem_iUnion, exists_prop] at mem
      rcases mem with ⟨mem, step⟩
      rw [NFA.mem_stepSet]
      rcases p with p | p
      case inl => exact ⟨p, ih p mem, step⟩
      case inr => cases step
    case inr =>
      right
      rw [hr₂]; clear hr₁ hr₂
      refine' ⟨q, accept, _⟩; clear accept
      revert eval
      rw [← x.reverse_reverse]
      induction' x.reverse with a as ih generalizing q
      case nil => exact id
      intro h
      unfold NFA.eval NFA.evalFrom at *
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
      rcases h with ⟨S, ⟨p, range⟩, mem⟩
      rw [← range] at mem
      rw [Set.mem_iUnion, exists_prop] at mem
      rcases mem with ⟨mem, step⟩
      rw [NFA.mem_stepSet]
      rcases p with p | p
      case inl => cases step
      case inr => exact ⟨p, ih p mem, step⟩

theorem comp_toNFA_eval₁ {r₁ r₂ : RegularExpression α} {x : List α} (q : r₁.State) :
    q ∈ r₁.toNFA.eval x ↔ Sum.inl q ∈ (r₁.comp r₂).toNFA.eval x :=
  by
  rw [← x.reverse_reverse]
  induction' x.reverse with a as ih generalizing q
  case nil => exact ⟨id, id⟩
  constructor
  · intro h
    rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at *
    rcases h with ⟨p, eval, step⟩
    rw [ih p] at eval
    exact ⟨Sum.inl p, eval, step⟩
  · intro h
    rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at *
    rcases h with ⟨p, eval, step⟩
    rcases p with p | p
    case inl => rw [← ih p] at eval; exact ⟨p, eval, step⟩
    case inr => cases step

theorem comp_toNFA_eval₂ {r₁ r₂ : RegularExpression α} {x y : List α} (q : r₂.State)
    (accepts : r₁.toNFA.accepts x) :
    q ∈ r₂.toNFA.eval y → Sum.inr q ∈ (r₁.comp r₂).toNFA.evalFrom ((r₁.comp r₂).toNFA.eval x) y :=
  by
  rw [← y.reverse_reverse]
  induction y.reverse generalizing q
  case nil =>
    intro h
    rcases accepts with ⟨p, accept, eval⟩
    rw [@comp_toNFA_eval₁ _ _ r₂ _ p] at eval
    revert eval
    rw [← x.reverse_reverse] at *
    cases' x.reverse with a as
    case nil => intro eval; exact ⟨h, p, accept, eval⟩
    intro eval
    rw [List.reverse_nil, NFA.evalFrom_nil]
    rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at *
    rcases eval with ⟨r, mem, step⟩
    refine' ⟨r, mem, _⟩
    cases r
    case inl => exact ⟨h, p, accept, step⟩
    case inr => cases step
  case cons b bs ih =>
    intro h
    simp only [List.reverse_cons, NFA.eval_append_singleton, NFA.evalFrom_append_singleton,
      NFA.mem_stepSet] at *
    rcases h with ⟨p, mem, step⟩
    refine' ⟨Sum.inr p, ih p mem, step⟩

theorem comp_toNFA_correct {r₁ r₂ : RegularExpression α} (hr₁ : r₁.matches' = r₁.toNFA.accepts)
    (hr₂ : r₂.matches' = r₂.toNFA.accepts) : (r₁.comp r₂).matches' = (r₁.comp r₂).toNFA.accepts :=
  by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, comp⟩
    rw [hr₁] at hy
    rw [hr₂] at hz
    rw [← comp]
    clear hr₁ hr₂ comp x
    rw [Set.mem_def] at *
    rw [← z.reverse_reverse] at *
    have ⟨ zr, zreq ⟩ : ∃ _, _ := ⟨z.reverse, rfl⟩
    rw[zreq] at hz
    rw[zreq]
    cases' zr with b bs
    case nil =>
      rcases hy with ⟨q, q_accept, q_eval⟩
      rcases hz with ⟨p, p_accept, p_eval⟩
      simp only [List.append_nil, NFA.eval_nil, List.reverse_nil] at *
      rw [comp_toNFA_eval₁ q] at q_eval
      exact ⟨Sum.inl q, ⟨q_accept, p, p_accept, p_eval⟩, q_eval⟩
    rcases hz with ⟨q, accept, eval⟩
    refine' ⟨Sum.inr q, accept, _⟩
    rw [List.reverse_cons] at *
    simp only [← List.append_assoc]
    rw [NFA.eval_append_singleton, NFA.mem_stepSet] at *
    rcases eval with ⟨p, mem, step⟩
    refine' ⟨Sum.inr p, _, step⟩
    unfold NFA.eval NFA.evalFrom
    rw [List.foldl_append]
    exact comp_toNFA_eval₂ p hy mem
  · rintro ⟨q, accept, eval⟩
    rcases q with q | q
    case inl =>
      rcases accept with ⟨accept, nil⟩
      refine' ⟨x, _, [], _, by simp⟩
      · rw [hr₁]
        refine' ⟨q, accept, _⟩; clear accept
        revert eval
        rw [← x.reverse_reverse]
        induction' x.reverse with a as ih generalizing q
        case nil => exact id
        intro h
        unfold NFA.eval NFA.evalFrom at *
        rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
          NFA.mem_stepSet] at *
        rcases h with ⟨p, mem, step⟩
        rcases p with p | p
        case inl => exact ⟨p, ih p mem, step⟩
        case inr => cases step
      · rw [hr₂]
        rcases nil with ⟨q, accept, eval⟩
        exact ⟨q, accept, eval⟩
    case
      inr =>
      suffices
        ∀ x q,
          Sum.inr q ∈ (r₁.comp r₂).toNFA.eval x →
            ∃ y z, y ∈ r₁.toNFA.accepts ∧ q ∈ r₂.toNFA.eval z ∧ y ++ z = x
        by
        specialize this x q eval
        rcases this with ⟨y, z, y_accepts, z_eval, append⟩
        refine' ⟨y, by simpa [hr₁], z, _, by assumption⟩
        rw [hr₂]
        exact ⟨q, accept, z_eval⟩
      clear accept eval q hr₁ hr₂
      intro x q
      rw [← x.reverse_reverse]
      induction' x.reverse with a as ih generalizing q
      case nil =>
        rintro ⟨start, nil⟩
        refine' ⟨[], [], _, start, by simp⟩
        unfold NFA.accepts at *
        simpa
      intro h
      unfold NFA.eval NFA.evalFrom
      rw [List.reverse_cons] at *
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at h
      rcases h with ⟨p, mem, step⟩
      rcases p with p | p
      case inl =>
        rcases step with ⟨start, r, accept, step⟩
        refine' ⟨as.reverse ++ [a], [], _, start, by simp⟩
        refine' ⟨r, accept, _⟩
        rw [NFA.eval_append_singleton, NFA.mem_stepSet]
        rw [← comp_toNFA_eval₁ p] at mem
        exact ⟨p, mem, step⟩
      case inr =>
        rcases ih p mem with ⟨y, z, accepts, eval, append⟩
        refine' ⟨y, z ++ [a], accepts, _, by simp [← append]⟩
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet]
        exact ⟨p, eval, step⟩

theorem star_toNFA_correct {r : RegularExpression α} (hr : r.matches' = r.toNFA.accepts) :
    (star r).matches' = (star r).toNFA.accepts :=
  by
  ext x
  rw [star_iff_pow]
  constructor
  · rintro ⟨n, h⟩
    rcases n with n | n
    case zero =>
      cases h
      refine' ⟨none, trivial, trivial⟩
    case succ =>
      rw [r.pow_eval x n hr] at h
      rcases h with ⟨q, accept, t⟩
      exact ⟨some q, accept, (r.star_eval x q).mpr ⟨n, t⟩⟩
  · rintro ⟨q, accept, eval⟩
    rcases q with q | q
    case none =>
      use 0
      rw [← x.reverse_reverse] at *
      have ⟨xr, xreq⟩ : ∃ _, _ := ⟨x.reverse, rfl⟩
      rw[xreq] at eval
      rw[xreq]
      cases' xr with a as
      case nil => exact rfl
      rw [List.reverse_cons, NFA.eval_append_singleton, NFA.mem_stepSet] at eval
      rcases eval with ⟨q, mem, step⟩
      cases q <;> cases step
    case some =>
      rcases(r.star_eval x q).mp eval with ⟨n, t⟩
      use n.succ
      exact (r.pow_eval x n hr).mpr ⟨q, accept, t⟩

theorem toNFA_correct (r : RegularExpression α) : r.matches' = r.toNFA.accepts :=
  by
  induction r
  case zero => exact zero_toNFA_correct
  case epsilon => exact epsilon_toNFA_correct
  case char a => exact char_toNFA_correct
  case plus r₁ r₂ hr₁ hr₂ => exact plus_toNFA_correct hr₁ hr₂
  case comp r₁ r₂ hr₁ hr₂ => exact comp_toNFA_correct hr₁ hr₂
  case star r hr => exact star_toNFA_correct hr

end RegularExpression

