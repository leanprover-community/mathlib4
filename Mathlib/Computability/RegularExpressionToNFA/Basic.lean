/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
-/
import Mathlib.Computability.RegularExpressionToNFA.Defs
import Mathlib.Data.List.Indexes

#align_import computability.regular_expression_to_NFA.basic

/-!
# Proof That Converting Regular Expressions to NFA's is Correct

Inductively proves that `RegularExpression.toNFA` converts a regular expression to an NFA with
the same accepting language.

TODO:
 * possibly merge the files into computability/regular_expression? or change filenames?
 * mark things as @simp?
 * clean up things
-/


universe u

variable {α : Type u}

namespace RegularExpression

lemma zero_toNFA_correct : (zero : RegularExpression α).matches' = zero.toNFA.accepts := by
  ext
  refine' ⟨False.elim, _⟩
  rintro ⟨q, ⟨⟩, _⟩

lemma epsilon_toNFA_correct :
    (epsilon : RegularExpression α).matches' = epsilon.toNFA.accepts := by
  ext x
  constructor
  · rintro ⟨⟨⟩⟩; repeat' fconstructor
  · rintro ⟨q, _, eval⟩
    rcases x.eq_nil_or_concat with eq | ⟨_, _, eq⟩ <;> subst eq
    case inl => simp
    rw [NFA.eval_append_singleton, NFA.mem_stepSet] at eval
    rcases eval with ⟨_, _, ⟨⟩⟩

lemma char_toNFA_correct {a : α} : (char a).matches' = (char a).toNFA.accepts := by
  ext x
  constructor
  · rintro ⟨⟨⟩⟩
    refine' ⟨true, rfl, _⟩
    simp only [NFA.eval, NFA.evalFrom, List.foldl]
    rw [NFA.mem_stepSet]
    repeat' fconstructor
  · rintro ⟨⟨⟩|⟨⟩, accept, eval⟩
    case false.intro => cases accept
    rcases x.eq_nil_or_concat with eq | ⟨as, c, eq⟩ <;> subst eq
    case inl => cases eval
    unfold NFA.eval NFA.evalFrom at eval
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, Set.mem_singleton_iff,
      RegularExpression.matches'_char, List.foldl_nil] at *
    rw [NFA.mem_stepSet] at eval
    rcases eval with ⟨⟨⟩|⟨⟩, mem, step⟩
    case true.intro => rcases step with ⟨⟨⟩, _, _⟩
    rcases as.eq_nil_or_concat with eq | ⟨_, _, eq⟩ <;> subst eq
    case inl => rcases step with ⟨_, eq, _⟩; exact eq ▸ rfl
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.append_assoc, List.singleton_append] at *
    rw [NFA.mem_stepSet] at mem
    rcases mem with ⟨_, _, _, _, ⟨⟩⟩

lemma plus_toNFA_correct {r₁ r₂ : RegularExpression α}
    (hr₁ : r₁.matches' = r₁.toNFA.accepts)
    (hr₂ : r₂.matches' = r₂.toNFA.accepts) :
    (r₁.plus r₂).matches' = (r₁.plus r₂).toNFA.accepts := by
  ext x
  constructor
  · rintro (hx | hx) <;>
    · simp only [hr₁, hr₂] at hx
      rw [NFA.mem_accepts] at *
      unfold NFA.eval NFA.evalFrom at *
      rcases hx with ⟨q, accept, eval⟩
      first | exists Sum.inl q | exists Sum.inr q
      refine' ⟨accept, _⟩; clear accept
      induction x using List.list_reverse_induction generalizing q
      case base => exact eval
      rename_i as a ih
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet] at *
      rcases eval with ⟨p, mem, step⟩
      first | exists Sum.inl p | exists Sum.inr p
      exact ⟨ih p mem, step⟩
  · rintro ⟨q | q, accept, eval⟩ <;>
    · simp only [plus_def, matches'_add, hr₁, hr₂]
      first | left; exists q | right; exists q
      refine' ⟨accept, _⟩; clear accept
      induction x using List.list_reverse_induction generalizing q
      case base => exact eval
      rename_i as a ih
      unfold NFA.eval NFA.evalFrom at *
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet] at *
      rcases eval with ⟨p, mem, step⟩
      rcases p with p | p <;> first | exact ⟨p, ih p mem, step⟩ | cases step

lemma comp_toNFA_eval₁ {r₁ r₂ : RegularExpression α} {x : List α} (q : r₁.State) :
    q ∈ r₁.toNFA.eval x ↔ Sum.inl q ∈ (r₁.comp r₂).toNFA.eval x := by
  induction x using List.list_reverse_induction generalizing q
  case base => exact ⟨id, id⟩
  rename_i as a ih
  constructor <;> simp only [NFA.eval_append_singleton, NFA.mem_stepSet] <;> rintro ⟨p, eval, step⟩
  · rw [ih p] at eval
    exact ⟨Sum.inl p, eval, step⟩
  · rcases p with p | p
    case inl => rw [← ih p] at eval; exact ⟨p, eval, step⟩
    case inr => cases step

lemma comp_toNFA_eval₂ {r₁ r₂ : RegularExpression α} {x y : List α} (q : r₂.State)
    (accepts : r₁.toNFA.accepts x) :
    q ∈ r₂.toNFA.eval y →
    Sum.inr q ∈ (r₁.comp r₂).toNFA.evalFrom ((r₁.comp r₂).toNFA.eval x) y := by
  induction y using List.list_reverse_induction generalizing q
  case base =>
    intro h
    rcases accepts with ⟨p, accept, eval⟩
    rw [comp_toNFA_eval₁ p] at eval
    rcases x.eq_nil_or_concat with eq | ⟨as, a, eq⟩ <;> subst eq
    case inl => exact ⟨h, p, accept, eval⟩
    rw [NFA.evalFrom_nil]
    rw [NFA.eval_append_singleton, NFA.mem_stepSet] at *
    rcases eval with ⟨r, mem, step⟩
    refine' ⟨r, mem, _⟩
    cases r
    case inl => exact ⟨h, p, accept, step⟩
    case inr => cases step
  case ind bs b ih =>
    simp only [NFA.eval_append_singleton, NFA.evalFrom_append_singleton, NFA.mem_stepSet]
    rintro ⟨p, mem, step⟩
    exact ⟨Sum.inr p, ih p mem, step⟩

lemma comp_toNFA_correct {r₁ r₂ : RegularExpression α}
    (hr₁ : r₁.matches' = r₁.toNFA.accepts)
    (hr₂ : r₂.matches' = r₂.toNFA.accepts) :
    (r₁.comp r₂).matches' = (r₁.comp r₂).toNFA.accepts := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, comp⟩
    rw [hr₁] at hy
    rw [hr₂] at hz
    rw [← comp]
    rcases z.eq_nil_or_concat with eq | ⟨bs, b, eq⟩ <;> subst eq
    · rcases hy with ⟨q, q_accept, q_eval⟩
      simp only [List.append_nil, NFA.eval_nil, List.reverse_nil] at *
      rw [comp_toNFA_eval₁ q] at q_eval
      exact ⟨Sum.inl q, ⟨q_accept, hz⟩, q_eval⟩
    · rcases hz with ⟨q, accept, eval⟩
      refine' ⟨Sum.inr q, accept, _⟩
      simp only [← List.append_assoc]
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at *
      rcases eval with ⟨p, mem, step⟩
      refine' ⟨Sum.inr p, _, step⟩
      unfold NFA.eval NFA.evalFrom
      rw [List.foldl_append]
      exact comp_toNFA_eval₂ p hy mem
  · rintro ⟨q | q, accept, eval⟩
    · rcases accept with ⟨accept, nil⟩
      refine' ⟨x, _, [], _, by simp⟩
      · rw [hr₁]
        refine' ⟨q, accept, _⟩; clear accept
        induction x using List.list_reverse_induction generalizing q
        case base => exact eval
        rename_i as a ih
        unfold NFA.eval NFA.evalFrom at *
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet] at *
        rcases eval with ⟨p | p, mem, step⟩
        · exact ⟨p, ih p mem, step⟩
        · cases step
      · rw [hr₂]
        rcases nil with ⟨q, accept, eval⟩
        exact ⟨q, accept, eval⟩
    · suffices ∃ y z, y ∈ r₁.toNFA.accepts ∧ q ∈ r₂.toNFA.eval z ∧ y ++ z = x by
        rcases this with ⟨y, z, y_accepts, z_eval, append⟩
        refine' ⟨y, hr₁ ▸ y_accepts, z, hr₂ ▸ ⟨q, accept, z_eval⟩, append⟩
      clear accept
      induction x using List.list_reverse_induction generalizing q
      case base => rcases eval with ⟨start, _⟩; exact ⟨[], [], by simpa, start, rfl⟩
      rename_i as a ih
      unfold NFA.eval NFA.evalFrom
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at eval
      rcases eval with ⟨p | p, mem, step⟩
      · rcases step with ⟨start, r, accept, step⟩
        refine' ⟨as ++ [a], [], ⟨r, accept, _⟩, start, by simp⟩
        rw [NFA.eval_append_singleton, NFA.mem_stepSet]
        rw [← comp_toNFA_eval₁ p] at mem
        exact ⟨p, mem, step⟩
      · rcases ih p mem with ⟨y, z, accepts, eval, append⟩
        refine' ⟨y, z ++ [a], accepts, _, by simp [← append]⟩
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, NFA.mem_stepSet]
        exact ⟨p, eval, step⟩

/-- All start states of an unstarred NFA can be reached in a starred NFA by a string in the
original's language. -/
lemma star_eval_aux {r : RegularExpression α} {y} (h : y ∈ r.toNFA.accepts) :
    r.star.toNFA.start \ {none} ⊆ r.star.toNFA.eval y := by
  rintro (⟨⟩ | s) ⟨selem, snelem⟩
  · simp at snelem
  rcases y.eq_nil_or_concat with rfl | ⟨as, a, rfl⟩
  · exact selem
  simp [NFA.mem_accepts, NFA.mem_stepSet] at h
  rcases h with ⟨q, accept, p, eval, step⟩
  simp only [NFA.eval_append_singleton, NFA.mem_stepSet]
  refine ⟨some p, ?_, Or.inr ⟨q, accept, step, selem⟩⟩
  clear step
  induction as using List.list_reverse_induction generalizing p
  · exact eval
  rename_i bs b ih
  simp only [NFA.evalFrom_append_singleton, NFA.mem_stepSet] at eval
  rcases eval with ⟨t, eval, step⟩
  simp only [NFA.eval_append_singleton, NFA.mem_stepSet]
  exact ⟨some t, ih t eval, Or.inl step⟩

/-- A state of an unstarred NFA can be reached in the starred NFA by any word that has prefixes
accepted by the original NFA and a suffix that would have reached the state anyway. -/
lemma star_eval {r : RegularExpression α} {x : List α} {q : r.State} :
    some q ∈ r.star.toNFA.eval x ↔
    ∃ (ys : List (List α)) (z : List α),
    x = ys.join ++ z ∧ q ∈ r.toNFA.eval z ∧ ∀ y ∈ ys, y ∈ r.toNFA.accepts := by
  constructor
  · induction x using List.list_reverse_induction generalizing q
    · rintro h; exact ⟨[], [], rfl, h, List.forall_mem_nil _⟩
    rename_i as a ih
    rw [NFA.eval_append_singleton,NFA.mem_stepSet]
    rintro ⟨⟨⟩ | p, eval, step⟩
    · cases step
    specialize ih eval
    rcases ih with ⟨ys, z, rfl, evalz, allys⟩
    rcases step with step | ⟨t, accept, step, start⟩
    · refine ⟨ys, z ++ [a], List.append_assoc _ _ _, ?_, allys⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨p, evalz, step⟩
    · refine ⟨ys ++ [z ++ [a]], [], by simp, start, ?_⟩
      refine List.forall_mem_append.mpr ⟨allys, List.forall_mem_singleton.mpr ⟨t, accept, ?_⟩⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨p, evalz, step⟩
  · rintro ⟨ys, z, rfl, eval, allys⟩
    unfold NFA.eval
    induction ys generalizing q
    · induction z using List.list_reverse_induction generalizing q <;> simp only [toNFA]
      · exact eval
      case ind as a ih =>
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at eval
      rcases eval with ⟨t, eval, step⟩
      simp [NFA.mem_stepSet]
      refine ⟨some t, ih eval, Or.inl step⟩
    case cons y ys ih =>
      simp only [List.join, List.append_assoc]
      simp at allys
      rcases allys with ⟨accepty, allys⟩
      specialize ih eval allys
      generalize ys.join ++ z = ysj at ih
      rw [NFA.evalFrom_append]
      refine (r.star.toNFA).evalFrom_subset _ (star_eval_aux accepty) ?_
      clear eval
      induction ysj using List.list_reverse_induction generalizing q
      · simp; exact ih
      rename_i as a iih
      simp only [NFA.evalFrom_append_singleton,NFA.mem_stepSet] at *
      rcases ih with ⟨⟨⟩ | t, eval, step⟩
      · simp[toNFA,Set.mem_def] at step
      exact ⟨some t, iih eval, step⟩

lemma star_toNFA_correct {r : RegularExpression α} (hr : r.matches' = r.toNFA.accepts) :
    (star r).matches' = (star r).toNFA.accepts := by
  ext x
  rw [matches'_star,Language.mem_kstar, NFA.mem_accepts]
  simp only [hr]
  constructor
  · rintro ⟨l, rfl, h⟩
    rcases l.eq_nil_or_concat with rfl | ⟨ys, z, rfl⟩
    · exact ⟨none, trivial, trivial⟩
    · rw [List.forall_mem_append, List.forall_mem_singleton, NFA.mem_accepts] at h
      rcases h with ⟨allys, q, accept, eval⟩
      exact ⟨some q, accept, star_eval.mpr ⟨ys, z, by simp, eval, allys⟩⟩
  · rintro ⟨⟨⟩ | q, accept, eval⟩
    · refine ⟨[], ?_, by simp⟩
      rcases x.eq_nil_or_concat with rfl | ⟨as, a, rfl⟩
      case inl => exact rfl
      simp [NFA.evalFrom_append_singleton, NFA.mem_stepSet] at eval
      rcases eval with ⟨_ | _, _, ⟨⟩⟩
    · rcases star_eval.mp eval with ⟨ys, z, rfl, evalz, allys⟩
      refine ⟨ys ++ [z], by simp, ?_⟩
      exact List.forall_mem_append.mpr ⟨allys, List.forall_mem_singleton.mpr ⟨q, accept, evalz⟩⟩

/-- The NFA constructed from a regular expression retains the same language. -/
theorem toNFA_correct (r : RegularExpression α) : r.matches' = r.toNFA.accepts := by
  induction r
  case zero => exact zero_toNFA_correct
  case epsilon => exact epsilon_toNFA_correct
  case char a => exact char_toNFA_correct
  case plus r₁ r₂ hr₁ hr₂ => exact plus_toNFA_correct hr₁ hr₂
  case comp r₁ r₂ hr₁ hr₂ => exact comp_toNFA_correct hr₁ hr₂
  case star r hr => exact star_toNFA_correct hr

end RegularExpression

