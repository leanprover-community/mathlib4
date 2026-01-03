import Mathlib

namespace SimpleGraph

open Walk

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/--
The first vertex at which two walks starting from the same vertex diverge.
-/
def DivergentPt {u v w : V} : G.Walk u v → G.Walk u w → V
  | nil, _ => u
  | _, nil => u
  | @cons _ _ _ v _ _ p, @cons _ _ _ w _ _ q =>
    if h : v = w
    then DivergentPt p (q.copy h.symm rfl)
    else u

@[simp]
theorem nil_divergentPt {u v : V} (p : G.Walk u v) :
    DivergentPt nil p = u :=
  rfl

@[simp]
theorem divergentPt_nil {u v : V} (p : G.Walk u v) :
    DivergentPt p nil = u := by
  cases p <;> rfl

@[simp]
theorem divergentPt_rfl {u v : V} (p : G.Walk u v) :
    DivergentPt p p = v := by
  induction p with
  | nil => rfl
  | cons h p ih => simpa [DivergentPt]

theorem divergentPt_cons_cons {a u₁ u₂ v w : V} (p : G.Walk u₁ v) (q : G.Walk u₂ w)
    (h₁ : G.Adj a u₁) (h₂ : G.Adj a u₂) (heq : u₁ = u₂) :
    DivergentPt (cons h₁ p) (cons h₂ q) = DivergentPt p (q.copy heq.symm rfl) := by
  subst heq
  simp [DivergentPt]

@[symm]
theorem divergentPt_symm {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    DivergentPt p q = DivergentPt q p := by
  induction p with
  | nil => simp
  | cons =>
    cases q with
    | nil => simp
    | cons =>
      rw [DivergentPt, DivergentPt]
      split <;> split <;> aesop

theorem divergentPt_in_support_fst {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    DivergentPt p q ∈ p.support := by
  induction p with
  | nil => simp
  | cons =>
    cases q with
    | nil => simp
    | cons =>
      rw [DivergentPt]
      split <;> aesop

theorem divergentPt_in_support_snd {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    DivergentPt p q ∈ q.support :=
  divergentPt_symm p q ▸ divergentPt_in_support_fst q p

/--
Given two walks `p` and `q` starting and ending at the same vertices, cut of the starting common
part, reverse `q`, glue them together, then bypass the whole appended walk.
This constructs a cycle from two different paths as shows in `getCycle_IsCycle`.
-/
def getCycle {u v : V} (p q : G.Walk u v) : G.Walk (DivergentPt p q) (DivergentPt p q) :=
  ((p.dropUntil (DivergentPt p q) (divergentPt_in_support_fst p q)).append
  (q.dropUntil (DivergentPt p q) (by simp [divergentPt_in_support_snd p q])).reverse).cycleBypass

theorem dropUntil_cons {u v w a : V} {p : G.Walk u v} (h : G.Adj w u) (_ : a ≠ w)
    (ha : a ∈ p.support) :
    (cons h p).dropUntil a (List.mem_of_mem_tail ha) = p.dropUntil a ha := by
  dsimp only [dropUntil]
  aesop

theorem dropUntil_eq {u v w₁ w₂ : V} {p : G.Walk u v} (hw : w₁ ∈ p.support) (heq : w₁ = w₂) :
    p.dropUntil w₁ hw = (p.dropUntil w₂ (heq ▸ hw)).copy heq.symm rfl := by
  subst heq
  rfl

@[simp]
theorem cycleBypass_copy {u v : V} (p : G.Walk u u) (h : u = v) :
    (p.copy h h).cycleBypass = p.cycleBypass.copy h h := by
  subst h
  rfl

theorem cons_in_cycleBypass_support {u v : V} (p : G.Walk u v) (h : G.Adj v u) :
    u ∈ (cycleBypass (cons h p)).support := by
  cases p <;> simp [cycleBypass]

theorem in_dropUntil_of_subset {u v a b : V} (p : G.Walk u v) (ha : a ∈ p.support)
    (hb : b ∈ p.support) (h : (p.dropUntil a ha).support ⊆ (p.dropUntil b hb).support) :
    a ∈ (p.dropUntil b hb).support := by
  apply h
  exact start_mem_support (p.dropUntil a ha)

theorem bypass_eq_nil {u : V} (p : G.Walk u u) :
    p.bypass = Walk.nil :=
  (isPath_iff_eq_nil p.bypass).mp <| bypass_isPath p

theorem dropUntil_penultimate {u v w : V} (p : G.Walk u v) (h : w ∈ p.support) (hn : w ≠ v) :
    (p.dropUntil w h).penultimate = p.penultimate := by
  induction p with
  | nil => simp [hn] at h
  | @cons u _ _ ha p ih =>
    rw [support_cons, List.mem_cons] at h
    by_cases! hw : u = w
    · subst hw
      simp [dropUntil]
    · cases p with
      | nil => simp [hn, hw.symm] at h
      | cons => simp only [dropUntil, hw, penultimate_cons_cons]; tauto

/-- false in general
to make it work, we must assume that `v` is not in `p.support.dorpLast`, in which case im not sure
the statement is still useful.
counterexample: `u - v - a - b - v`
-/
theorem bypass_penultimate_eq {u v : V} (p : G.Walk u v) (hn : u ≠ v) :
    p.bypass.penultimate = p.penultimate := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    by_cases! hv : v = w
    · subst hv

      sorry
    cases p with
    | nil => simp [bypass, h.ne]
    | @cons u₁ v₁ w₁ ha p =>
      rw [bypass]
      split_ifs with hs
      · by_cases! hv : v = w
        · subst hv
          simp [bypass_eq_nil, hn] at hs
        rwa [penultimate_cons_cons, ← ih hv, dropUntil_penultimate]
      · by_cases! hv : v = w
        · subst hv
          simp only [bypass_eq_nil, penultimate_cons_nil, penultimate_cons_cons]

          sorry
        rw [penultimate_cons_cons, ← ih hv, bypass]
        split
        · exact penultimate_cons_of_not_nil _ _ (not_nil_of_ne hv)
        · rw [penultimate_cons_cons]

/--
Also false in general for the same reason as above
-/
theorem concat_in_bypass_support {u v w : V} (p : G.Walk u v) (h : G.Adj v w) (hn : u ≠ w) :
    v ∈ (p.concat h).bypass.support := by
  induction p with
  | nil => exact start_mem_support (nil.concat h).bypass
  | cons ha p ih =>
    specialize ih h
    rename_i ut t wt
    by_cases ht : t ≠ w
    · rw [concat_cons, bypass]
      split_ifs with hs
      · specialize ih ht
        apply in_dropUntil_of_subset _ ih
        sorry
      · simpa using Or.inr <| ih ht
    simp only [ne_eq, Decidable.not_not] at ht
    simp only [concat_cons]
    subst ht
    have : (p.concat h).bypass = Walk.nil:= by
      exact bypass_eq_nil (p.concat h)
    rw [bypass, this]
    simp [hn]
    sorry

theorem concat_in_cycleBypass_support {u v : V} (p : G.Walk u v) (h : G.Adj v u) :
    v ∈ (cycleBypass (p.concat h)).support := by
  cases p with
  | nil => simp
  | cons ha p =>
    rw [concat_cons, cycleBypass, support_cons, List.mem_cons]
    exact Or.inr <| concat_in_bypass_support p h ha.ne'

theorem getCycle_cons_cons_of_eq {u₁ u₂ v w : V} {p : G.Walk u₁ v} (h₁ : G.Adj w u₁)
    (q : G.Walk u₂ v) (h₂ : G.Adj w u₂) (heq : u₁ = u₂) (hp : w ∉ p.support) :
    getCycle (cons h₁ p) (cons h₂ q) = (getCycle p (q.copy heq.symm rfl)).copy
      (divergentPt_cons_cons p q h₁ h₂ heq).symm (divergentPt_cons_cons p q h₁ h₂ heq).symm := by
  have ha : DivergentPt (cons h₁ p) (cons h₂ q) ∈ p.support := by
    simpa [divergentPt_cons_cons _ _ _ _ heq] using divergentPt_in_support_fst _ _
  have hb : DivergentPt (cons h₁ p) (cons h₂ q) ∈ q.support := by
    simpa [divergentPt_cons_cons _ _ _ _ heq]
      using divergentPt_in_support_snd _ (q.copy heq.symm rfl)
  have h : DivergentPt (cons h₁ p) (cons h₂ q) ≠ w := by
    contrapose ha
    rwa [ha]
  simp [getCycle, dropUntil_cons h₁ h ha, dropUntil_cons h₂ h hb,
    dropUntil_eq _ (divergentPt_cons_cons p q h₁ h₂ heq)]

theorem cons_in_getCycle_support {u₁ u₂ v w : V} (p : G.Walk u₁ v) (q : G.Walk u₂ v)
    (h : G.Adj u₁ u₂) : u₂ ∈ (getCycle p (cons h q)).support := by
  induction p with
  | nil => simpa [getCycle, dropUntil] using concat_in_cycleBypass_support _ _
  | cons ha p ih =>
    sorry

theorem divergentPt_cons_cons_in_support {u₁ u₂ v w : V} {p : G.Walk u₁ v} (h₁ : G.Adj w u₁)
    (q : G.Walk u₂ v) (h₂ : G.Adj w u₂) (heq : u₁ ≠ u₂) :
    DivergentPt (cons h₁ p) (cons h₂ q) ∈ (getCycle p (cons h₁.symm (cons h₂ q))).support := by
  have : DivergentPt (cons h₁ p) (cons h₂ q) = w := by simp [DivergentPt, heq]
  rw [this]
  apply cons_in_getCycle_support
  exact DivergentPt p p

theorem getCycle_cons_cons_of_ne {u₁ u₂ v w : V} {p : G.Walk u₁ v} (h₁ : G.Adj w u₁)
    (q : G.Walk u₂ v) (h₂ : G.Adj w u₂) (heq : u₁ ≠ u₂) (hp : w ∉ p.support) :
    getCycle (cons h₁ p) (cons h₂ q) = (getCycle p (cons h₁.symm (cons h₂ q))).rotate
    (divergentPt_cons_cons_in_support h₁ q h₂ heq) := by
  sorry

lemma cycleBypass_support_subset {v : V} : ∀ {w : G.Walk v v}, w.cycleBypass.support ⊆ w.support
  | .nil => by simp
  | .cons (v := v') hvv' w => by
    simp [cycleBypass, List.subset_cons_of_subset v (support_bypass_subset w)]

theorem getCycle_support_subset {u v : V} (p q : G.Walk u v) :
    (getCycle p q).support ⊆ p.support ++ q.support := by
  simp only [getCycle]
  have : (getCycle p q).support ⊆ ((p.dropUntil (DivergentPt p q) _).append
      (q.dropUntil (DivergentPt p q) _).reverse).support := cycleBypass_support_subset
  apply trans this
  intro a ha
  simp only [mem_support_append_iff, support_reverse, List.mem_reverse, List.mem_append] at ha ⊢
  cases ha with
  | inl ha => exact Or.inl <| (support_dropUntil_subset p (divergentPt_in_support_fst p q)) ha
  | inr ha => exact Or.inr <| (support_dropUntil_subset q (divergentPt_in_support_snd p q)) ha

theorem getCycle_isCycle {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (h : p ≠ q) : (getCycle p q).IsCycle := by
  induction p with
  | nil => exact (h.symm ((isPath_iff_eq_nil q).mp hq)).elim
  | cons hap p ih =>
    cases q with
    | nil => exact (h ((isPath_iff_eq_nil _).mp hp)).elim
    | cons haq q =>
      expose_names
      by_cases heq : v_1 = v_2
      · rw [getCycle_cons_cons_of_eq _ _ _ heq]
        · rw [isCycle_copy]
          rw [cons_isPath_iff] at hp hq
          apply ih hp.1 (by simp [hq.1])
          subst heq
          simp only [ne_eq, cons.injEq, heq_eq_eq, true_and] at h ⊢
          exact h
        · aesop
      · by_cases hv : v_1 ∈ q.support
        · -- this cycle here is v_1 -- u_1 -- v_2 -- v_1
          sorry
        rw [getCycle_cons_cons_of_ne _ _ _ heq]
        · apply IsCycle.rotate
          apply ih
          · rw [cons_isPath_iff] at hp
            tauto
          · rw [cons_isPath_iff]
            apply And.intro hq
            simp only [support_cons, List.mem_cons, not_or]
            exact ⟨hap.ne', hv⟩
          · aesop
        · rw [cons_isPath_iff] at hp
          tauto

end SimpleGraph
