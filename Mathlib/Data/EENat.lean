import Mathlib.Data.ENat.Lattice

def EENat : Type := WithBot (WithTop ℕ) deriving
  Bot, Zero, One, Nontrivial, PartialOrder, AddMonoidWithOne, SemilatticeSup,
  SemilatticeInf, Monoid, OrderedCommSemiring, LinearOrder

notation "ℕ±∞" => EENat

instance : OrderBot ℕ±∞ := inferInstanceAs <| OrderBot <| WithBot <| WithTop ℕ
instance : OrderTop ℕ±∞ := inferInstanceAs <| OrderTop <| WithBot <| WithTop ℕ
instance : SuccOrder ℕ±∞ := inferInstanceAs <| SuccOrder <| WithBot <| WithTop ℕ
instance : WellFoundedLT ℕ±∞ := inferInstanceAs <| WellFoundedLT <| WithBot <| WithTop ℕ
instance : CharZero ℕ±∞ := inferInstanceAs <| CharZero <| WithBot <| WithTop ℕ
instance : IsWellOrder ℕ±∞ (· < ·) := inferInstanceAs <| IsWellOrder (WithBot <| WithTop ℕ) (. < .)
instance : ZeroLEOneClass ℕ±∞ := inferInstanceAs <| ZeroLEOneClass <| WithBot <| WithTop ℕ

noncomputable instance : InfSet ℕ±∞ := inferInstanceAs <| InfSet <| WithBot <| ENat
noncomputable instance : SupSet ℕ±∞ := inferInstanceAs <| SupSet <| WithBot <| ENat
noncomputable instance : CompleteLinearOrder ℕ±∞ :=
  inferInstanceAs <| CompleteLinearOrder <| WithBot <| WithTop ℕ

namespace EENat

def fromNat (n : ℕ) : ℕ±∞ := n

lemma bot_ne_top : (⊥ : ℕ±∞) ≠ (⊤ : ℕ±∞) := _root_.bot_ne_top

lemma coe_lt_top (n : ℕ) : n < (⊤ : ℕ±∞) := by
  rw [lt_top_iff_ne_top]
  exact ne_of_beq_false rfl

lemma bot_lt_coe (n : ℕ) : (⊥ : ℕ±∞) < n := by
  rw [bot_lt_iff_ne_bot]
  exact ne_of_beq_false rfl

lemma coe_lt_coe {m n : ℕ} : (m : ℕ±∞) < n ↔ m < n := by
  fconstructor
  . intros h; exact WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)
  . intros h; exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h)

lemma coe_le_coe {m n : ℕ} : (m : ℕ±∞) ≤ n ↔ m ≤ n := by
  fconstructor
  . intros h; exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h)
  . intros h; exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)

@[elab_as_elim] def rec {C : ℕ±∞ → Sort _} (coe : ∀ (n : ℕ), C n) (top : C ⊤) (bot : C ⊥) : ∀ n : ℕ±∞, C n :=
WithBot.recBotCoe bot <| WithTop.recTopCoe top coe

@[elab_as_elim] def recOn (n : ℕ±∞) {C : ℕ±∞ → Sort _} (coe : ∀ (n : ℕ), C n) (top : C ⊤) (bot : C ⊥) : C n :=
rec coe top bot n

lemma eq_bot_of_lt_zero (n : ℕ±∞) : n < 0 → n = ⊥ := recOn n
  (fun n hn => False.elim <| not_le_of_lt hn <| Nat.cast_nonneg n)
  (fun hn => False.elim <| not_le_of_lt hn le_top)
  (fun _ => rfl)

lemma iSup_coe_eq_top {ι : Sort _} (f : ι → ℕ) :
  ⨆ x, (f x : ℕ±∞) = ⊤ ↔ ¬BddAbove (Set.range f) := by
  by_cases i1 : IsEmpty ι
  . simp only [ciSup_of_empty, _root_.bot_ne_top, false_iff, not_not]
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    refine i1.elim x
  rw [not_isEmpty_iff] at i1
  rw [iSup_eq_top, not_bddAbove_iff]
  refine' ⟨fun hf r => _, fun hf a ha => _⟩
  · rcases hf r (coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, coe_lt_coe.mp hi⟩
  · induction a using rec with
    | coe n =>
      specialize hf n
      obtain ⟨_, ⟨m, rfl⟩, hm⟩ := hf
      exact ⟨m, coe_lt_coe.mpr hm⟩
    | top => exact (lt_irrefl (⊤ : ℕ±∞) ha).elim
    | bot => exact ⟨Nonempty.some (inferInstance : Nonempty ι), bot_lt_coe _⟩

lemma iSup_coe_lt_top {ι : Sort _} (f : ι → ℕ) : (⨆ x, f x : ℕ±∞) < ⊤ ↔ BddAbove (Set.range f) :=
  lt_top_iff_ne_top.trans <| (iSup_coe_eq_top f).not.trans not_not

theorem coe_iSup {ι : Sort _} [Nonempty ι] (f : ι → ℕ) (hf : BddAbove (Set.range f)) :
  ↑(⨆ i, f i) = (⨆ i, f i : ℕ±∞) := by
  classical
  apply le_antisymm
  . rw [le_iSup_iff]
    refine rec ?_ (fun _ => le_top) ?_
    . intros n h
      rw [coe_le_coe, iSup, sSup]
      change dite _ _ _ ≤_
      split_ifs with H
      . apply Nat.find_le
        rintro _ ⟨m, rfl⟩
        exact coe_le_coe.mp <| h m
      . exact zero_le _
    . intro h
      have i1 : IsEmpty ι
      . by_contra r; rw [not_isEmpty_iff] at r; specialize h r.some; rw [le_bot_iff] at h;
        exact WithBot.coe_ne_bot h
      exact (not_isEmpty_iff.mpr inferInstance i1).elim
  . rw [iSup_le_iff]
    intros i
    rw [coe_le_coe, iSup]
    exact le_csSup hf ⟨_, rfl⟩

noncomputable def pred (m : ℕ±∞) := ⨆ x < m, x

lemma pred_le (m : ℕ±∞) : pred m ≤ m := iSup_le fun _ => iSup_le fun hi => le_of_lt hi

lemma pred_bot : pred ⊥ = ⊥ := le_antisymm (pred_le _) bot_le
lemma pred_top : pred ⊤ = ⊤ := le_antisymm le_top <| le_iSup_iff.mpr fun i hi => by
  induction i using rec with
  | coe n =>
    specialize hi (n + 1)
    have hi := (le_iSup _ ?_).trans hi
    . exact (not_lt_of_le hi <| coe_lt_coe.mpr (lt_add_one n)).elim
    . exact Iff.mp (cmp_eq_lt_iff (n + 1 : ℕ±∞) ⊤) rfl
  | top => exact le_refl _
  | bot =>
    specialize hi 0
    have hi := (le_iSup _ ?_).trans hi
    . exact ((not_le_of_lt <| bot_lt_coe 0) hi).elim
    . exact Iff.mp (cmp_eq_lt_iff 0 ⊤) rfl

lemma pred_zero : pred 0 = ⊥ := Function.swap le_antisymm bot_le <| iSup_le_iff.mpr fun i =>
  iSup_le_iff.mpr fun hi => by
    have hi := eq_bot_of_lt_zero _ hi
    subst hi
    rfl

lemma pred_succ (n : ℕ) : pred n.succ = n := le_antisymm (iSup_le <| fun i => iSup_le fun hi =>
  by exact Order.le_of_lt_succ hi) <| le_iSup_of_le n <|
  le_iSup_of_le (coe_lt_coe.mpr <| Nat.lt.base n) <| le_refl _

lemma pred_le_self (n : ℕ±∞) (hn : n ≤ pred n) : n = ⊥ ∨ n = ⊤ := by
  have H : ¬ (n = ⊥ ∨ n = ⊤) → ∃ (n' : ℕ), n = n'
  . intro h
    rw [not_or] at h
    induction n using rec with
    | coe n => exact ⟨n, rfl⟩
    | top => exact (h.right rfl).elim
    | bot => exact (h.left rfl).elim
  contrapose hn
  specialize H hn
  rcases H with ⟨n, rfl⟩
  intro r
  rcases n with ⟨n⟩
  . erw [pred_zero] at r
    exact not_le_of_lt (bot_lt_coe 0) r
  rw [pred_succ, coe_le_coe] at r
  exact not_le_of_lt (Nat.lt.step r) r

instance : PredOrder ℕ±∞ where
  pred := pred
  pred_le := pred_le
  min_of_le_pred := fun {m} hm {n} hmn => by
    have := pred_le_self _ hm
    sorry

  le_pred_of_lt := _
  le_of_pred_lt := _

end EENat
