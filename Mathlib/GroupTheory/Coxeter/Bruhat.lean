import Mathlib.GroupTheory.Coxeter.inversion
import Mathlib.Order.Interval.Basic

open CoxeterSystem  List
open Classical (choose choose_spec)

section aux

section IsCoxeterGroup
open Classical

variable (G : Type) [Group G] [hG : IsCoxeterGroup G]

noncomputable def csOf := choice <| choose_spec <| (choose_spec hG.1)

noncomputable def indexOf := choose hG.1

-- namespace ReducedWord
-- noncomputable abbrev choose (w : G) :=
--   Classical.choose (exists_reduced_word (csOf G) w)

-- noncomputable abbrev choose' (w : G) :=
--   Classical.choose (exists_reduced_word' (csOf G) w)

-- abbrev choose_spec (w : G) := Classical.choose_spec (exists_reduced_word (csOf G) w)

-- abbrev choose_spec' (w : G) := Classical.choose_spec (exists_reduced_word' (csOf G) w)
-- end ReducedWord

end IsCoxeterGroup

end aux

section StrongExchange

variable {B : Type*}
variable {W : Type} [Group W] [IsCoxeterGroup W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

@[simp]
lemma nilIsReduced : cs.IsReduced [] := by simp [IsReduced]

@[simp]
lemma singletonIsReduced (h : l.length = 1) : cs.IsReduced l := by
  simp [IsReduced, h, length_eq_one_iff,List.length_eq_one]
  have := List.length_eq_one.1 h
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [ha]; simp⟩

lemma StrongExchange {l : List B} (ht : cs.IsReflection t) : ℓ (π l * t) < ℓ π l →
  ∃ l' : List B, π l' = π l * t ∧ ∃ i : Fin l.length, l' = l.eraseIdx i := by
    sorry

/-- If l is not a reduced word of w but a experssion, there exist a subword of l is also a
  expression of w. -/
lemma DeletionExchange {l : List B} (h : ¬IsReduced cs l) :
  ∃ i : Fin l.length, ∃ j : Fin i, π l = π (l.eraseIdx j).eraseIdx i := sorry

private lemma DeletionExchange_aux {l : List B} (h : ¬IsReduced cs l) :
  ∃ l', l' <+ l ∧ π l' = π l ∧ l'.length + 2 = l.length := sorry

/-- If l is not a reduced word of w but a experssion, there must exist a subword of l which
  is reduced word of w. -/
lemma DeletionExchange' {l : List B} (h : ¬IsReduced cs l) :
  ∃ l' : List B, l' <+ l ∧ π l' = π l ∧ IsReduced cs l' := by
  generalize hl : l.length = n
  revert l h
  induction' n using Nat.twoStepInduction with n h1 _ <;> intro l h llsucc
  · have : l = [] := List.eq_nil_of_length_eq_zero llsucc
    rw [this] at h
    exact (h <| nilIsReduced cs).elim
  · exact (h (singletonIsReduced cs llsucc)).elim
  · obtain ⟨ll, hll⟩ := DeletionExchange_aux cs h
    have lll : ll.length = n := by linarith
    by_cases hh : IsReduced cs ll
    · exact ⟨ll, ⟨hll.1, ⟨hll.2.1, hh⟩ ⟩⟩
    · obtain ⟨ll', hll'⟩ := h1 hh lll
      exact ⟨ll', ⟨hll'.1.trans hll.1, ⟨hll'.2.1.trans hll.2.1, hll'.2.2⟩ ⟩ ⟩

-- lemma llt_of_not_reduced {l : List B} {w : W} (hw : w = π l) (nred : ¬IsReduced cs l) :
--   ℓ w < l.length := sorry

end StrongExchange

namespace Bruhat

variable {B : Type*}
variable (W : Type) [Group W] [IsCoxeterGroup W]
variable {u v : W} {l l' : List (indexOf W)}

local prefix:100 "ℓ" => length (csOf W)
local prefix:100 "s" => simple (csOf W)
local prefix:100 "π" => wordProd (csOf W)

-- instance (cs : CoxeterSystem M W) : IsCoxeterGroup W where
--   nonempty_system := ⟨B, M, ⟨cs⟩ ⟩
section definition

def lt_adj  : W → W → Prop := fun u v =>
  (∃ t,  (csOf W).IsReflection t ∧ v = u * t) ∧ ℓ u < ℓ v

def lt_adj' : W → W → Prop := fun u v =>
  (∃ t, (csOf W).IsReflection t ∧ v = t * u) ∧ ℓ u < ℓ v

def lt := Relation.TransGen <| lt_adj W

def lt' := Relation.TransGen <| lt_adj' W

/-- the left Bruhat order is equivalent to the right Bruhat order-/
lemma lt_adj_iff_lt_adj' : lt_adj W u v ↔ lt_adj' W u v := by
  constructor <;> rintro ⟨⟨t, vut⟩, llt⟩
  · have : (csOf W).IsReflection (u * t * u⁻¹):=
      IsReflection.conj vut.1 u
    exact ⟨⟨u * t * u⁻¹, by simpa⟩, llt⟩
  · have subt : (csOf W).IsReflection (u⁻¹ * t * u) := by
      have := IsReflection.conj vut.1 u⁻¹
      simp at this
      assumption
    exact ⟨⟨u⁻¹ * t * u, ⟨subt, by group; exact vut.2⟩⟩, llt⟩

lemma lt_iff_lt' : lt W u v ↔ lt' W u v := by
  constructor <;> intro h
  · exact Relation.TransGen.mono (fun _ _ => (lt_adj_iff_lt_adj' W).1) h
  · exact Relation.TransGen.mono (fun _ _ => (lt_adj_iff_lt_adj' W).2) h

def le := Relation.ReflTransGen <| lt_adj W

def le' := Relation.ReflTransGen <| lt_adj' W

lemma le_iff_le' : le W u v ↔ le' W u v := sorry

lemma length_lt_of_lt : lt W u v → ℓ u < ℓ v := by
  intro hlt
  exact Relation.TransGen.trans_induction_on hlt (fun h => h.2)
    (fun _ _ h1 h2 => h1.trans h2)

lemma length_le_of_le : le W u v → ℓ u ≤ ℓ v := sorry

lemma lt_of_le_of_length_lt : le W u v → ℓ u < ℓ v → lt W u v := sorry

lemma eq_of_le_of_length_ge : le W u v → ℓ v ≤ ℓ u → u = v := fun hle lle => (by
    have : ¬Relation.TransGen (lt_adj W) u v := by
      contrapose! lle; exact length_lt_of_lt W lle
    exact ((or_iff_left this).1 (Relation.reflTransGen_iff_eq_or_transGen.1 hle)).symm )

instance : PartialOrder W where
  lt := lt W
  le := le W
  le_refl := fun _ => id Relation.ReflTransGen.refl
  le_trans := fun _ _ _ ha hb => Relation.ReflTransGen.trans ha hb
  le_antisymm := fun a b ha hb =>
    eq_of_le_of_length_ge W ha (length_le_of_le W hb)
  lt_iff_le_not_le := by
    intro a b;
    constructor <;> intro h
    · sorry
    · sorry

lemma covby_iff : u ⋖ v ↔ u < v ∧ ℓ u + 1 = ℓ v := by
  constructor <;> intro h
  · exact ⟨h.1, by have := h.2; sorry⟩
  · exact ⟨h.1, fun _ hw hwv => by linarith [length_lt_of_lt W hw, length_lt_of_lt W hwv]⟩

end definition

section SubwordProp

variable {ω : List (indexOf W)}
/-- If u ⋖ v, then exists reduced word of u is subword of reduced word of v. -/
lemma subword_of_lt_adj (veq : v = π ω) (h : lt_adj W u v) :
  ∃ ω' : List (indexOf W), (IsReduced (csOf W) ω' ∧ u = π ω') ∧ ω'.Sublist ω := by
    obtain ⟨ ⟨t, vut⟩, llt⟩ := h
    have vtu : v * t = u := by rw [←IsReflection.inv vut.1, vut.2]; group
    rw [←vtu, veq] at llt
    obtain ⟨ l, ⟨h1, ⟨i, hi⟩ ⟩ ⟩ := StrongExchange (csOf W) vut.1 llt
    by_cases lred : IsReduced (csOf W) l
    · refine ⟨l, ⟨⟨lred, by rw [h1, ←veq, vtu]⟩, ?_ ⟩⟩
      rw [hi]; exact eraseIdx_sublist ω i.1
    · let ll      := choose <| DeletionExchange' (csOf W) lred
      let ll_spec := choose_spec <| DeletionExchange' (csOf W) lred
      refine  ⟨ll, ⟨?_ , ?_ ⟩⟩
      · exact ⟨ll_spec.2.2, by rw [←vtu, ll_spec.2.1, h1, ←veq]⟩
      · exact ll_spec.1.trans (by rw [hi]; exact eraseIdx_sublist ω i.1)

/-- If u < v, then exists reduced word of u is subword of reduced word of v. -/
lemma subword_of_lt (veq : v = π ω) (h : u < v)  : ∃ ω' : List (indexOf W),
  (IsReduced (csOf W) ω' ∧ u = π ω') ∧ ω'.Sublist ω := by
    induction h  generalizing ω with
    | @single b hub => exact subword_of_lt_adj W veq hub
    | @tail b c _ hbc ih =>
      have := subword_of_lt_adj W veq hbc
      obtain ⟨l2, ⟨ll2, h2⟩ ⟩ := this
      obtain ⟨l1, ⟨ll1, h1⟩ ⟩ := ih  ll2.2
      exact ⟨l1, ⟨ll1, h1.trans h2⟩⟩

/-- If u ≤ v, then exists reduced word of u is subword of reduced word of v. -/
theorem subword_of_le (veq : v = π ω) (wred : (csOf W).IsReduced ω) : u ≤ v →
  ∃ ω' : List (indexOf W), (IsReduced (csOf W) ω' ∧ u = π ω') ∧ ω'.Sublist ω := by
    intro hle
    induction hle with
    | refl => exact ⟨ω, ⟨wred, veq⟩, by simp⟩
    | @tail b v hab hbc _ =>
      have : u < v := Relation.TransGen.tail' hab hbc
      exact subword_of_lt W veq this

-- def aux_aux : ∃ n,

lemma le_of_subword_aux {l l' : List (indexOf W)} {hl' : IsReduced (csOf W) l'}
  {hl : IsReduced (csOf W) l} (neq : l ≠ l') (lsub : l <+ l')
    : ∃ ll, IsReduced (csOf W) ll ∧ π l < π ll ∧ l.length + 1 = ll.length ∧ ll <+ l' := sorry

lemma le_of_subword {l l' : List (indexOf W)} {h : IsReduced (csOf W) l'} (lsub : l <+ l') :
  π l < π l' := by sorry

theorem SubwordProp : u ≤ v ↔ ∀ ω, v = π ω ∧ IsReduced (csOf W) ω → ∃ ω',
  v = π ω' ∧ IsReduced (csOf W) ω' ∧ ω' <+ ω := sorry

end SubwordProp

section otherProperty
#check Interval
/--Bruhat interval is finite because of Subword property. -/
-- lemma Interval.finite : sorry := sorry

abbrev BruhatInterval := NonemptyInterval W

def listInterval := {ω : List (indexOf W) | l <+ ω ∧ ω <+ l'}

instance BruhatInterval.finite (H : BruhatInterval W) : Fintype H := by
  -- have := sorry
  have : 0 < Nat.card H := sorry
  sorry


lemma inv_le_iff_le : u⁻¹ ≤ v⁻¹ ↔ u ≤ v := by sorry


theorem chainProp (hlt : u < v) : ∃ l : List W, Chain (· ⋖ ·) u (l.concat v) := sorry

lemma liftingProp {i : indexOf W} (hlt : u < v) (hirv : (csOf W).IsRightDescent v i)
  (nhiru : ¬(csOf W).IsRightDescent u i) : u ≤ s i * v ∧ s i * u ≤ v := sorry

instance : IsDirected W (· ≤ ·) where
  directed := sorry

end otherProperty

end Bruhat

-- section List
-- open Classical
-- def boolist (n : Nat) := Vector Bool n
-- variable {l : List α} {n : Nat} {bl : boolist n}

-- def tosublists {α : Type} (l : List α) : boolist l.length → List α :=
--   fun bl => (map (β := List α) (fun x => if x.2 then [x.1] else []) (zip l bl.1)).join

-- variable {l L : List α}

-- -- def sublist_lex := Finset.Colex {l : List α // l <+ L}
-- -- example : MulAut.conj g '' H
-- end List
