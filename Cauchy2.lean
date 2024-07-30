import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Set.Card
import Mathlib.Tactic

variable {p : Nat}
variable {G : Type} [Group G]

lemma Set.Finite.ncard_pos_iff_nonempty {α : Type} {s : Set α} (hs : s.Finite) :
    0 < Set.ncard s ↔ s.Nonempty := by
  lift s to Finset α using hs
  simp

lemma Set.Finite.one_lt_ncard_iff_nontrivial {α : Type} {s : Set α} (hs : s.Finite) :
    1 < Set.ncard s ↔ s.Nontrivial := by
  lift s to Finset α using hs
  simp [Finset.one_lt_card_iff_nontrivial]

lemma mul_eq_one_iff_comm {a b : G} : a * b = 1 ↔ b * a = 1 := by
  rw [mul_eq_one_iff_inv_eq, mul_eq_one_iff_eq_inv, eq_comm]

lemma mul_eq_one_comm {a b : G} (h : a * b = 1) : b * a = 1 := by
  rwa [mul_eq_one_iff_comm]

def ZMod.prod (f : ZMod p → G) : G := List.range p |>.map (f ∘ Nat.cast) |>.prod

abbrev Diag (p : Nat) (G : Type) [Group G]  := { f : ZMod p → G // ZMod.prod f = 1 }

variable [Fact p.Prime]

lemma rotate_aux (f : Diag p G) : ∀ i, ZMod.prod (fun j ↦ f.1 (j + i)) = 1 := by
  rw [(ZMod.natCast_zmod_surjective).forall]
  intro i
  induction i; simp [f.2]; next n ih =>
  have : List.range p = List.range p.pred.succ := by rw [Nat.succ_pred]; exact Ne.symm (NeZero.ne' p)
  rw [ZMod.prod, this, List.range_succ, List.map_append, List.prod_append]
  apply mul_eq_one_comm
  apply Eq.trans _ ih
  rw [←List.prod_append, ←List.map_append, ZMod.prod, this, List.range_succ_eq_map,
    List.map_cons, List.prod_cons]
  simp
  congr 1
  · rw [Nat.cast_sub (Nat.Prime.one_le Fact.out), Nat.cast_one, add_comm _ 1,
      ←add_assoc, sub_add_cancel, ZMod.natCast_self p, zero_add]
  congr; ext j; simp; ring_nf

def rotate (i : ZMod p) (f : Diag p G) : Diag p G := ⟨fun j => f.1 (j + i), rotate_aux f i⟩

theorem rotate_zero (f : Diag p G) : rotate 0 f = f := by simp [rotate]

theorem rotate_rotate (i j : ZMod p) (f : Diag p G) :
  rotate (i + j) f = rotate i (rotate j f) := by simp [rotate, add_assoc]

instance : AddAction (ZMod p) (Diag p G) where
  vadd := rotate
  zero_vadd := rotate_zero
  add_vadd := rotate_rotate

@[simp]
theorem Diag.vadd_coeff (x : Diag p G) (i j : ZMod p) : (i +ᵥ x).1 j = x.1 (j + i) := rfl

theorem ZMod.card_orbit (X : Type*) [AddAction (ZMod p) X] (x : X) :
    Nat.card (AddAction.orbit (ZMod p) x) ∣ p := by
  rw [Nat.card_congr (AddAction.orbitEquivQuotientStabilizer (ZMod p) x)]
  simpa using AddSubgroup.card_quotient_dvd_card (AddAction.stabilizer (ZMod p) x)

theorem Diag_card : Nat.card (Diag p G) = (Nat.card G) ^ (p - 1) := by
  suffices e : Diag p G ≃ (Fin (p - 1) → G) by
    calc Nat.card (Diag p G)
        = Nat.card (Fin (p - 1) → G) := by exact Nat.card_congr e
      _ = (Nat.card G) ^ (p - 1)     := by rw [Nat.card_pi, Fin.prod_const]
  constructor
  case toFun => exact fun x i => x.1 i
  case invFun =>
    intro x
    sorry
  sorry
  sorry

instance : One (Diag p G) where
  one := ⟨Function.const _ 1, by simp [ZMod.prod, - Function.const_one]⟩

open AddAction in
theorem Group.Cauchy [Finite G] (hp : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by
  suffices ∃ g : G, g ≠ 1 ∧ g ^ p = 1 by
    obtain ⟨g, hg⟩ := this
    use g
    rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_prime Fact.out, orderOf_eq_one_iff] at hg
    tauto
  have aux (x) : x ∈ fixedPoints (ZMod p) (Diag p G) ↔ x.1 = Function.const _ (x.1 0) := by
    rw [mem_fixedPoints]
    constructor
    · intro h
      ext j
      specialize h j
      apply_fun (fun x ↦ x.1 0) at h
      simpa using h
    · intro h i
      ext j
      rw [Diag.vadd_coeff, h, h]
      rfl
  suffices (fixedPoints (ZMod p) (Diag p G)).Nontrivial by
    obtain ⟨x, hx, hx1⟩ := this.exists_ne 1
    use x.1 0
    constructor
    · contrapose! hx1
      ext i
      calc x.1 i = (i +ᵥ x).1 0 := by simp
               _ = x.1 0        := by rw [hx]
               _ = 1            := by exact hx1
    · have := x.2
      rw [aux] at hx
      rw [ZMod.prod, hx] at this
      simpa using this
  have h1 : 1 ∈ fixedPoints (ZMod p) (Diag p G) := by
    intro i; ext j
    simp; rfl
  suffices p ∣ (fixedPoints (ZMod p) (Diag p G)).ncard by
    rw [← (Set.toFinite _).one_lt_ncard_iff_nontrivial]
    calc 1 < p := Nat.Prime.one_lt Fact.out
         _ ≤ (fixedPoints (ZMod p) (Diag p G)).ncard := Nat.le_of_dvd ?_ this
    rw [(Set.toFinite _).ncard_pos_iff_nonempty]
    exact ⟨1, h1⟩
  let e := AddAction.selfEquivSigmaOrbits' (ZMod p) (Diag p G)
  sorry




