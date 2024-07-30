import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

variable {p : Nat}
variable {G : Type} [Group G]

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

#check AddAction.orbitEquivQuotientStabilizer
