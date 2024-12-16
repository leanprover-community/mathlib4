import Mathlib.Algebra.Operad.Operad
import Mathlib.Tactic.Linarith.Frontend

/- An abstract clone is a set of operations that have composition and all projections.
  Here we define it with the multi-argument composition, typically called "superposition".
  Single-argument composition can be built from this using the identity `proj 1 0`. -/
class Clone (A : ℕ → Type*) extends Superposable A, OneGradedOne A where
  /- Superposition is associative -/
  superpose_assoc {n m k : ℕ} (a : A n) (bs : Fin n → A m) (cs : Fin m → A k) :
    (a ∘∈ bs) ∘∈ cs = a ∘∈ (fun i ↦ bs i ∘∈ cs)
  /- All projections are accessible -/
  proj (n : ℕ) (k : Fin n) : A n
  /- Projections are compatible on the left -/
  proj_left {n m : ℕ} (l : Fin n) (cs : Fin n → A m) : proj n l ∘∈ cs = cs l
  /- Projections are compatible on the right -/
  proj_right {n : ℕ} (c : A n) : c ∘∈ (fun i ↦ proj n i) = c
  /- The "1" element is the unary projection -/
  one_proj : 1 = proj 1 0

namespace Clone

variable {A : ℕ → Type*} [Clone A]

/- Pad a m-arity element of a clone to a larger arity, by adding projections that ignore
 the left- and right-most elements. -/
def clonePadTo {m : ℕ} (p : A m) (n : ℕ) (k : Fin n) : A (n+m-1) :=
  p ∘∈ fun i ↦ proj (n+m-1) ⟨k + i, Nat.lt_sub_of_add_lt (by omega)⟩

@[simp]
theorem clonePadTo_zero {m} (p : A m) (k : Fin 1) :
    clonePadTo p 1 k = (Nat.one_add_sub_one m).symm ▸ p := by
  apply eq_of_heq
  have := Nat.one_add_sub_one m
  nth_rewrite 2 [← proj_right p]
  simp only [heq_rec_iff_heq, clonePadTo, Fin.val_eq_zero, zero_add]
  congr!

/- Clones are defined with the multi-argument superpose operation, but this gives a natural
 one-argument composition operation. -/
def cloneCompose {n m : ℕ} (a : A n) (p : Fin n) (b : A m) : A (n + m - 1) :=
  a ∘∈ (
    fun k ↦ if hkp1 : k = p.1 then
        clonePadTo b n k
      else if hkp : k < p.1 then
        proj (n+m-1) ⟨k.val, Nat.lt_sub_of_add_lt (by omega)⟩
      else
        proj (n+m-1) ⟨k.val+m-1, tsub_lt_tsub_right_of_le
          (by omega)
          (Nat.add_lt_add_right k.isLt m)⟩
      )

@[simp]
theorem clone_proj_left {m n : ℕ} (l : Fin n) (cs : Fin n → A m) :
    proj n l ∘∈ cs = cs l :=
  proj_left l cs

@[simp]
theorem clone_proj_right {n : ℕ} (c : A n) : c ∘∈ (fun i ↦ proj n i) = c :=
  proj_right c

@[simp]
theorem clone_id_left {n : ℕ} (a : Fin 1 → A n) : 1 ∘∈ a = a 0 := by
  rw [one_proj]
  exact clone_proj_left 0 a

@[simp]
theorem cloneCompose_id {n : ℕ} (a : A n) (b : Fin n) : cloneCompose a b (1 : A 1) = a := by
  simp [cloneCompose, clonePadTo]

lemma add_add_sub_one_comm_of_Fin {x b : ℕ} (a c : ℕ) (h : x < b) :
  a + (b + c - 1) = a + b - 1 + c := by
    omega

lemma add_sub_one_comm_of_Fin {a : ℕ} (b c : ℕ) (x : Fin a) :
  a + b - 1 + c - 1 = a + c - 1 + b - 1 := by
    repeat rw [tsub_add_eq_add_tsub (le_add_right (Nat.one_le_of_lt x.isLt))]
    rw [Nat.add_right_comm]

/- The `cloneCompose` one-argument composition induced by a clone's
  superpose operation is associative. -/
theorem cloneCompose_assoc (a b c : Sigma A) (p1 : Fin a.fst) (p2 : Fin b.fst) :
  HEq (cloneCompose a.snd p1 (cloneCompose b.snd p2 c.snd))
  (cloneCompose (cloneCompose a.snd p1 b.snd) (p1.hAdd p2) c.snd) := by
    dsimp [cloneCompose]
    rw [superpose_assoc]
    have := add_add_sub_one_comm_of_Fin a.fst c.fst p2.2
    congr! 2 with _ x y hxy
    subst hxy
    simp only [Fin.val_inj, Fin.val_fin_lt]
    split
    next hyp1 =>
      simp only [hyp1, clonePadTo, superpose_assoc, Fin.hAdd]
      congr! 2 with k _ hk
      subst hk
      rw [clone_proj_left]
      simp only [Fin.val_inj, Fin.val_fin_lt]
      split
      next hkp2 =>
        subst hkp2
        simp only [dite_true, superpose_assoc, clone_proj_left, clonePadTo]
        congr! 4
        rw [add_assoc]
        congr!
      next hkp2 =>
        simp only [Fin.mk.injEq, add_right_inj, Fin.mk_lt_mk, add_lt_add_iff_left,
          Fin.val_fin_lt, Fin.val_inj, if_neg hkp2]
        split <;> simp only [clone_proj_left] <;> congr! 2
        next hkp2' =>
          rw [← Nat.add_sub_assoc, add_assoc]
          omega
    next hyp1 =>
      split
      next hxp1 =>
        have : x.1 < p1.1 + p2.1 := by exact Nat.lt_add_right p2.1 hxp1
        simp only [Fin.hAdd, clonePadTo, clone_proj_left, Fin.mk.injEq, this, this.ne, Fin.mk_lt_mk,
          dite_true, dite_false]
        congr!
      next hxp1 =>
        simp only [Fin.hAdd, clone_proj_left, Fin.mk.injEq, Fin.mk_lt_mk]
        rw [dif_neg, dif_neg]
        · congr! 2
          omega
        · omega
        · omega


/- The `cloneCompose` one-argument composition induced by a clone's superpose operation
  is commutative: it doesn't matter whether the p1'th or p2'th argument is provided first. -/
theorem cloneCompse_comm (a b c : Sigma A) (p1 p2 : Fin a.fst) (hp: p1 < p2)
  (p1' : Fin (a.fst + c.fst - 1)) (p2' : Fin (a.fst + b.fst - 1))
  (hp1' : p1.val = p1'.val) (hp2' : p2'.val = p2.val + b.fst - 1) :
  HEq (cloneCompose (cloneCompose a.snd p1 b.snd) p2' c.snd)
      (cloneCompose (cloneCompose a.snd p2 c.snd) p1' b.snd) := by
  have h := add_sub_one_comm_of_Fin b.fst c.fst p2
  rcases p1 with ⟨p1, hp1⟩
  rcases p2 with ⟨p2, hp2⟩
  rcases p1' with ⟨p1', _⟩
  rcases p2' with ⟨p2', _⟩
  subst hp2'
  subst hp1'
  simp only
  dsimp [cloneCompose]
  rw [superpose_assoc, superpose_assoc]
  congr! 2 with ⟨k, hk⟩ ⟨k2, hk2⟩ hkk2
  rw [Fin.mk.injEq] at hkk2
  subst hkk2
  dsimp [Fin.val, Fin.addNat, Fin.hAdd]
  replace hp : p1 < p2 := hp
  split
  next hkp1 =>
    subst k
    have hp1p2 : p1 ≠ p2 := hp.ne
    simp only [dif_neg hp1p2, dif_pos hp, clonePadTo, superpose_assoc]
    simp only [clone_proj_left, lt_self_iff_false, dite_false, dite_true]
    congr! with ⟨k2, hk2⟩ ⟨k3, hk3⟩ hk2k3
    have h₁ : p1 + k2 < p2 + b.fst - 1 := Nat.lt_sub_of_add_lt (by omega)
    simp only [h₁, h₁.ne, dite_true, dite_false]
    congr!
    rwa [Fin.mk.injEq] at hk2k3
  next =>
    split
    next hkp1 =>
      have h₁ : k < p2 := by omega
      have h₂ : k < p2 + b.fst - 1 := Nat.lt_sub_of_add_lt (by omega)
      simp only [clone_proj_left, hkp1, h₁, h₂, hkp1.ne, h₁.ne, h₂.ne, dite_true, dite_false]
      congr!
    next =>
      have hkp1 : k > p1 := by omega
      split
      next hkp2 =>
        simp only [clone_proj_left]
        have hkbp2 : k + b.fst - 1 = p2 + b.fst - 1 := by congr
        rw [dif_pos hkbp2]
        dsimp [clonePadTo]
        rw [superpose_assoc]
        congr! with ⟨k2, hk2⟩ ⟨k3, hk3⟩ hk2k3
        rw [Fin.mk.injEq] at hk2k3
        subst hk2k3
        rw [clone_proj_left]
        have hkk2p1 : k + k2 > p1 := Nat.lt_add_right k2 hkp1
        dsimp
        rw [dif_neg hkk2p1.ne.symm, dif_neg (Nat.lt_asymm hkk2p1)]
        congr! 2
        rw [tsub_add_eq_add_tsub (le_add_right (Nat.one_le_of_lt hkp1)),
          Nat.add_right_comm]
      next hkp2 =>
        split
        next hkp2 =>
          simp only [clone_proj_left]
          have hkbp2 : k + b.fst - 1 < p2 + b.fst - 1 := by
            apply tsub_lt_tsub_right_of_le
            · exact le_add_right (Nat.one_le_of_lt hkp1)
            · apply Nat.add_lt_add_right hkp2
          rw [dif_neg hkbp2.ne, dif_pos hkbp2, dif_neg hkp1.ne.symm, dif_neg (Nat.lt_asymm hkp1)]
          congr!
        next =>
          simp only [clone_proj_left]
          replace hkp2 : k > p2 := by omega
          have hkbp2 : k + b.fst - 1 > p2 + b.fst - 1 := by
            apply tsub_lt_tsub_right_of_le
            · exact le_add_right (Nat.one_le_of_lt hp)
            · apply Nat.add_lt_add_right hkp2
          have hkcp1 : k + c.fst - 1 > p1 := Nat.lt_sub_of_add_lt (by omega)
          rw [dif_neg hkbp2.ne.symm, dif_neg (Nat.lt_asymm hkbp2)]
          rw [dif_neg hkcp1.ne.symm, dif_neg (Nat.lt_asymm hkcp1)]
          congr! 3
          rw [tsub_add_eq_add_tsub (le_add_right (Nat.one_le_of_lt hkp1)),
            tsub_add_eq_add_tsub (le_add_right (Nat.one_le_of_lt hkp1)),
            Nat.add_right_comm]

set_option maxHeartbeats 400000

/- Every abstract clone naturally induces a (symmetric) operad. Currently this only shows the
 (nonsymmetric) `Operad` instance; extending it to `SymmOperad` requires some annoying lemmas with
  permutations. -/
instance clone_toSymmOperad [Clone A] : Operad A where
  compose := cloneCompose

  id_right := fun a p ↦ by
    dsimp [composeAt]
    congr!
    exact cloneCompose_id a.snd p

  id_left := fun a ↦ by
    dsimp [composeAt, cloneCompose]
    congr!
    · exact add_tsub_cancel_left 1 a.fst
    · simp

  assoc := fun a b c p1 p2 ↦ by
    dsimp [composeAt]
    congr 1
    · congr 1
      exact add_add_sub_one_comm_of_Fin _ _ p2.2
    · exact cloneCompose_assoc a b c p1 p2

  comm := fun {a} b c p1 p2 hp ↦ by
    dsimp [composeAt]
    congr 1
    · exact add_sub_one_comm_of_Fin _ _ p2
    · exact cloneCompse_comm a b c p1 p2 hp _ _ rfl rfl

  -- The following would be needed to improve this from `extends Operad` to `extends SymmOperad`
  -- act_at := fun i ↦ {
  --   smul := fun s x ↦ x ∘∈ fun k ↦ proj i (s k),
  --   one_smul := fun b ↦ proj_right b,
  --   mul_smul := fun x y b ↦ by
  --     dsimp [HSMul.hSMul]
  --     simp_rw [superpose_assoc, proj_left]
  --   }
  -- perm_left := fun s k x y ↦ by
  --   dsimp [SigmaMul_smul, MultiComposable.compose]
  --   rw [superpose_assoc]
  --   congr! with z
  --   rw [proj_left]
  --   split
  --   · split
  --     · dsimp [clonePadTo]
  --       congr!
  --       sorry
  --     · sorry
  --   · sorry
  -- perm_right := sorry

end Clone
