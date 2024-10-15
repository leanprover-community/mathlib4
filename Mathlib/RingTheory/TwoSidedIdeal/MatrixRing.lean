import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Data.Matrix.Basis


section shouldbeelsewhere

variable {R : Type*} [Ring R] (t : TwoSidedIdeal R)

variable {M : Type*} [AddCommMonoid M] (r : AddCon M) {ι : Type*} (s : Finset ι) in
variable {t s} in
lemma AddCon.sum {f g : ι → M} (h : ∀ i ∈ s, r (f i) (g i)) :
    r (∑ i in s, f i) (∑ i in s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using r.refl 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact r.add (h _ (by simp)) <| ih fun i hi ↦ h _ (by aesop)

variable (ι : Type) {t s} in
lemma TwoSidedIdeal.sum {f g : ι → R} (h : ∀ i ∈ s, t.ringCon (f i) (g i)) :
    t.ringCon (∑ i in s, f i) (∑ i in s, g i) :=
  t.ringCon.toAddCon.sum h

variable (I : TwoSidedIdeal R)

variable (ι : Type) {t s} in
lemma TwoSidedIdeal.sum_mem (f : ι → R) (h : ∀ i ∈ s, f i ∈ I) : ∑ i in s, f i ∈ I := by
  simpa using I.sum _ h

end shouldbeelsewhere

variable (A : Type*) [Ring A] (ι : Type) [Fintype ι]

open Matrix

/--
If `I` is a two-sided-ideal of `A`, then `Mₙ(I) := {(xᵢⱼ) | ∀ i j, xᵢⱼ ∈ I}` is a two-sided-ideal of
`Mₙ(A)`.
-/
@[simps]
def TwoSidedIdeal.mapMatrix (I : TwoSidedIdeal A) : TwoSidedIdeal (Matrix ι ι A) := .mk
{
  r := fun X Y => ∀ i j, I.ringCon (X i j) (Y i j)
  iseqv :=
  { refl := fun X i j ↦ I.ringCon.refl (X i j)
    symm := fun h i j ↦ I.ringCon.symm (h i j)
    trans := fun h1 h2 i j ↦ I.ringCon.trans (h1 i j) (h2 i j) }
  mul' := by
    intro _ _ _ _ h h' i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [TwoSidedIdeal.rel_iff, ← Finset.sum_sub_distrib]
    apply I.sum_mem
    rintro k -
    rw [← TwoSidedIdeal.rel_iff]
    apply I.ringCon.mul (h _ _) (h' _ _)
  add' := fun {X X' Y Y'} h h' i j ↦ by
    simpa only [Matrix.add_apply] using I.ringCon.add (h _ _) (h' _ _)
}

@[simp]
lemma TwoSidedIdeal.mem_mapMatrix (I : TwoSidedIdeal A) (x) :
    x ∈ I.mapMatrix A ι ↔ ∀ i j, x i j ∈ I := Iff.rfl

/--
The two-sided-ideals of `A` corresponds bijectively to that of `Mₙ(A)`.
Given an ideal `I ≤ A`, we send it to `Mₙ(I)`.
Given an ideal `J ≤ Mₙ(A)`, we send it to `{x₀₀ | x ∈ J}`.
-/
@[simps]
def TwoSidedIdeal.equivRingConMatrix (oo : ι) :
    TwoSidedIdeal A ≃ TwoSidedIdeal (Matrix ι ι A) where
  toFun I := I.mapMatrix A ι
  invFun J := TwoSidedIdeal.mk'
    ((fun (x : (Matrix ι ι A)) => x oo oo) '' J)
    ⟨0, J.zero_mem, rfl⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, J.add_mem hx hy, rfl⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, J.neg_mem hx, rfl⟩)
    (by
      classical
      rintro x _ ⟨y, hy, rfl⟩
      exact ⟨Matrix.diagonal (fun _ ↦ x) * y, J.mul_mem_left _ _ hy, by simp⟩)
    (by
      classical
      rintro _ y ⟨x, hx, rfl⟩
      exact ⟨x * Matrix.diagonal (fun _ ↦ y), J.mul_mem_right _ _ hx, by simp⟩)
  right_inv J := SetLike.ext fun x ↦ by
    classical
    simp only [mem_mapMatrix]
    generalize_proofs h1 h2 h3 h4 h5
    constructor
    · intro h
      choose y hy1 hy2 using h
      rw [Matrix.matrix_eq_sum_stdBasisMatrix x]
      refine J.sum_mem _ _ fun i _ ↦ J.sum_mem _ _ fun j _ ↦ ?_
      suffices
          stdBasisMatrix i j (x i j) =
          stdBasisMatrix i oo 1 * y i j * stdBasisMatrix oo j 1 by
        rw [this]
        exact J.mul_mem_right _ _ (J.mul_mem_left _ _ <| hy1 _ _)
      ext a b
      by_cases hab : a = i ∧ b = j
      · rcases hab with ⟨ha, hb⟩
        subst ha hb
        simp only [stdBasisMatrix, and_self, ↓reduceIte, StdBasisMatrix.mul_right_apply_same,
          StdBasisMatrix.mul_left_apply_same, one_mul, mul_one]
        specialize hy2 a b
        simp only [sub_zero] at hy2
        exact hy2.symm
      · conv_lhs =>
          dsimp [stdBasisMatrix]
          rw [if_neg (by tauto)]
        rw [not_and_or] at hab
        rcases hab with ha | hb
        · rw [mul_assoc, Matrix.StdBasisMatrix.mul_left_apply_of_ne (h := ha)]
        · rw [Matrix.StdBasisMatrix.mul_right_apply_of_ne (hbj := hb)]
    · intro hx i j
      refine ⟨stdBasisMatrix oo i 1 * x * stdBasisMatrix j oo 1,
        J.mul_mem_right _ _ (J.mul_mem_left _ _ hx), ?_⟩
      simp only [StdBasisMatrix.mul_right_apply_same, StdBasisMatrix.mul_left_apply_same, one_mul,
        mul_one, sub_zero]
  left_inv I := SetLike.ext fun x ↦ by
    simp only
    constructor
    · intro h
      choose y hy1 hy2 using h
      simp only [sub_zero] at hy2
      exact hy2 ▸ hy1 _ _
    · intro h
      exact ⟨of fun _ _ => x, by simp [h], by simp⟩
