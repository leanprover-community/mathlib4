import Mathlib.Data.Int.Parity
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Parity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Perm.Cycle.Concrete

-- 2.1. One can associate an n x n matrix M_σ with a permutation σ ∈ S_n, by letting the entry at
-- (i, σ(i)) be 1 and letting all other entries be 0.
-- For example, the matrix corresponding to the permutation σ = c![1, 3, 2] ∈ S_3 would be
-- M_σ = !![0, 0, 1; 0, 1, 0; 1, 0 0]
-- Prove that, with this notation, M_στ = M_σ * M_τ for all σ,τ ∈ S_n, where the product on the
-- right is the ordinary product of matrices. [IV.4.13]
def exercise21 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of (λ i j => if j = σ i then 1 else 0)

lemma exercise21_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    exercise21 (τ * σ) = exercise21 σ * exercise21 τ := by
  ext i j
  simp [exercise21, Matrix.mul_apply, Finset.sum_ite]

-- 2.2. Prove that if d ≤ n, then S_n contains elements of order d. [§2.1]
@[simp]
lemma finRotate_pow_apply {n : ℕ} (k : ℕ) (i : Fin (n + 1)) :
    (finRotate (n + 1) ^ k) i = i + k := by
  induction' k with k IH
  · simp
  rw [pow_succ]
  simp [IH, add_assoc]

lemma orderOf_finRotate (n : ℕ) (npos : 0 < n) : orderOf (finRotate n) = n := by
  cases' n with n
  · exact absurd npos (lt_irrefl _)
  rw [orderOf_eq_iff npos, Nat.succ_eq_add_one]
  simp only [Equiv.ext_iff, finRotate_pow_apply, Nat.cast_add, Nat.cast_one, Equiv.Perm.coe_one,
             id_eq, add_right_eq_self, forall_const, ne_eq]
  constructor
  · rw [Fin.cast_nat_eq_last, Fin.last_add_one]
  · intros m hmn mpos
    simp [Fin.ext_iff, Nat.mod_eq_of_lt hmn, mpos.ne']

@[simp]
lemma extendDomain_pow {α' β' : Type _} (e : Equiv.Perm α') {p : β' → Prop} [DecidablePred p]
    (f : α' ≃ Subtype p) (n : ℕ) : (e.extendDomain f) ^ n = (e ^ n).extendDomain f := by
  induction' n with n IH
  · simp
  rw [pow_succ, IH, pow_succ]
  exact Equiv.Perm.extendDomain_trans f _ _

@[simp]
lemma extendDomain_eq_one_iff {α' β' : Type _} (e : Equiv.Perm α') {p : β' → Prop} [DecidablePred p]
    (f : α' ≃ Subtype p) : (e.extendDomain f) = 1 ↔ e = 1 := by
  constructor
  · intro H
    rw [Equiv.ext_iff] at H ⊢
    intro x
    simp only [Equiv.Perm.coe_one, id_eq] at H ⊢
    apply f.injective
    rw [Subtype.ext_iff, ←Equiv.Perm.extendDomain_apply_image e f x, H]
  · rintro rfl
    simp

@[simp]
lemma orderOf_extendDomain {α' β' : Type _} (e : Equiv.Perm α') {p : β' → Prop} [DecidablePred p]
    (f : α' ≃ Subtype p) : orderOf (e.extendDomain f) = orderOf e := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [extendDomain_pow, extendDomain_eq_one_iff]

lemma orderOf_cycleRange {n : ℕ} (d : Fin n) :
    orderOf (Fin.cycleRange d) = d + 1 := by
  rw [Fin.cycleRange]
  simpa using orderOf_finRotate _ Nat.succ_pos'

lemma exercise22 {n d : ℕ} (dpos : 0 < d) (hd : d ≤ n) : ∃ g : Equiv.Perm (Fin n), orderOf g = d :=
  if h : d = n then ⟨finRotate _, (orderOf_finRotate _ (dpos.trans_le hd)).trans h.symm⟩ else
  ⟨Fin.cycleRange ⟨d - 1, (Nat.pred_le _).trans_lt (lt_of_le_of_ne hd h)⟩, by
    rw [orderOf_cycleRange]
    exact Nat.succ_pred_eq_of_pos dpos⟩

section
set_option linter.unreachableTactic false
notation3 (prettyPrint := false) "cx["(l", "* => foldr (h t => List.cons h t) List.nil)"]" =>
  Cycle.formPerm (Cycle.ofList l) (by decide)
end

-- 2.4. Define a homomorphism D8 → S4 by labeling vertices of a square, as we did for a triangle in
-- §2.2. List the 8 permutations in the image of this homomorphism.
def exercise24' : DihedralGroup 4 → Equiv.Perm (Fin 4)
    | .r 0 => Equiv.refl _
    | .r 1 => cx[0, 3, 2, 1]
    | .r 2 => cx[0, 2] * cx[1, 3]
    | .r 3 => cx[0, 1, 2, 3]
    | .sr 0 => cx[1, 3]
    | .sr 1 => cx[0, 1] * cx[2, 3]
    | .sr 2 => cx[0, 2]
    | .sr 3 => cx[0, 3] * cx[1, 2]

lemma exercise24rr (x y : ZMod 4) :
    exercise24' (.r x * .r y) = exercise24' (.r x) * exercise24' (.r y) := by
  fin_cases x <;> fin_cases y <;> simp [exercise24']

lemma exercise24rsr (x y : ZMod 4) :
    exercise24' (.r x * .sr y) = exercise24' (.r x) * exercise24' (.sr y) := by
  fin_cases x <;> fin_cases y <;> simp [exercise24']

lemma exercise24srr (x y : ZMod 4) :
    exercise24' (.sr x * .r y) = exercise24' (.sr x) * exercise24' (.r y) := by
  fin_cases x <;> fin_cases y <;> simp [exercise24']

lemma exercise24srsr (x y : ZMod 4) :
    exercise24' (.sr x * .sr y) = exercise24' (.sr x) * exercise24' (.sr y) := by
  fin_cases x <;> fin_cases y <;> simp [exercise24']

def exercise24 : DihedralGroup 4 →* Equiv.Perm (Fin 4) where
  toFun := exercise24'
  map_one' := rfl
  map_mul' := by
    rintro (⟨_⟩|⟨_⟩) (⟨_⟩|⟨_⟩)
    · exact exercise24rr _ _
    · exact exercise24rsr _ _
    · exact exercise24srr _ _
    · exact exercise24srsr _ _

-- 2.5. Describe generators and relations for all dihedral groups D_2n.
-- (Hint: Let x be the reflection about a line through the center of a regular n-gon and a vertex,
-- and let y be the counterclockwise rotation by 2π/n. The group D_2n will be generated by x and y,
-- subject to three relations. To see that these relations really determine D_2n, use them to show
-- that any product x^i_1 * y^i_2 * x^i_3 * y^i_4 * ... = x^i * y^j for some i, j with
-- 0 ≤ i ≤ 1, 0 ≤ j ≤ n)  [8.4, §IV.2.5]
namespace exercise25

variable (n : ℕ)

def x : DihedralGroup n := .sr 0
def y : DihedralGroup n := .r 1

lemma relx : x n * x n = 1 := DihedralGroup.sr_mul_self _

lemma relx_inv : (x n)⁻¹ = x n := by
  rw [inv_eq_iff_mul_eq_one, relx]

lemma rely : y n ^ n = 1 := DihedralGroup.r_one_pow_n

lemma rely_inv (hn : n ≠ 0) : (y n)⁻¹ = y n ^ (n - 1) := by
  rw [inv_eq_iff_mul_eq_one, ←pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), rely]

lemma relxy : (y n)⁻¹ * x n = x n * y n := by
  rw [←relx_inv, ←mul_inv_rev, relx_inv, x, y, DihedralGroup.sr_mul_r, zero_add]
  rfl

lemma relxy_pow (k : ℕ) : (y n ^ k)⁻¹ * x n = x n * y n ^ k := by
  induction' k with k IH
  · simp
  · rw [pow_succ, mul_inv_rev, mul_assoc, relxy, ←mul_assoc, IH, mul_assoc, ←pow_succ, ←pow_succ']

lemma relx' (k : ℕ) : x n ^ k = x n ^ (k % 2) := by
  rw [←Nat.div_add_mod k 2, pow_add, pow_mul, pow_two, relx, one_pow, one_mul,
      Nat.div_add_mod]

lemma rely' (k : ℕ) : y n ^ k = y n ^ (k % n) := by
  rw [←Nat.div_add_mod k n, pow_add, pow_mul, rely, one_pow, one_mul,
      Nat.div_add_mod]

lemma relxy' (k : ℕ) (hn : n ≠ 0) : y n ^ k * x n = x n * y n ^ (n - k % n) := by
  rw [rely']
  generalize hk : k % n = m
  have hm : m < n := hk.ge.trans_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
  clear hk k
  induction' m with m IH
  · simp [rely]
  · specialize IH ((Nat.lt_succ_self _).trans hm)
    rw [pow_succ, mul_assoc, IH, pow_sub, pow_sub, rely, one_mul, one_mul, pow_succ', mul_inv_rev,
        ←mul_assoc, mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_cancel_right, ←inv_mul_eq_iff_eq_mul,
        relx_inv, ←mul_assoc, ←relxy, mul_assoc, relx, mul_one]
    · exact Nat.succ_le_of_lt ((Nat.lt_succ_self _).trans hm)
    · exact (Nat.le_succ m).trans hm.le

lemma reduction (xyi : List (ℕ × ℕ)) (hn : n ≠ 0) : ∃ (i j : ℕ), i ≤ 1 ∧ j ≤ (n - 1) ∧
    xyi.foldr (λ ij e => e * x n ^ ij.1 * y n ^ ij.2) 1 = x n ^ i * y n ^ j := by
  have npos : 0 < n := Nat.pos_of_ne_zero hn
  induction' xyi with xy xys IH
  · refine' ⟨0, 0, Nat.zero_le _, Nat.zero_le _, _⟩
    simp
  · obtain ⟨i, j, _, _, IH⟩ := IH
    simp_rw [List.foldr, IH]
    rw [relx' _ xy.fst]
    generalize hxy1 : (xy.fst % 2) = xyf
    have : xyf ≤ 1 := by rw [←hxy1]; exact Nat.le_of_lt_succ (Nat.mod_lt _ zero_lt_two)
    interval_cases i <;> interval_cases xyf
    · refine' ⟨0, (j + xy.snd) % n, zero_le_one, Nat.le_pred_of_lt (Nat.mod_lt _ npos), _⟩
      simp [←pow_add, rely']
    · simp only [pow_zero, one_mul, pow_one, relxy' _ _ hn, ge_iff_le]
      refine' ⟨1, (n - j % n + xy.snd) % n, le_rfl, Nat.le_pred_of_lt (Nat.mod_lt _ npos), _⟩
      rw [mul_assoc, ←pow_add, rely', pow_one]
    · simp only [pow_zero, one_mul, pow_one, relxy' _ _ hn, ge_iff_le]
      refine' ⟨1, (j + xy.snd) % n, le_rfl, Nat.le_pred_of_lt (Nat.mod_lt _ npos), _⟩
      rw [mul_one, mul_assoc, ←pow_add, rely', pow_one]
    · refine' ⟨0, (n - j % n + xy.snd) % n, zero_le_one, Nat.le_pred_of_lt (Nat.mod_lt _ npos), _⟩
      rw [pow_one, mul_assoc _ _ (x n), relxy' _ _ hn, ←mul_assoc, relx, one_mul, pow_zero, one_mul,
          ←pow_add, rely']

end exercise25

-- 2.6.  For every positive integer n construct a group containing two elements g, h.
-- such that |g| = 2, |h| = 2, and |gh| = n. (Hint: For n > 1, D_2n will do.) [§1.6]
open Multiplicative in
lemma exercise26one :
    ∃ g h : Multiplicative (Fin 2), orderOf g = 2 ∧ orderOf h = 2 ∧ orderOf (g * h) = 1 := by
  refine' ⟨ofAdd 1, ofAdd 1, _⟩
  simp_all [addOrderOf_eq_iff]

lemma exercise26 {n : ℕ} : ∃ (G : Type) (hG : Group G) (g h : G),
    orderOf g = 2 ∧ orderOf h = 2 ∧ orderOf (g * h) = n := by
  refine' ⟨DihedralGroup n, inferInstance, .sr 0, .sr 0 * .r 1, _, _, _⟩
  · simp [orderOf_eq_iff]
  · simp [orderOf_eq_iff]
  · simp

-- 2.7. Find all elements of D_2n that commute with every other element.
-- (The parity of n plays a role.)
/- Reduction of a D_2n to the powers of reflection and rotation. -/
def dihed_reduction' {n : ℕ} : DihedralGroup n.succ → ZMod 2 × ZMod n.succ
  | .sr k => (1, k)
  | .r k => (0, -k)

lemma dihed_reduction'_injective (n : ℕ) : Function.Injective (dihed_reduction' (n := n)) := by
  rintro (_|_) (_|_) <;> simp [dihed_reduction']

def twist' (n : ℕ) : ZMod 2 → MulAut (Multiplicative (ZMod n)) := fun x =>
  if x = 0 then 1 else (AddEquiv.toMultiplicative (AddEquiv.neg _))

def Multiplicative.recOn {G : Type _} {motive : Multiplicative G → Sort _}
    (h : ∀ g : G, motive (Multiplicative.ofAdd g)) (g : Multiplicative G) : motive g :=
  h (Multiplicative.toAdd g)

@[simp] lemma AddEquiv.toMultiplicative_neg (G : Type _) [SubtractionCommMonoid G] :
    AddEquiv.toMultiplicative (AddEquiv.neg G) = MulEquiv.inv (Multiplicative G) := rfl

@[simp] lemma MulEquiv.inv_mul_inv (G : Type _) [DivisionCommMonoid G] :
  MulEquiv.inv G * MulEquiv.inv G = 1 := by ext; simp

@[simp] lemma AddEquiv.neg_mul_neg (G : Type _) [SubtractionCommMonoid G] :
  AddEquiv.neg G * AddEquiv.neg G = 1 := by ext; simp

def twist (n : ℕ) : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod n)) where
  toFun x := twist' n (Multiplicative.toAdd x)
  map_one' := by
    ext
    simp [twist']
  map_mul' := by
    intros x y
    induction' x using Multiplicative.recOn with x
    induction' y using Multiplicative.recOn with y
    fin_cases x <;>
    fin_cases y <;>
    simp [twist']

def dihed_reduction {n : ℕ} : DihedralGroup n.succ →
  SemidirectProduct (Multiplicative (ZMod n.succ)) (Multiplicative (ZMod 2)) (twist _) := fun
    | .r k => ⟨Multiplicative.ofAdd k, Multiplicative.ofAdd 0⟩
    | .sr k => ⟨Multiplicative.ofAdd (-k), Multiplicative.ofAdd 1⟩

@[simps]
def dihed_semidirect_equiv (n : ℕ) : DihedralGroup n.succ ≃*
    SemidirectProduct (Multiplicative (ZMod n.succ)) (Multiplicative (ZMod 2)) (twist _) where
  toFun := dihed_reduction
  invFun := fun
    | .mk i j => (.r 1) ^ (Multiplicative.toAdd i).val * (.sr 0) ^ ((Multiplicative.toAdd j).val)
  left_inv := by
    intro x
    have : ZMod.val (n := 2) 1 = 1 := rfl
    cases' x
    · rw [dihed_reduction]
      simp
    · simp [this, twist, twist', dihed_reduction]
  right_inv := by
    intro x
    have h0 : ZMod.val (n := 2) 0 = 0 := rfl
    have h1 : ZMod.val (n := 2) 1 = 1 := rfl
    cases' x with i j
    induction' i using Multiplicative.recOn with i
    induction' j using Multiplicative.recOn with j
    fin_cases j
    · simp [h0, dihed_reduction]
    · simp [dihed_reduction, twist, twist', h1]
  map_mul' := by
    rintro (_|_) (_|_)
    · simp [dihed_reduction]
    · simp [dihed_reduction, ←mul_assoc, div_eq_mul_inv]
    · simp only [dihed_reduction, DihedralGroup.sr_mul_r, ofAdd_zero, ofAdd_add, map_mul,
        mul_inv_rev, SemidirectProduct.mk_eq_inl_mul_inr, map_one, mul_one, ofAdd_neg, map_inv]
      rw [SemidirectProduct.ext_iff]
      simp [twist, twist', mul_comm]
    · simp only [dihed_reduction, DihedralGroup.sr_mul_sr, ofAdd_zero, ofAdd_add, map_mul,
        mul_inv_rev, SemidirectProduct.mk_eq_inl_mul_inr, map_one, mul_one, ofAdd_neg, map_inv]
      rw [SemidirectProduct.ext_iff]
      suffices : (1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1
      · simpa [twist, twist', mul_comm, div_eq_mul_inv] using this
      rw [eq_comm, ←ofAdd_add, ofAdd_eq_one]
      rfl

lemma dihed_center_even_four_le (k : ℕ) (g : DihedralGroup (2 * k + 4)) :
    (∀ h, g * h = h * g) ↔ g = 1 ∨ g = .r (k + 2) := by
  have h2 : ZMod.val (n := 2 * k + 4) 2 = 2
  · rw [←Nat.cast_two (R := ZMod _), ZMod.val_nat_cast, Nat.mod_eq_of_lt (a := 2)]
    simp [Nat.lt_succ_iff, Nat.succ_le_succ_iff]
  have hk : (k : ZMod (2 * k + 4)).val = k
  · rw [ZMod.val_cast_of_lt]
    simp [Nat.lt_succ_iff, two_mul, add_assoc]
  have hkm : (k + 2) % (2 * k + 4) = k + 2
  · refine' Nat.mod_eq_of_lt _
    rw [Nat.lt_succ_iff]
    simp [two_mul, Nat.succ_le_succ_iff, add_assoc]
  constructor
  · contrapose!
    intro H
    rcases g with (g|g)
    · refine' ⟨.sr 0, _⟩
      simp only [DihedralGroup.r_mul_sr, zero_sub, DihedralGroup.sr_mul_r, zero_add, ne_eq,
        DihedralGroup.sr.injEq, ZMod.neg_eq_self_iff, not_or]
      simp only [DihedralGroup.one_def, ne_eq, DihedralGroup.r.injEq] at H
      contrapose! H
      intro hg
      specialize H hg
      have : ZMod.val g = k + 2
      · rw [←mul_right_inj' (two_ne_zero : (2 : ℕ) ≠ 0), H, mul_add]
      refine' ZMod.val_injective (2 * k + 4) _
      rw [this, ZMod.val_add, h2, hk, hkm]
    · refine' ⟨.r 1, _⟩
      simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, ne_eq, DihedralGroup.sr.injEq]
      rw [eq_comm, sub_eq_iff_eq_add, eq_comm, add_assoc, add_right_eq_self, ←ZMod.val_eq_zero,
          ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.one_mod, Nat.mod_eq_of_lt]
      · exact two_ne_zero
      · simp
  · rintro (rfl|rfl)
    · simp
    rintro (h|h)
    · simp [add_comm]
    · simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq]
      rw [sub_eq_iff_eq_add, eq_comm, add_assoc, add_right_eq_self, add_eq_zero_iff_eq_neg,
          eq_comm, ZMod.neg_eq_self_iff, ZMod.val_add, h2, hk, hkm, mul_add]
      exact Or.inr rfl

lemma dihed_center_odd_three_le (k : ℕ) (g : DihedralGroup (2 * k + 3)) :
    (∀ h, g * h = h * g) ↔ g = 1 := by
  constructor
  · contrapose!
    intro H
    rcases g with (g|g)
    · refine' ⟨.sr 0, _⟩
      simp only [DihedralGroup.r_mul_sr, zero_sub, DihedralGroup.sr_mul_r, zero_add, ne_eq,
        DihedralGroup.sr.injEq, ZMod.neg_eq_self_iff, not_or]
      simp only [DihedralGroup.one_def, ne_eq, DihedralGroup.r.injEq] at H
      refine' ⟨H, _⟩
      intro H
      suffices : Odd (2 * ZMod.val g)
      · simp at this
      rw [H]
      refine' ⟨k + 1, _⟩
      simp [mul_add, add_assoc]
    · refine' ⟨.r 1, _⟩
      simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, ne_eq, DihedralGroup.sr.injEq]
      rw [eq_comm, sub_eq_iff_eq_add, eq_comm, add_assoc, add_right_eq_self, ←ZMod.val_eq_zero,
          ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.one_mod, Nat.mod_eq_of_lt]
      · exact two_ne_zero
      · simp
  · simp (config := {contextual := true})

lemma dihed_center_zero (g : DihedralGroup 0) :
    (∀ h, g * h = h * g) ↔ g = 1 := by
  constructor
  · contrapose!
    intro H
    rcases g with (g|g)
    · refine' ⟨.sr 0, _⟩
      simp only [DihedralGroup.r_mul_sr, zero_sub, DihedralGroup.sr_mul_r, zero_add, ne_eq,
        DihedralGroup.sr.injEq, ZMod.neg_eq_self_iff, not_or]
      simp only [DihedralGroup.one_def, ne_eq, DihedralGroup.r.injEq] at H
      simp [H]
    · refine' ⟨.r 1, _⟩
      simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, ne_eq, DihedralGroup.sr.injEq]
      rw [eq_comm, sub_eq_iff_eq_add, eq_comm, add_assoc, add_right_eq_self, ←ZMod.val_eq_zero]
      simp
  · simp (config := {contextual := true})

lemma dihed_center_one_eq_top (g : DihedralGroup 1) :
    ∀ h, g * h = h * g := by
  rintro (h|h) <;> rcases g with (g|g) <;> simp

lemma dihed_center_two_eq_top (g : DihedralGroup 2) :
    ∀ h, g * h = h * g := by
  rintro (h|h) <;> rcases g with (g|g)
  · simp [add_comm]
  · simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq]
    rw [sub_eq_add_neg, add_left_cancel_iff, eq_comm, ZMod.neg_eq_self_iff]
    fin_cases h <;> norm_num
  · simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq]
    rw [sub_eq_add_neg, add_left_cancel_iff, ZMod.neg_eq_self_iff]
    fin_cases g <;> norm_num
  · simp [sub_eq_sub_iff_add_eq_add, ←two_mul]

-- 2.8. Find the orders of the groups of symmetries of the five `platonic solids'.

-- 2.9. Verify carefully that `congruence mod n' is an equivalence relation.
def Nat.ModSetoid (n : ℕ) : Setoid ℕ where
  r x y := x ≡ y [MOD n]
  iseqv := by
    constructor
    · intro x
      rw [ModEq]
    · intro x y
      rw [ModEq, ModEq]
      exact Eq.symm
    · intro x y z
      rw [ModEq, ModEq, ModEq]
      exact Eq.trans

def Int.ModSetoid (n : ℤ) : Setoid ℤ where
  r x y := x ≡ y [ZMOD n]
  iseqv := by
    constructor
    · intro x
      rw [ModEq]
    · intro x y
      rw [ModEq, ModEq]
      exact Eq.symm
    · intro x y z
      rw [ModEq, ModEq, ModEq]
      exact Eq.trans

-- 2.10. Prove that Z/nZ consists of precisely `n` elements.
-- `ZMod.card` proves this by construction
lemma exercise210 (n : ℕ) : Fintype.card (ZMod n.succ) = n.succ := by
  simp only [ZMod.card]

-- 2.11. Prove that the square of every odd integer is congruent to 1 modulo 8. [§VII.5.1]
lemma Int.one_emod (n : ℤ) (hn : |n| ≠ 1): 1 % n = 1 := by
  -- have : (1 : ℤ) = ofNat 1 := rfl
  rcases eq_or_ne n 0 with rfl|hn'
  · simp
  rw [←Int.emod_abs, Int.emod_eq_of_lt zero_le_one]
  rw [ne_eq, ←abs_eq_zero, abs_eq_natAbs] at hn'
  rw [abs_eq_natAbs] at hn ⊢
  rcases h : natAbs n with _|_|_
  · simp [h] at hn'
  · simp [h] at hn
  · simp

lemma Int.pow_emod (x n : ℤ) (k : ℕ) : x ^ k % n = (x % n) ^ k % n := by
  induction' k with k IH
  · simp
  · simp [pow_succ', mul_emod, IH]

lemma Nat.odd_mod_even_iff {k n : ℕ} (hn : Even n) :
    Odd (k % n) ↔ Odd k := by
  rcases hn with ⟨n, rfl⟩
  rw [←two_mul]
  constructor
  · rintro ⟨x, hx⟩
    rw [←Nat.div_add_mod k (2 * n), add_comm, odd_add, hx, mul_assoc]
    simp
  · rintro ⟨x, hx⟩
    rcases eq_or_ne n 0 with rfl|hn
    · simp [hx]
    rw [hx]
    refine' ⟨x % n, _⟩
    have : 1 % (2 * n) = 1
    · rw [Nat.mod_eq_of_lt]
      rw [two_mul]
      exact Nat.one_lt_bit0 hn
    rw [←Nat.mul_mod_mul_left, Nat.add_mod_of_add_mod_lt, this]
    rw [this]
    have hx : 2 * x % (2 * n) < 2 * n := Nat.mod_lt _ (mul_pos zero_lt_two (Nat.pos_of_ne_zero hn))
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt hx
    rw [add_right_comm] at hl
    refine' lt_of_lt_of_le _ hl.ge
    rw [lt_add_iff_pos_right]
    contrapose! hl
    rw [nonpos_iff_eq_zero] at hl
    subst l
    rw [mul_mod_mul_left, add_zero]
    have : Even (2 * n) := by simp
    intro H
    rw [H, even_iff_not_odd] at this
    exact this ⟨_, rfl⟩

lemma Nat.even_mod_even_iff {k n : ℕ} (hn : Even n) :
    Even (k % n) ↔ Even k := by
  rw [even_iff_not_odd, odd_mod_even_iff hn, even_iff_not_odd]

theorem Odd.sub_even_iff {a b : ℤ} (hb : Even b) : Odd (a - b) ↔ Odd a :=
⟨fun h ↦ by convert h.add_even hb; simp, fun ha ↦ sub_even ha hb⟩

lemma Int.odd_mod_even_iff {k n : ℤ} (hn : Even n) :
    Odd (k % n) ↔ Odd k := by
  rw [← sub_eq_of_eq_add $ (Int.emod_add_ediv' k n).symm, Odd.sub_even_iff]
  rw [even_mul]
  exact Or.inr hn

lemma exercise211 (n : ℤ) (hn : Odd n) : n ^ 2 ≡ 1 [ZMOD 8] := by
  rw [Int.ModEq, Int.pow_emod]
  generalize hk : n % 8 = k
  have hk0 : 0 ≤ k
  · rw [←hk]
    exact Int.emod_nonneg _ (by norm_num)
  have hk8 : k < 8
  · rw [←hk]
    refine Int.emod_lt_of_pos _ (by norm_num)
  have ho : Odd (n % 8)
  · rwa [Int.odd_mod_even_iff]
    simp
  interval_cases k <;> try { simp [hk] at ho } <;> simp

-- 2.12. Prove that there are no integers a, b, c such that a^2 + b^2 = 3c^2.
-- (Hint: By studying the equation [a]^2_4 + [b]^2_4 = 3[c]^2_4 in Z/4Z, show that a, b, c would all
-- have to be even. Letting a = 2k, b = 2l, c = 2m, you would have k^2 + l^2 = 3^m2.
--- What's wrong with that?)
lemma sq_zmod_four (a : ZMod 4) : a ^ 2 = 0 ∨ a ^ 2 = 1 := by
  cases' a with a
  interval_cases a
  · simp
  · simp
  · rw [Fin.ext_iff, pow_two, Fin.mul_def]
    simp
  · rw [Fin.ext_iff, pow_two, Fin.mul_def]
    norm_num

lemma sq_zmod_four_eq_zero_iff (a : ℕ) : (a : ZMod 4) ^ 2 = 0 ↔ Even a := by
  constructor
  · intro h
    rw [pow_two] at h
    have : (a : ZMod 4) = 0 ∨ (a : ZMod 4) = 2
    · cases' ha : (a : ZMod 4) with k
      interval_cases k
      · simp
      · rw [ha, Fin.ext_iff] at h
        simp at h
      · rw [Fin.ext_iff, Fin.ext_iff]
        simp
      · rw [ha, Fin.ext_iff, Fin.mul_def] at h
        simp at h
    rw [show (0 : ZMod 4) = (0 : ℕ) from rfl, show (2 : ZMod 4) = (2 : ℕ) from rfl] at this
    rw [ZMod.nat_cast_eq_nat_cast_iff', ZMod.nat_cast_eq_nat_cast_iff'] at this
    cases' this with hc hc
    · simp only [Nat.cast_ofNat, Nat.zero_mod, ←Nat.dvd_iff_mod_eq_zero] at hc
      obtain ⟨k, rfl⟩ := hc
      refine' ⟨2 * k, _⟩
      rw [←two_mul, ←mul_assoc]
      norm_num
    · zify at hc
      simp only [Nat.cast_ofNat, Int.emod_eq_emod_iff_emod_sub_eq_zero,
          EuclideanDomain.mod_eq_zero] at hc
      obtain ⟨k, hk⟩ := hc
      rw [sub_eq_iff_eq_add] at hk
      rw [←Int.even_coe_nat, hk]
      refine' ⟨2 * k + 1, _⟩
      ring
  · rintro ⟨k, rfl⟩
    simp [←two_mul, mul_pow, show (2 : ZMod 4) ^ 2 = 0 from rfl]

lemma Int.sq_zmod_four_eq_zero_iff (a : ℤ) : (a : ZMod 4) ^ 2 = 0 ↔ Even a := by
  constructor
  · intro h
    rw [pow_two] at h
    have : (a : ZMod 4) = 0 ∨ (a : ZMod 4) = 2
    · cases' ha : (a : ZMod 4) with k
      interval_cases k
      · simp
      · rw [ha, Fin.ext_iff] at h
        simp at h
      · rw [Fin.ext_iff, Fin.ext_iff]
        simp
      · rw [ha, Fin.ext_iff, Fin.mul_def] at h
        simp at h
    rw [show (0 : ZMod 4) = (0 : ℤ) from rfl, show (2 : ZMod 4) = (2 : ℤ) from rfl] at this
    rw [ZMod.int_cast_eq_int_cast_iff', ZMod.int_cast_eq_int_cast_iff'] at this
    cases' this with hc hc
    · simp only [Nat.cast_ofNat, EuclideanDomain.zero_mod, EuclideanDomain.mod_eq_zero] at hc
      obtain ⟨k, rfl⟩ := hc
      refine' ⟨2 * k, _⟩
      rw [←two_mul, ←mul_assoc]
      norm_num
    · simp only [Nat.cast_ofNat, Int.emod_eq_emod_iff_emod_sub_eq_zero,
        EuclideanDomain.mod_eq_zero] at hc
      obtain ⟨k, hk⟩ := hc
      rw [sub_eq_iff_eq_add] at hk
      rw [hk]
      refine' ⟨2 * k + 1, _⟩
      ring
  · rintro ⟨k, rfl⟩
    simp [←two_mul, mul_pow, show (2 : ZMod 4) ^ 2 = 0 from rfl]

lemma exercise212 (a b c : ℤ) : a ^ 2 + b ^ 2 ≠ 3 * c ^ 2 ∨ a = 0 ∧ b = 0 ∧ c = 0 := by
  by_cases h0 : a = 0 ∧ b = 0 ∧ c = 0
  · exact Or.inr h0
  simp at h0
  refine' Or.inl _
  have key : ∀ (a b c : ℕ), a ^ 2 + b ^ 2 = 3 * c ^ 2 → (a / 2) ^ 2 + (b / 2) ^ 2 = 3 * (c / 2) ^ 2
  · intro a b c H
    have H' := congr_arg (λ x : ℕ => ((x : ℤ) : ZMod 4)) H
    cases' sq_zmod_four a with ha ha <;>
    cases' sq_zmod_four b with hb hb <;>
    cases' sq_zmod_four c with hc hc <;>
    try { simp [ha, hb, hc] at H' }
    rw [sq_zmod_four_eq_zero_iff] at ha hb hc
    obtain ⟨k, rfl⟩ := ha
    obtain ⟨l, rfl⟩ := hb
    obtain ⟨m, rfl⟩ := hc
    rw [←two_mul, ←two_mul, ←two_mul] at H ⊢
    rw [mul_pow, mul_pow, mul_pow, ←mul_add, mul_left_comm] at H
    simp only [mul_eq_mul_left_iff, or_false] at H
    simp [H]
  rw [←Int.natAbs_pow_two a, ←Int.natAbs_pow_two b, ←Int.natAbs_pow_two c, ←Nat.cast_pow,
      ←Nat.cast_pow, ←Nat.cast_pow, ←Nat.cast_add, ←show (3 : ℕ) = (3 : ℤ) from rfl,
      ←Nat.cast_mul, ne_eq, Nat.cast_inj]
  replace h0 : a.natAbs = 0 → b.natAbs = 0 → c.natAbs ≠ 0
  · simpa using h0
  generalize a.natAbs = x at *
  generalize b.natAbs = y at *
  generalize c.natAbs = z at *
  intro H
  induction' z using Nat.strongInductionOn with n IH generalizing x y
  cases' lt_or_le n 2 with hn hn
  · interval_cases n
    · simp only [ne_eq, zero_pow', mul_zero, add_eq_zero, zero_lt_two, pow_eq_zero_iff] at H
      simp [H.left, H.right] at h0
    · simp only [one_pow, mul_one] at H
      have hx : x ≤ 3
      · rw [←H]
        exact (Nat.le_self_pow two_ne_zero _).trans le_self_add
      have hy : y ≤ 3
      · rw [←H]
        exact (Nat.le_self_pow two_ne_zero _).trans le_add_self
      interval_cases x <;>
      interval_cases y <;>
      norm_num at H
  refine' IH _ (Nat.div_lt_self (zero_lt_two.trans_le hn) one_lt_two) _ _ _ (key _ _ _ H)
  intros
  exact (Nat.div_pos hn zero_lt_two).ne'

-- 2.13. Prove that if gcd(m, n) = 1, then there exist integers a and b such that am + bn = 1.
-- (Use Corollary 2.5.) Conversely, prove that if am + bn = 1 for some integers a and b,
-- then god(m, n) = 1. [2.15, §V.2.1, V.2.4]

-- Proposition 2.3. The order of [m]_n in Z/nZ is 1 if n | m, and more generally |[m]_n| =
-- n / gcd m n
lemma proposition23 {n : ℕ} (hn : n ≠ 0) (m : ℕ) : addOrderOf (m : ZMod n) = n / m.gcd n := by
  rw [ZMod.addOrderOf_coe _ hn, Nat.gcd_comm]

lemma proposition23' {n : ℕ} (hn : n ≠ 0) (m : ℤ) : addOrderOf (m : ZMod n) = n / m.gcd n := by
  obtain ⟨x, rfl|rfl⟩ := Int.eq_nat_or_neg m
  · simp [proposition23 hn, Int.gcd]
  · simp [proposition23 hn, Int.gcd]

-- Corollary 2.5. The class [m]n generates Z/nZ if and only if gcd(m, n) = 1.
lemma corollary25 {n : ℕ} (hn : n ≠ 0) (m : ℕ) : addOrderOf (m : ZMod n) = n ↔ m.gcd n = 1 := by
  rw [proposition23 hn, Nat.div_eq_self]
  simp [hn]

lemma corollary25' {n : ℕ} (hn : n ≠ 0) (m : ℤ) : addOrderOf (m : ZMod n) = n ↔ m.gcd n = 1 := by
  rw [proposition23' hn, Nat.div_eq_self]
  simp [hn]

lemma Int.sign_mul_self (m : ℤ) : m.sign * m = |m| := by
  rcases eq_or_ne m 0 with rfl|hm
  · simp
  rw [←mul_right_inj' (_ : m.sign ≠ 0), sign_mul_abs, ←mul_assoc, ←sign_mul, ←pow_two,
      sign_eq_one_of_pos, one_mul]
  · exact pow_two_pos_of_ne_zero _ hm
  · simp [sign_eq_zero_iff_zero, hm]

lemma exists_multiple {n : ℕ} (hn : n ≠ 0) (m : ZMod n) (hm : addOrderOf m = n) (x : ZMod n) :
    ∃ k : ℕ, k • m = x := by
  have := @ZMod.fintype _ ⟨hn⟩
  have := addOrderOf_eq_card_multiples (x := m)
  have : AddSubmonoid.multiples m = ⊤
  · rw [SetLike.ext'_iff, AddSubmonoid.coe_top, ← Finset.coe_univ,
        ← (AddSubmonoid.multiples m : Set (ZMod n)).coe_toFinset, Finset.coe_inj,
        ← Finset.card_eq_iff_eq_univ]
    simp [←hm, this]
  obtain ⟨k, hx⟩ : x ∈ AddSubmonoid.multiples m
  · simp [this]
  exact ⟨k, hx⟩

lemma exercise213mp (m n : ℤ) (h : Int.gcd m n = 1) : ∃ a b, a * m + b * n = 1 := by
  suffices : ∃ a b, a * m - 1 = b * n
  · obtain ⟨a, b, h⟩ := this
    refine' ⟨a, -b, _⟩
    simp [←h]
  rcases eq_or_ne n 0 with rfl|hn
  · simp only [Int.gcd_zero_right] at h
    refine' ⟨Int.sign m, 0, _⟩
    rw [zero_mul, Int.sign_mul_self, sub_eq_zero, ←Nat.cast_one, ←h, Int.coe_natAbs]
  obtain ⟨n, rfl|rfl⟩ := Int.eq_nat_or_neg n <;> simp at hn
  · rw [←corollary25' hn] at h
    obtain ⟨k, hk⟩ := exists_multiple hn m h 1
    rw [←sub_eq_zero, ←Int.cast_one, nsmul_eq_mul, ←Int.cast_ofNat, ←Int.cast_mul,
        ←Int.cast_sub, ZMod.int_cast_zmod_eq_zero_iff_dvd] at hk
    obtain ⟨b, hb⟩ := hk
    refine' ⟨k, b, _⟩
    rw [hb, mul_comm]
  -- ideally, wlog here
  · simp only [Int.gcd_neg_right] at h
    rw [←corollary25' hn] at h
    obtain ⟨k, hk⟩ := exists_multiple hn m h 1
    rw [←sub_eq_zero, ←Int.cast_one, nsmul_eq_mul, ←Int.cast_ofNat, ←Int.cast_mul,
        ←Int.cast_sub, ZMod.int_cast_zmod_eq_zero_iff_dvd] at hk
    obtain ⟨b, hb⟩ := hk
    refine' ⟨k, -b, _⟩
    rw [hb]
    ring

lemma exercise213mpr (m n : ℤ) (h : ∃ a b, a * m + b * n = 1) : Int.gcd m n = 1 := by
  obtain ⟨a, b, hab⟩ := h
  -- ignore definition of coprime
  have : n ∣ a * m - 1
  · refine' ⟨-b, _⟩
    rw [←hab]
    ring
  have hn : (m.gcd n : ℤ) ∣ a * m - 1 := (Int.gcd_dvd_right _ _).trans this
  have hm : (m.gcd n : ℤ) ∣ m := Int.gcd_dvd_left _ _
  have := hn.add (hm.mul_left (-a))
  simp only [sub_eq_add_neg, neg_mul, add_neg_cancel_comm, dvd_neg] at this
  simpa using Int.eq_one_of_dvd_one (Int.coe_nat_nonneg _) this

-- 2.14. State and prove an analog of Lemma 2.2, showing that the multiplicationon Z/nZ is a
-- well-defined operation. [§2.3, §III.1.2]

-- 2.15. Let n > 0 he an odd integer.
-- - Prove that if gcd(m, n) = 1, then gcd(2m + n, 2n) = 1. (Use Exercise 2.13.)
-- - Prove that if gcd(r, 2n) = 1, then gcd((r + n) / 2, n) = 1. (Ditto.)
-- - Conclude that the function [m]n → [2m + n]2n is a bijection between (Z/nZ)* and (Z/2nZ)*.
lemma Int.even_gcd {m n : ℤ} :
    Even (m.gcd n) ↔ Even m ∧ Even n := by
  simp_rw [even_iff_two_dvd]
  constructor
  · intro h
    replace h : (2 : ℤ) ∣ gcd m n
    · obtain ⟨k, hk⟩ := h
      simp [hk]
    exact ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩
  · rintro ⟨hm, hn⟩
    have := dvd_gcd hm hn
    exact_mod_cast this

lemma Int.dvd_of_odd_dvd_two_mul {m n : ℤ} (hm : Odd m) (h : m ∣ 2 * n) : m ∣ n := by
  obtain ⟨k, hk⟩ := h
  have : Even (m * k)
  · simp [←hk]
  rw [even_mul, Int.even_iff_not_odd] at this
  cases' this with he he
  · exact absurd hm he
  obtain ⟨l, rfl⟩ := he
  rw [←two_mul, mul_left_comm] at hk
  refine' ⟨l, _⟩
  simpa using hk

lemma exercise215a {n : ℕ} (hn : Odd n) (m : ℤ) (h : m.gcd n = 1) :
    Int.gcd (2 * m + n) (2 * n) = 1 := by
  have : Int.gcd (2 * m + n) (2 * n) ∣ 2 * n := gcd_dvd_right _ _
  cases' Int.even_or_odd (Int.gcd (2 * m + n) (2 * n)) with he ho
  · rw [Int.even_coe_nat, Int.even_gcd] at he
    simp [Int.even_coe_nat, Int.even_add, Nat.odd_iff_not_even.mp hn] at he
  have : (Int.gcd (2 * m + n) (2 * n) : ℤ) ∣ 2 * n
  · exact_mod_cast this
  have hn := Int.dvd_of_odd_dvd_two_mul ho this
  have := (Int.gcd_dvd_left _ _).add (Int.dvd_neg.mpr hn)
  simp only [add_neg_cancel_right] at this
  have hm := Int.dvd_of_odd_dvd_two_mul ho this
  have := Int.dvd_gcd hm hn
  rw [h] at this
  exact_mod_cast (Int.eq_one_of_dvd_one (Int.coe_nat_nonneg _) this)

lemma exercise215b {n : ℕ} (hn : Odd n) (r : ℤ) (h : r.gcd (2 * n) = 1) :
    Int.gcd ((r + n) / 2) n = 1 := by
  cases' Int.even_or_odd r with he ho
  · rw [even_iff_two_dvd] at he
    have key : (2 : ℤ) ∣ (r.gcd (2 * n))
    · exact Int.dvd_gcd he (by simp)
    simp [h] at key
  have hd1 : r.gcd (2 * n) ∣ 1 := by simp [h]
  obtain ⟨a, b, hab⟩ := exercise213mp _ _
    (Nat.dvd_one.mp ((Int.gcd_dvd_gcd_mul_left_right _ _ _).trans hd1))
  apply exercise213mpr
  refine' ⟨2 * a, b - a, _⟩
  rw [mul_comm, ←mul_assoc, Int.ediv_mul_cancel, ←hab]
  · ring
  · rw [←even_iff_two_dvd, Int.even_add, Int.even_iff_not_odd]
    simp only [ho, not_true, Int.even_iff_not_odd, Int.odd_coe_nat, hn]

lemma Nat.cast_div_int {m n : ℕ} (h : m ∣ n) : (((n / m) : ℕ) : ℤ) = n / m := by
  rcases eq_or_ne m 0 with rfl|hm
  · simp
  obtain ⟨k, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm)]
  simp only [cast_mul, ne_eq, cast_eq_zero]
  rw [Int.mul_ediv_cancel_left]
  exact_mod_cast hm

lemma Nat.odd_of_coprime_even {m n : ℕ} (hn : Even n) (h : Nat.coprime m n) : Odd m := by
  rw [Nat.odd_iff_not_even]
  rintro ⟨k, rfl⟩
  rcases hn with ⟨m, rfl⟩
  simp [coprime, ←two_mul, gcd_mul_left] at h

def exercise215c {n : ℕ} (hn : Odd n) : Units (ZMod n) ≃ Units (ZMod (2 * n)) where
  toFun m := ZMod.unitOfCoprime (2 * m.val.val + n) $ by
    rw [Nat.coprime, ←Int.coe_nat_gcd, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_two,
        exercise215a hn]
    exact ZMod.val_coe_unit_coprime _
  invFun r := ZMod.unitOfCoprime ((r.val.val + n) / 2) $ by
    rw [Nat.coprime, ←Int.coe_nat_gcd, Nat.cast_div_int, Nat.cast_add, Nat.cast_two,
        exercise215b hn]
    · exact ZMod.val_coe_unit_coprime _
    · have := ZMod.val_coe_unit_coprime r
      rw [←even_iff_two_dvd, Nat.even_add, Nat.even_iff_not_odd, Nat.even_iff_not_odd]
      simp only [hn, iff_false, not_not]
      exact Nat.odd_of_coprime_even (by simp) this
  left_inv := by
    have npos : 0 < n
    · obtain ⟨k, rfl⟩ := hn
      simp
    have : NeZero n := NeZero.of_pos npos
    have : NeZero (2 * n) := NeZero.of_pos (mul_pos zero_lt_two npos)
    intro x
    have hc2 : Nat.coprime 2 n
    · refine' (Nat.coprime_or_dvd_of_prime Nat.prime_two _).resolve_right _
      contrapose! hn
      simp [even_iff_two_dvd, hn]
    let u2 := ZMod.unitOfCoprime (n := n) 2 hc2
    rw [←mul_left_inj u2]
    simp only [ZMod.coe_unitOfCoprime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Units.ext_iff]
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime]
    rcases eq_or_ne n 1 with rfl|h1
    · simp
    replace h1 : 2 < n
    · contrapose! h1
      interval_cases n
      · rfl
      · simp at hn
    have h2 : (2 : ZMod (2 * n)) = (2 : ℕ) := by simp
    rw [h2, ←Nat.cast_mul, ←Nat.cast_mul, ←Nat.cast_add, ZMod.val_nat_cast,
        Nat.div_mul_cancel, Nat.cast_add, CharP.cast_eq_zero (ZMod n) n, add_zero,
        ←(ZMod.val_injective n).eq_iff,
        ZMod.val_nat_cast, Nat.mod_mul_left_mod, Nat.add_mod_right, ZMod.val_mul,
        ZMod.val_nat_cast, Nat.mod_eq_of_lt h1, mul_comm]
    rw [←even_iff_two_dvd, Nat.even_add, Nat.even_iff_not_odd, not_iff_comm, ←Nat.odd_iff_not_even]
    simp only [hn, true_iff]
    rw [Nat.odd_mod_even_iff (Even.mul_right even_two _), Nat.odd_add, Nat.odd_iff_not_even,
        not_iff_comm, ←Nat.odd_iff_not_even]
    simp only [hn, true_iff, Even.mul_right even_two]
  right_inv := by
    have npos : 0 < n
    · obtain ⟨k, rfl⟩ := hn
      simp
    have : NeZero n := NeZero.of_pos npos
    have : NeZero (2 * n) := NeZero.of_pos (mul_pos zero_lt_two npos)
    have h2 : (2 : ZMod (2 * n)) = (2 : ℕ) := by simp
    intro x
    simp only [ZMod.coe_unitOfCoprime, Units.ext_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    cases' Nat.even_or_odd x.val.val with he ho
    · simpa using Nat.odd_of_coprime_even he (ZMod.val_coe_unit_coprime x).symm
    cases' lt_or_le x.val.val n with hx' hx'
    · rw [h2, ←Nat.cast_mul, ZMod.val_nat_cast, Nat.mod_eq_of_lt, Nat.mul_div_cancel_left',
          Nat.cast_add, add_assoc, ←two_mul, h2, ←Nat.cast_mul]
      · simp
      · rw [←even_iff_two_dvd, Nat.even_add, Nat.even_iff_not_odd, not_iff_comm,
            ←Nat.odd_iff_not_even]
        exact ⟨λ _ => ho, λ _ => hn⟩
      · rw [Nat.div_lt_iff_lt_mul zero_lt_two, mul_two]
        simp [hx']
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hx'
      obtain ⟨l, rfl⟩ : Even k
      · rw [hk, Nat.odd_add] at ho
        rwa [←ho]
      rw [←two_mul] at hk
      rw [hk, add_right_comm, ←two_mul, ←mul_add, Nat.mul_div_right _ zero_lt_two, ZMod.nat_cast_val,
          Nat.cast_add, CharP.cast_eq_zero, zero_add, ←ZMod.nat_cast_val, ZMod.val_nat_cast,
          Nat.mod_eq_of_lt, h2, ←Nat.cast_mul, ←Nat.cast_add, add_comm, ←hk]
      · simp
      · rw [←Nat.add_lt_add_iff_left (n + l), add_assoc, ←two_mul, ←hk, add_right_comm, ←two_mul]
        exact (ZMod.val_lt _).trans_le (by simp)

-- 2.16. Find the last digit of 1238237^18238456 (Work in Z/1OZ.)
lemma Nat.digits_getD (b n k : ℕ) (h : b ≠ 1 ∨ n ≤ k) :
    (Nat.digits b n).getD k 0 = (Nat.digits b (n % (b ^ (k + 1)))).getD k 0 := by
  rcases b with _|_|b
  · simp
  · simp only [zero_eq, succ_eq_add_one, zero_add, ne_eq, digits_one, one_pow]
    rw [Nat.mod_one]
    simp only [List.replicate, List.getD_nil]
    cases H : (List.get? (List.replicate n 1) k)
    · simp [List.getD, Option.getD, H]
    · simp only [List.getD, Option.getD, H]
      rw [List.get?_eq_some] at H
      obtain ⟨hk, -⟩ := H
      simp only [false_or] at h
      simp [h.not_lt] at hk
  simp only [succ_eq_add_one, add_assoc, ne_eq]
  norm_num
  induction' n using Nat.strongInductionOn with n IH generalizing k
  cases' n with n
  · simp
  rw [digits_eq_cons_digits_div (by simp) (by simp)]
  cases' k with k
  · by_cases H : (succ n) % (b + 2) = 0
    · simp [H]
    rw [eq_comm, digits_eq_cons_digits_div (by simp), List.getD_cons_zero] <;>
    simp [H]
  rw [List.getD_cons_succ, IH _ (Nat.div_lt_self' _ _) _ (by simp),
      Nat.div_mod_eq_mod_mul_div, ←pow_succ', succ_add]
  by_cases H : (succ n) % ((b + 2) ^ (succ k + 1)) = 0
  · simp [H]
  rw [eq_comm, digits_eq_cons_digits_div (by simp) H, List.getD_cons_succ]

lemma exercise216 : (Nat.digits 10 (1238237 ^ 18238456)).getD 0 0 = 1 := by
  have : 1238237 % 10 = 7 := by norm_num
  have red : 18238456 % 4 = 0 := by norm_num
  have key : ∀ k, 7 ^ k % 10 = 7 ^ (k % 4) % 10
  · intro k
    nth_rewrite 1 [←Nat.div_add_mod k 4]
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [Nat.digits_getD, zero_add, pow_one, Nat.pow_mod, this, key, red]
  · rfl
  · refine' Or.inl _
    norm_num

-- 2.17. Show that if m ≡ m' mod n, then gcd(m, n) = 1 if and only if gcd(m', n) = 1. [§2.3]
lemma exercise217 {m m' n : ℤ} (h : m ≡ m' [ZMOD n]) : Int.gcd m n = 1 ↔ Int.gcd m' n = 1 := by
  constructor <;> intro hm
  swap; swap_var m ↔ m'; rw [Int.modEq_comm] at h
  all_goals
  · obtain ⟨a, b, hab⟩ := exercise213mp _ _ hm
    obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp h.symm
    rw [hk, mul_add, ←mul_assoc, mul_right_comm, add_assoc, ←add_mul] at hab
    exact exercise213mpr _ _ ⟨_, _, hab⟩

-- 2.18. For d < n, define an injective function Z/dZ → S_n. preserving the operation,
-- that is, such that the sum of equivalence classes in Z/nZ corresponds to the product
-- of the corresponding permutations.
lemma Fin.cycleRange_pow_apply_of_gt {n : ℕ} {i j : Fin n} (h : i < j) (k : ℕ) :
    (Fin.cycleRange i ^ k) j = j := by
  cases' n
  · exact Fin.elim0 i
  induction' k with k IH
  · simp
  · simp [pow_succ', cycleRange_of_gt h, IH]

lemma Fin.cycleRange_pow_apply_of_le {n : ℕ} {i j : Fin n.succ} (h : j ≤ i) (k : ℕ) :
    (Fin.cycleRange i ^ k) j = if i = 0 then 0 else ⟨(j + k) % (i + 1),
      i.is_lt.trans_le' (Nat.le_of_lt_succ (Nat.mod_lt _ Nat.succ_pos'))⟩  := by
  rcases eq_or_ne i 0 with rfl|hi
  · simpa using h
  rw [if_neg hi]
  induction' k with k IH generalizing j
  · simp only [Nat.zero_eq, pow_zero, Equiv.Perm.coe_one, id_eq, add_zero, Fin.ext_iff]
    refine' (Nat.mod_eq_of_lt _).symm
    rw [le_iff_val_le_val] at h
    exact Nat.lt_succ_of_le h
  · rw [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply, IH h, cycleRange_of_le]
    split_ifs with H
    · simp only [ext_iff, val_zero] at H ⊢
      simp_rw [Nat.succ_eq_add_one, ←add_assoc]
      rw [Nat.add_mod, H, Nat.mod_eq_of_lt (_ : (1 : ℕ) < (i + 1)), Nat.mod_self]
      simp only [lt_add_iff_pos_left]
      exact Nat.pos_of_ne_zero ((Fin.ne_iff_vne _ _).mp hi)
    · rw [ext_iff, Fin.val_add, val_one', Nat.add_mod_mod]
      simp only
      have key : ((j : ℕ) + k) % (i + 1) < i
      · exact lt_of_le_of_ne (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _)))
          ((Fin.ne_iff_vne _ _).mp H)
      rw [Nat.succ_eq_add_one k, ←add_assoc, Nat.add_mod _ 1 (i + 1),
          Nat.mod_eq_of_lt, Nat.add_mod_mod]
      · refine' (Nat.mod_eq_of_lt _).symm
        simp [add_lt_add_iff_right, key]
      · exact i.is_lt.trans_le' (Nat.succ_le_of_lt key)
    · rw [Fin.le_iff_val_le_val, ←Nat.lt_succ_iff]
      exact Nat.mod_lt _ Nat.succ_pos'

def exercise218 {d n : ℕ} (hd : 0 < d) (h : d < n) : ZMod d ↪ Equiv.Perm (Fin n) where
  toFun x :=  Fin.cycleRange ⟨d - 1, (Nat.pred_le _).trans_lt (lt_of_le_of_ne h.le h.ne)⟩ ^ x.val
  inj' := by
    cases' n
    · simp at h
    intro x y hxy
    simp only [ge_iff_le, Equiv.ext_iff] at hxy
    have : NeZero d := ⟨hd.ne'⟩
    specialize hxy 0
    rw [Fin.cycleRange_pow_apply_of_le (Fin.zero_le _),
        Fin.cycleRange_pow_apply_of_le (Fin.zero_le _)] at hxy
    simp only [ge_iff_le, Fin.ext_iff, Fin.val_zero, tsub_eq_zero_iff_le, zero_add, Fin.mk_zero] at hxy
    split_ifs at hxy with H
    · have : d = 1 := le_antisymm H (Nat.succ_le_of_lt hd)
      subst d
      exact Subsingleton.elim x y
    · simp only [ge_iff_le, tsub_add_cancel_of_le (Nat.succ_le_of_lt hd)] at hxy
      change ZMod.val x ≡ ZMod.val y [MOD d] at hxy
      simpa [←ZMod.nat_cast_eq_nat_cast_iff] using hxy

lemma exercise218_map_add {d n : ℕ} (hd : 0 < d) (h : d < n) (x y : ZMod d) :
    exercise218 hd h (x + y) = exercise218 hd h x * exercise218 hd h y := by
  ext a
  simp only [exercise218, ge_iff_le, Function.Embedding.coeFn_mk, Equiv.Perm.coe_mul,
             Function.comp_apply]
  cases' lt_or_le (d - 1) a with H H
  · rw [Fin.cycleRange_pow_apply_of_gt H, Fin.cycleRange_pow_apply_of_gt _,
        Fin.cycleRange_pow_apply_of_gt H]
    rw [Fin.cycleRange_pow_apply_of_gt H]
    exact H
  · cases' n
    · simp at h
    rcases d with _|_|d
    · simp at hd
    · simp
    rw [Fin.cycleRange_pow_apply_of_le H, Fin.cycleRange_pow_apply_of_le _,
        Fin.cycleRange_pow_apply_of_le H]
    · simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero, and_false,
               tsub_zero] at H ⊢
      simp only [Fin.ext_iff, Fin.val_zero, add_eq_zero, and_false, ite_false, Nat.mod_add_mod]
      rw [ZMod.val_add]
      simp [Nat.succ_eq_add_one, ←add_assoc, add_right_comm]
    · rw [Fin.cycleRange_pow_apply_of_le H]
      simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero, and_false,
                 tsub_zero, Fin.ext_iff, Fin.val_zero, ite_false, Fin.mk_le_mk]
      exact Nat.le_of_lt_succ (Nat.mod_lt _ Nat.succ_pos')

-- 2.19.  Both (Z/5Z)ˣ and (Z/12Z)ˣ consist of 4 elements. Write their multiplication tables,
-- and prove that no re-ordering of the elements will make them match.
-- (Cf. Exercise 1.6.) [§4.3]
lemma exercise219_5 : (Finset.univ : Finset (Units (ZMod 5))) =
    {1,
      ZMod.unitsEquivCoprime.symm ⟨2, by norm_num⟩,
      ZMod.unitsEquivCoprime.symm ⟨3, by norm_num⟩,
      ZMod.unitsEquivCoprime.symm ⟨4, by norm_num⟩} := by
  rfl

lemma exercise219_5order : (Finset.univ : Finset (Units (ZMod 5))).val.map orderOf =
    {1, 4, 4, 2} := by
  rw [exercise219_5]
  simp only [Finset.mem_singleton, Finset.mem_insert, Finset.insert_val, Finset.singleton_val,
    Multiset.mem_singleton, not_false_eq_true, Multiset.ndinsert_of_not_mem, Multiset.mem_cons,
    Multiset.map_cons, orderOf_one, Multiset.map_singleton, Multiset.insert_eq_cons,
    Multiset.cons_inj_right]
  congr <;> rw [orderOf_eq_iff] <;> norm_num

lemma exercise219_12 : (Finset.univ : Finset (Units (ZMod 12))) =
    {1,
      ZMod.unitsEquivCoprime.symm ⟨5, by norm_num⟩,
      ZMod.unitsEquivCoprime.symm ⟨7, by norm_num⟩,
      ZMod.unitsEquivCoprime.symm ⟨11, by norm_num⟩} := by
  rfl

lemma exercise219_12order : (Finset.univ : Finset (Units (ZMod 12))).val.map orderOf =
    {1, 2, 2, 2} := by
  rw [exercise219_12]
  simp only [Finset.mem_singleton, Finset.mem_insert, Finset.insert_val, Finset.singleton_val,
    Multiset.mem_singleton, not_false_eq_true, Multiset.ndinsert_of_not_mem, Multiset.mem_cons,
    Multiset.map_cons, orderOf_one, Multiset.map_singleton, Multiset.insert_eq_cons,
    Multiset.cons_inj_right]
  congr <;> rw [orderOf_eq_iff] <;> norm_num

-- FIXME: use MulEquivLike
@[to_additive (attr := simp)]
theorem orderOf_map_equiv {M N} [Monoid M] [Monoid N] (φ : M ≃* N) (x : M) :
    orderOf (φ x) = orderOf x := by
  refine' dvd_antisymm (orderOf_map_dvd (G := M) (H := N) φ x) _
  convert orderOf_map_dvd (G := N) (H := M) φ.symm (φ x)
  simp

lemma univ_map_orderOf_eq_of_mulEquiv {M N} [Monoid M] [Monoid N] [Fintype M] [Fintype N]
    (φ : M ≃* N) :
    (Finset.univ (α := M)).val.map orderOf = (Finset.univ (α := N)).val.map orderOf := by
  have : (Finset.univ (α := N)) = (Finset.univ (α := M)).map φ
  · ext
    simp
  simp [this, -Finset.map_univ_equiv]

lemma exercise219 : ¬ Nonempty (Units (ZMod 5) ≃* Units (ZMod 12)) := by
  intro ⟨e⟩
  have := univ_map_orderOf_eq_of_mulEquiv e
  rw [exercise219_5order, exercise219_12order] at this
  simp at this
