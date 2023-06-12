import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Group.Ext
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Image
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

universe u v w

open BigOperators CategoryTheory

-- 1.1. Write a careful proof that every group is the group of isomorphisms of a groupoid.
-- In particular, every group is the group of automorphisms of some object in some category. [§2.1]
def Group.Groupoid (G : Type _) [Group G] : Groupoid Unit where
  Hom _ _ := G
  id _ := 1
  comp := (· * ·)
  id_comp := one_mul
  comp_id := mul_one
  assoc := mul_assoc
  inv := (· ⁻¹)
  inv_comp := inv_mul_self
  comp_inv := mul_inv_self

-- Opposite direction of mathlibs
def Category.Aut.Group {C : Type _} [Category C] (X : C) : Group (Aut X) where
  mul := (· ≪≫ ·)
  mul_assoc := Iso.trans_assoc
  one := Iso.refl _
  one_mul := Iso.refl_trans
  mul_one := Iso.trans_refl
  inv := Iso.symm
  div f g := f ≪≫ g.symm
  mul_left_inv := Iso.symm_self_id

-- 1.2.  Consider the `sets of numbers' listed in §1.1, and decide which are made into groups by
-- conventional operations such as + and ⬝. Even if the answer is negative
-- (for example, (ℝ, ⬝) is not a group), see if variations on the definition of these sets lead to
-- groups (for example, (R*, ) is a group; cf. §1.4). [§1.2]

-- 1.3. Prove that (gh)⁻¹ = h⁻¹g⁻¹ for all elements g, h of a group G.
lemma exercise13 {G : Type _} [Group G] (g h : G) : (g * h)⁻¹ = h⁻¹ * g⁻¹ := calc
  (g * h)⁻¹ = 1 * (g * h)⁻¹ := (one_mul _).symm
  _ = (h⁻¹ * h) * (g * h)⁻¹ := by rw [inv_mul_self]
  _ = (h⁻¹ * (1 * h)) * (g * h)⁻¹ := by rw [one_mul]
  _ = (h⁻¹ * ((g ⁻¹ * g) * h)) * (g * h)⁻¹ := by rw [inv_mul_self]
  _ = (h⁻¹ * g ⁻¹ * (g * h)) * (g * h)⁻¹ := by simp_rw [mul_assoc]
  _ = h⁻¹ * g⁻¹ := by rw [mul_assoc, mul_inv_self, mul_one]

-- 1.4. Suppose that g2 = e for all elements g of a group G; prove that G is commutative.
lemma exercise14 {G : Type _} [Group G] (h : ∀ g : G, g * g = 1) (g g' : G) : Commute g g' := by
  rw [Commute, SemiconjBy]
  have : ∀ g : G, g⁻¹ = g
  · intro g
    rw [inv_eq_iff_mul_eq_one, h]
  rw [←this g', mul_inv_eq_iff_eq_mul, ←this g, ←mul_inv_rev, this (g * g'), mul_assoc, h, mul_one,
      this]

-- 1.5. The 'multiplication table' of a group is an array compiling the results of all
-- multiplications `g * h`.
-- Prove that every row and every column of the multiplication table of a group contains all
-- elements of the group exactly once (like Sudoku diagrams!).
def exercise15 {G : Type _} [Group G] (g : G) :
    G ≃ ((g * ·) '' Set.univ) where
  toFun h := ⟨g * h, by simp⟩
  invFun := λ ⟨h, _⟩ => g⁻¹ * h
  left_inv h := by simp
  right_inv := λ ⟨h, gh⟩ => by simp

def exercise15' {G : Type _} [Group G] (g : G) :
    G ≃ ((· * g) '' Set.univ) where
  toFun h := ⟨h * g, by simp⟩
  invFun := λ ⟨h, _⟩ => h * g⁻¹
  left_inv h := by simp
  right_inv := λ ⟨h, gh⟩ => by simp

-- 1.6. Prove that there is only one possible multiplication table for G if G has exactly 1, 2, or 3
-- elements. Analyze the possible multiplication tables for groups with exactly 4 elements, and show
-- that there are two distinct tables, up to reordering the elements of G. Use these tables to prove
-- that all groups with < 4 elements are commutative.
-- (You are welcome to analyze groups with 5 elements using the same technique, but you will soon
-- know enough about groups to be able to avoid such brute-force approaches.) [2.19]

section Fintype

instance {G : Type _} [Fintype G] : Fintype (One G) := derive_fintype% _
instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (Mul G) := derive_fintype% _
instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (Semigroup G) := derive_fintype% _

lemma np_inj {G : Type _} [Mul G] [One G]
    (np np' : ℕ → G → G) (nph0 : ∀ x, np 0 x = 1) (nph0' : ∀ x, np' 0 x = 1)
    (nph1 : ∀ n x, np (n + 1) x = x * np n x)
    (nph1' : ∀ n x, np' (n + 1) x = x * np' n x) : np = np' := by
  ext n x
  induction' n with n IH generalizing x <;>
  simp_all

instance np_unique {G : Type _} [Mul G] [One G] :
    Unique {np : ℕ → G → G // (∀ x, np 0 x = 1) ∧ (∀ n x, np (n + 1) x = x * np n x)} :=
  ⟨⟨npowRec, by intros; rfl, by intros; rfl⟩,
    λ f => (Subtype.ext
      (np_inj _ _ f.prop.left (by intros; rfl) f.prop.right (by intros; rfl)))⟩

instance np_fintype {G : Type _} [Mul G] [One G] :
    Fintype {np : ℕ → G → G // (∀ x, np 0 x = 1) ∧ (∀ n x, np (n + 1) x = x * np n x)} :=
  np_unique.fintype

instance {G : Type _} [Semigroup G] [One G] : Fintype (@Sigma (ℕ → G → G) fun npow ↦
    (_ : PLift ((∀ (x : G), npow 0 x = 1))) ×
    PLift ((∀ (n : ℕ) (x : G), npow (n + 1) x = x * npow n x))) :=
  Fintype.ofEquiv {np : ℕ → G → G // (∀ x, np 0 x = 1) ∧ (∀ n x, np (n + 1) x = x * np n x)} {
    toFun := λ ⟨f, hf⟩ => ⟨f, PLift.up hf.left, PLift.up hf.right⟩
    invFun := λ ⟨f, hf⟩ => ⟨f, hf.fst.down, hf.snd.down⟩
    left_inv := λ ⟨f, hf⟩ => by simp
    right_inv := λ ⟨f, hf⟩ => by simp
  }

instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (Monoid G) := derive_fintype% _
instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (Div G) := derive_fintype% _
instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (Inv G) := derive_fintype% _

lemma zp_inj {G : Type _} [Mul G] [One G] [Inv G]
    (zp zp' : ℤ → G → G) (zph0 : ∀ x, zp 0 x = 1) (zph0' : ∀ x, zp' 0 x = 1)
    (zph1 : ∀ (n : ℕ) (a : G), zp (Int.ofNat (Nat.succ n)) a = a * zp (Int.ofNat n) a)
    (zph1' : ∀ (n : ℕ) (a : G), zp' (Int.ofNat (Nat.succ n)) a = a * zp' (Int.ofNat n) a)
    (zphn : ∀ (n : ℕ) (a : G), zp (Int.negSucc n) a = (zp (Int.ofNat (Nat.succ n)) a)⁻¹)
    (zphn' : ∀ (n : ℕ) (a : G), zp' (Int.negSucc n) a = (zp' (Int.ofNat (Nat.succ n)) a)⁻¹) :
    zp = zp'
    := by
  ext n x
  induction' n with n n generalizing x
  · induction n
    · simp_all
    · simp_all
  · rw [zphn, zphn', zph1, zph1']
    congr
    induction n
    · simp_all
    · simp_all


instance zp_unique {G : Type _} [Mul G] [One G] [Inv G] :
    Unique {zp : ℤ → G → G // (∀ x, zp 0 x = 1) ∧
      (∀ (n : ℕ) (a : G), zp (Int.ofNat (Nat.succ n)) a = a * zp (Int.ofNat n) a) ∧
      (∀ (n : ℕ) (a : G), zp (Int.negSucc n) a = (zp (Int.ofNat (Nat.succ n)) a)⁻¹)} :=
  ⟨⟨zpowRec, by intros; rfl, by intros; rfl, by intros; rfl⟩,
    λ f => (Subtype.ext (zp_inj _ _ f.prop.left (by intros; rfl) f.prop.right.left (by intros; rfl)
      f.prop.right.right (by intros; rfl)))⟩

instance zp_fintype {G : Type _} [Mul G] [One G] [Inv G]:
    Fintype {zp : ℤ → G → G // (∀ x, zp 0 x = 1) ∧
      (∀ (n : ℕ) (a : G), zp (Int.ofNat (Nat.succ n)) a = a * zp (Int.ofNat n) a) ∧
      (∀ (n : ℕ) (a : G), zp (Int.negSucc n) a = (zp (Int.ofNat (Nat.succ n)) a)⁻¹)} :=
  zp_unique.fintype

instance {G : Type _} [Mul G] [One G] [Inv G] : Fintype (@Sigma (ℤ → G → G) fun zpow ↦
  (_ : PLift ((∀ (a : G), zpow 0 a = 1))) ×
    (_ : PLift ((∀ (n : ℕ) (a : G), zpow (Int.ofNat (Nat.succ n)) a = a * zpow (Int.ofNat n) a))) ×
      PLift ((∀ (n : ℕ) (a : G), zpow (Int.negSucc n) a = (zpow (↑(Nat.succ n)) a)⁻¹))) :=
  Fintype.ofEquiv {zp : ℤ → G → G // (∀ x, zp 0 x = 1) ∧
      (∀ (n : ℕ) (a : G), zp (Int.ofNat (Nat.succ n)) a = a * zp (Int.ofNat n) a) ∧
      (∀ (n : ℕ) (a : G), zp (Int.negSucc n) a = (zp (Int.ofNat (Nat.succ n)) a)⁻¹)} {
    toFun := λ ⟨f, hf⟩ => ⟨f, PLift.up hf.left, PLift.up hf.right.left, PLift.up hf.right.right⟩
    invFun := λ ⟨f, hf⟩ => ⟨f, hf.fst.down, hf.snd.fst.down, hf.snd.snd.down⟩
    left_inv := λ ⟨f, hf⟩ => by simp
    right_inv := λ ⟨f, hf, hf', hf''⟩ => by simp
  }
instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (DivInvMonoid G) := derive_fintype% _
instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (Group G) := derive_fintype% _
instance {G : Type _} [Fintype G] [DecidableEq G] : Fintype (CommGroup G) := derive_fintype% _

lemma Mul.ext {G : Type _} {a b : Mul G} (h : a.mul = b.mul) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance {G : Type _} [Fintype G] [DecidableEq G] : DecidableEq (Mul G) :=
  λ g g' => decidable_of_iff (g.mul = g'.mul) ⟨Mul.ext, congr_arg _⟩

instance {G : Type _} [Fintype G] [DecidableEq G] : DecidableEq (Semigroup G) :=
  λ g g' => decidable_of_iff (g.toMul = g'.toMul) $ by
  constructor
  · intro h
    cases g
    cases g'
    cases h
    rfl
  · exact congr_arg _

instance {G : Type _} [Fintype G] [DecidableEq G] : DecidableEq (Group G) :=
  λ g g' => decidable_of_iff (g.toMul = g'.toMul) $ by
  constructor
  · intro h
    refine' Group.ext _
    cases' g with g
    cases' g' with g'
    cases' g with g
    cases' g' with g'
    cases' g with g
    cases' g' with g'
    cases' g with g
    cases' g' with g'
    cases h
    rfl
  · intro h
    cases h
    rfl

end Fintype
lemma exercise161 : Fintype.card (CommGroup Unit) = 1 := by
  rw [Fintype.card_eq_one_iff]
  let g : CommGroup Unit := {
    mul := λ _ _ => ()
    mul_assoc := by decide
    one := ()
    one_mul := by decide
    mul_one := by decide
    inv := λ _ => ()
    mul_left_inv := by decide
    mul_comm := by decide
  }
  refine' ⟨g, λ g' => CommGroup.ext _⟩
  ext

section

local instance exercise162a : CommGroup Bool where
  mul x y := match x, y with
    | true, y => y
    | x, true => x
    | false, false => true
  mul_assoc := by decide
  one := true
  one_mul := by decide
  mul_one := by decide
  inv := id
  mul_left_inv := by decide
  mul_comm := by decide

def Bool' := Bool

local instance exercise162b : CommGroup Bool' where
  mul x y := match x, y with
    | false, y => y
    | x, false => x
    | true, true => false
  mul_assoc := by delta Bool'; decide
  one := false
  one_mul := by delta Bool'; decide
  mul_one := by delta Bool'; decide
  inv := id
  mul_left_inv := by delta Bool'; decide
  mul_comm := by delta Bool'; decide

def exercise162equiv : Bool ≃* Bool' where
  toFun := not
  invFun := not
  left_inv := by delta Bool'; decide
  right_inv := by delta Bool'; decide
  map_mul' := by delta Bool'; decide

end

section

def exercise163a : CommGroup (Fin 3) where
  mul x y := x + y
  mul_assoc := by decide
  one := 0
  one_mul := by decide
  mul_one := by decide
  inv := (- ·)
  div := (· - ·)
  div_eq_mul_inv := by decide
  mul_left_inv := by decide
  mul_comm := by decide

def exercise163b : CommGroup (Fin 3) where
  mul x y := x + y + 1
  mul_assoc := by decide
  one := 2
  one_mul := by decide
  mul_one := by decide
  inv x := -x + 1
  div x y := x - y - 1
  div_eq_mul_inv := by decide
  mul_left_inv := by decide
  mul_comm := by decide

def exercise163c : CommGroup (Fin 3) where
  mul x y := x + y + 2
  mul_assoc := by decide
  one := 1
  one_mul := by decide
  mul_one := by decide
  inv x := -x + 2
  div x y := x - y - 2
  div_eq_mul_inv := by decide
  mul_left_inv := by decide
  mul_comm := by decide

def F3a := Fin 3
def F3b := Fin 3
def F3c := Fin 3

instance : CommGroup (F3a) := exercise163a
instance : CommGroup (F3b) := exercise163b
instance : CommGroup (F3c) := exercise163c

def exercise163ab : F3a ≃* F3b where
  toFun := λ (x : Fin 3) => x + 2
  invFun := λ (x : Fin 3) => x + 1
  left_inv := by delta F3a F3b; simp
  right_inv := by delta F3a F3b; simp
  map_mul' := by delta F3a F3b; simp

def exercise163bc : F3b ≃* F3c where
  toFun := λ (x : Fin 3) => x + 2
  invFun := λ (x : Fin 3) => x + 1
  left_inv := by delta F3b F3c; simp
  right_inv := by delta F3b F3c; simp
  map_mul' := by delta F3b F3c; simp

end

section

inductive V
| e
| a
| b
| ab
deriving Fintype, DecidableEq

open V in
instance : CommGroup V where
  mul x y := match x, y with
    | e, _ => y
    | _, e => x
    | a, b => ab
    | b, a => ab
    | a, a => e
    | b, b => e
    | ab, ab => e
    | ab, a => b
    | a, ab => b
    | ab, b => a
    | b, ab => a
  mul_assoc := by decide
  one := e
  one_mul := by decide
  mul_one := by decide
  inv := id
  mul_left_inv := by decide
  mul_comm := by decide

lemma involutive_inv (v : V) : v⁻¹ = v := by revert v; decide

lemma exercise164 : ¬ Nonempty (V ≃* Multiplicative (Fin 4)) := by
  intro ⟨e⟩
  suffices : ∀ x : Fin 4, x + x = 0
  · simpa using this 1
  intro x
  rw [add_eq_zero_iff_eq_neg]
  refine' Multiplicative.ofAdd.injective _
  rw [ofAdd_neg]
  refine' e.symm.injective _
  simp [involutive_inv]

end

-- 1.7. Prove Corollary 1.11.
-- Corollary 1.11. Let g be an element of finite order, and let N ∈ Z. Then
-- g^N = e ↔ N is a multiple of |g|.
lemma corollary111' {G : Type _} [Group G] (g : G) (hg : orderOf g ≠ 0) (N : ℕ) :
      g ^ N = 1 ↔ orderOf g ∣ N := by
  constructor
  · intro h
    rw [←Nat.mod_add_div N (orderOf g), pow_add, pow_mul, pow_orderOf_eq_one, one_pow, mul_one] at h
    suffices : N % orderOf g = 0
    · exact Nat.dvd_of_mod_eq_zero this
    have : ∀ n < orderOf g, n ≠ 0 → g ^ n ≠ 1
    · intros n hn hn0
      exact pow_ne_one_of_lt_orderOf' hn0 hn
    specialize this (N % orderOf g) (Nat.mod_lt _ (Nat.pos_of_ne_zero hg))
    contrapose! h
    exact this h
  · rintro ⟨x, rfl⟩
    rw [pow_mul, pow_orderOf_eq_one, one_pow]

lemma corollary111 {G : Type _} [Group G] (g : G) (hg : orderOf g ≠ 0) (N : ℤ) :
      g ^ N = 1 ↔ (orderOf g : ℤ) ∣ N := by
  have : ∀ (g : G) (N : ℕ), g ^ (- N : ℤ) = 1 → g ^ N = 1
  · intros g N h
    rw [←mul_left_inj (g ^ (- N : ℤ))]
    simp only [zpow_neg, zpow_coe_nat, one_mul, one_eq_inv]
    rw [mul_inv_self, ←h]
    simp
  suffices : g ^ N.natAbs = 1 ↔ orderOf g ∣ N.natAbs
  · have key : N = N.natAbs ∨ N = -N.natAbs
    · induction N
      · simp
      · simp only [Int.natAbs_negSucc, Nat.cast_succ, neg_add_rev]
        rw [Int.negSucc_coe]
        simp
    cases' key with key key
    · rw [key, zpow_coe_nat, Int.coe_nat_dvd, this]
    · rw [key, zpow_neg, inv_eq_one, zpow_coe_nat, Int.dvd_neg, Int.coe_nat_dvd, this]
  exact corollary111' g hg _

-- I.8. Let G be a finite group, with exactly one element f of order 2. Prove that ∏_g g = f. [4.16]
lemma Nat.dvd_two_iff {n : ℕ} : n ∣ 2 ↔ n = 1 ∨ n = 2 := by
  constructor
  · intro h
    have : n ≤ 2 := Nat.le_of_dvd zero_lt_two h
    interval_cases n <;>
    simp_all
  · rintro (rfl|rfl|rfl) <;>
    simp

lemma inv_eq_self_of_orderOf_eq_two {G : Type _} [Group G] {g : G} (h : orderOf g = 2) :
    g⁻¹ = g := by
  rw [inv_eq_iff_mul_eq_one, ←pow_two, corollary111', h]
  simp [h]

lemma inv_eq_self_iff_orderOf_eq_one_or_two {G : Type _} [Group G] {g : G} :
    g⁻¹ = g ↔ g = 1 ∨ orderOf g = 2 := by
  rw [inv_eq_iff_mul_eq_one, ←pow_two]
  constructor
  · intro h
    by_cases hg : orderOf g = 0
    · rw [orderOf_eq_zero_iff'] at hg
      exact absurd h (hg _ zero_lt_two)
    rw [corollary111' _ hg] at h
    replace h : orderOf g ≤ 2 := Nat.le_of_dvd zero_lt_two h
    interval_cases H : (orderOf g)
    · contradiction
    · rw [orderOf_eq_one_iff] at H
      simp [H]
    · simp
  · rintro (rfl|h)
    · simp
    · rw [←h, pow_orderOf_eq_one]

lemma two_lt_orderOf_iff_inv_ne_self {G : Type _} [Fintype G] [Group G] {g : G} :
    2 < orderOf g ↔ g⁻¹ ≠ g := by
  constructor
  · contrapose!
    rw [inv_eq_iff_mul_eq_one, ←pow_two, corollary111' g (orderOf_pos g).ne']
    exact Nat.le_of_dvd zero_lt_two
  · contrapose!
    generalize hk : orderOf g = k
    intro H
    interval_cases k
    · exact absurd hk (orderOf_pos _).ne'
    · rw [orderOf_eq_one_iff] at hk
      simp [hk]
    · exact inv_eq_self_of_orderOf_eq_two hk

lemma prod_one' {G : Type _} [CommGroup G] (s : Finset G) (hs : ∀ g ∈ s, g⁻¹ ≠ g ∧ g⁻¹ ∈ s) :
    ∏ g in s, g = 1 := by
  classical
  induction' s using Finset.strongInduction with s IH
  rcases s.eq_empty_or_nonempty with (rfl|⟨g, hg⟩)
  · simp
  have hgs : {g, g⁻¹} ⊆ s
  · intro
    simp only [Finset.mem_singleton, Finset.mem_insert]
    rintro (rfl|rfl)
    · exact hg
    · exact (hs _ hg).right
  rw [←Finset.prod_sdiff hgs, IH]
  · rw [Finset.prod_insert]
    · simp
    · simpa using (hs _ hg).left.symm
  · refine' Finset.sdiff_ssubset hgs _
    simp
  · simp_all [not_or, inv_eq_iff_eq_inv]

lemma Even.add_two {n : ℕ} (hn : Even n) : Even (n + 2) := by
  obtain ⟨k, rfl⟩ := hn
  refine' ⟨k + 1, _⟩
  simp [add_comm, add_assoc, add_left_comm]

lemma card_even {G : Type _} [Group G] (s : Finset G) (hs : ∀ g ∈ s, g⁻¹ ≠ g ∧ g⁻¹ ∈ s) :
    Even (Finset.card s) := by
  classical
  induction' s using Finset.strongInduction with s IH
  rcases s.eq_empty_or_nonempty with (rfl|⟨g, hg⟩)
  · simp
  have hgs : {g, g⁻¹} ⊆ s
  · intro
    simp only [Finset.mem_singleton, Finset.mem_insert]
    rintro (rfl|rfl)
    · exact hg
    · exact (hs _ hg).right
  rw [←Finset.card_sdiff_add_card_eq_card hgs, Finset.card_insert_eq_ite]
  simp only [Finset.mem_singleton, (hs g hg).left.symm, Finset.card_singleton, ite_false]
  refine' (IH _ (Finset.sdiff_ssubset hgs _) _).add_two
  · simp
  · simp only [Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_insert, not_or, ne_eq, and_imp]
    intros x hx hxg hxfg
    refine' ⟨(hs _ hx).left, (hs _ hx).right, _, inv_injective.ne hxg⟩
    rwa [inv_eq_iff_eq_inv]

lemma exercise18' {G : Type _} [Fintype G] [CommGroup G] [DecidableEq G] :
    ∏ g : G, g = ∏ g in ((Finset.univ (α := G)).filter (λ i => i⁻¹ = i)), g := by
  rw [←Finset.prod_filter_mul_prod_filter_not Finset.univ (λ i => i⁻¹ = i)]
  simp only [Finset.mem_univ, forall_true_left, mul_right_eq_self]
  rw [prod_one']
  simp [ne_comm]

lemma exercise18 {G : Type _} [Fintype G] [CommGroup G] (f : G)
    (hf : ∀ g : G, orderOf g = 2 ↔ g = f) : ∏ g : G, g = f := by
  have : ∀ g : G, (g = 1 ∨ g = f) ↔ g⁻¹ = g
  · intro g
    rw [inv_eq_self_iff_orderOf_eq_one_or_two, hf]
  classical
  rw [exercise18']
  convert_to (∏ g in {1, f}, g)  = f
  · congr
    ext
    simp [this]
  · simp

-- 1.9. Let G be a finite group, of order n, and let m be the number of elements g ∈ G of order
-- exactly 2. Prove that n - m is odd. Deduce that if n is even, then G necessarily contains
-- elements of order 2.
@[simp]
lemma orderOf_lt_two_iff {G : Type _} [Fintype G] [LeftCancelMonoid G] {g : G} :
    orderOf g < 2 ↔ g = 1 := by
  constructor
  · intro h
    generalize hn : orderOf g = n
    rw [hn] at h
    interval_cases n
    · exact absurd hn (orderOf_pos _).ne'
    · simpa using hn
  · rintro rfl
    simp

lemma exercise19 (G : Type _) [Fintype G] [Group G] :
    Odd (Fintype.card G - (Finset.univ.filter (λ g : G => orderOf g = 2)).card) := by
  generalize h : (Fintype.card G - (Finset.univ.filter (λ g : G => orderOf g = 2)).card) = k
  induction' k using Nat.evenOddRec with k IH generalizing G
  · simp only [Finset.mem_univ, forall_true_left, ge_iff_le, tsub_eq_zero_iff_le] at h
    replace h := le_antisymm (Finset.card_le_univ _) h
    simp only [Finset.mem_univ, forall_true_left, Finset.card_eq_iff_eq_univ,
               Finset.filter_eq_self] at h
    simpa using h 1
  · exfalso
    cases' k with k
    · simpa using IH _ h
    replace h : Finset.card (Finset.filter (λ g : G => orderOf g ≠ 2) Finset.univ) = 2 * (k + 1)
    · rw [←h, eq_comm, tsub_eq_iff_eq_add_of_le (Finset.card_le_univ _), add_comm,
          Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
    classical
    have : ∃ a, Finset.filter (fun a : G ↦ orderOf a < 2) Finset.univ = {a}
    · refine' ⟨1, _⟩
      ext
      simp
    replace h : Finset.card (Finset.filter (λ g : G => 2 < orderOf g) Finset.univ) = 2 * k + 1
    · simp_rw [ne_iff_lt_or_gt, Finset.filter_or] at h
      rw [Finset.card_union_eq, add_comm] at h
      have key : 2 * (k + 1) - 1 = 2 * k + 1
      · simp [mul_add]
      · rw [←key, ←h, ←Finset.card_singleton (1 : G), eq_comm,
          tsub_eq_iff_eq_add_of_le]
        · simpa [Finset.card_eq_one] using this
        · refine' (Finset.card_mono _).trans (self_le_add_left _ _)
          intro
          simp
      · refine' Finset.disjoint_filter_filter' _ _ _
        intro p hx hx' x H
        exact (hx x H).not_lt (hx' x H)
    simp_rw [two_lt_orderOf_iff_inv_ne_self] at h
    have H : Even (Finset.card (Finset.filter (fun g : G => g⁻¹ ≠ g) Finset.univ))
    · refine' card_even _ _
      simp [inv_eq_iff_eq_inv]
    rw [Nat.even_iff_not_odd] at H
    exact H ⟨k, h⟩
  · simp

lemma exercise19' {G : Type _} [Fintype G] [Group G] (hG : Even (Fintype.card G)) :
    ∃ g : G, orderOf g = 2 := by
  obtain ⟨k, hk⟩ := hG
  cases' k with k
  · simp [Fintype.card_eq_zero_iff] at hk
  obtain ⟨n, hn⟩ := exercise19 G
  have : 2 * n + 1 ≤ 2 * (k + 1)
  · rw [←hn, two_mul, ←hk]
    simp
  have hn' := hn
  classical
  rw [tsub_eq_iff_eq_add_of_le (Finset.card_le_univ _), hk, add_comm (2 * _ + _),
      ←tsub_eq_iff_eq_add_of_le] at hn
  · rw [Nat.add_succ, Nat.succ_eq_add_one, add_tsub_add_eq_tsub_right, Nat.succ_eq_add_one,
        add_comm k, add_assoc, add_tsub_assoc_of_le, add_comm, eq_comm, Finset.card_eq_succ] at hn
    · obtain ⟨g, s, _, hg', _⟩ := hn
      refine' ⟨g, _⟩
      simpa using hg'.le (Finset.mem_insert_self g _)
    · rw [Nat.succ_le] at this
      rw [←two_mul]
      refine' Nat.mul_le_mul_left _ _
      rw [←Nat.lt_succ]
      simpa using this
  · rwa [←two_mul]

-- 1.10. Suppose the order of g is odd. What can you say about the order of g^2?
lemma exercise110 {G : Type _} [Group G] {g : G} (hg : Odd (orderOf g)) :
    orderOf (g ^ 2) = orderOf g := by
  rw [orderOf_pow' _ two_ne_zero, Nat.coprime_iff_gcd_eq_one.mp, Nat.div_one]
  obtain ⟨k, hk⟩ := hg
  simp [hk]

-- 1.11. Prove that for all g, h in a group G, |gh| = |hg|.
-- (Hint: Prove that |a * g * a⁻¹| = |g| for all a, g in G.)
lemma conj_pow' {G : Type _} [Group G] (a g : G) (n : ℕ) :
    (a * g * a⁻¹) ^ n = a * g ^ n * a⁻¹ := by
  induction' n with n IH generalizing g
  · simp
  rw [pow_succ, IH, mul_assoc, ←mul_assoc a⁻¹, ←mul_assoc, ←mul_assoc a⁻¹, inv_mul_self, one_mul,
      mul_assoc _ g, ←pow_succ]

lemma exercise111' {G : Type _} [Group G] (a g : G) :
    orderOf (a * g * a⁻¹) = orderOf g := by
  generalize hk : orderOf (a * g * a⁻¹) = k
  generalize hn : orderOf g = n
  have := pow_orderOf_eq_one (a * g * a⁻¹)
  have hg' := pow_orderOf_eq_one g
  rw [←mul_right_inj a, mul_one, ←mul_inv_eq_one, ←conj_pow'] at hg'
  rw [conj_pow', mul_inv_eq_one, mul_right_eq_self] at this
  rcases n.zero_le.eq_or_lt with rfl|npos
  · rw [orderOf_eq_zero_iff'] at hn
    cases' k with k
    · rfl
    · rw [hk] at this
      exact absurd this (hn _ Nat.succ_pos')
  rcases k.zero_le.eq_or_lt with rfl|kpos
  · rw [orderOf_eq_zero_iff'] at hk
    exact absurd hg' (hk _ (npos.trans_le hn.ge))
  rw [←hk, ←hn]
  exact le_antisymm (orderOf_le_of_pow_eq_one (npos.trans_le hn.ge) hg')
    (orderOf_le_of_pow_eq_one (kpos.trans_le hk.ge) this)

lemma exercise111 {G : Type _} [Group G] (g h : G) :
    orderOf (g * h) = orderOf (h * g) := by
  rw [←exercise111' h (g * h), mul_assoc, mul_assoc, mul_inv_self, mul_one]

-- 1.12. In the group of invertible 2 x 2 matrices, consider
-- g = (0 -1; 1 0); h = (0 1; -1 -1)
-- Verify that |g| = 4, |h| = 3, and |gh| = oo. [§1.6]
lemma exercise112 : orderOf (!![0, -1; 1, 0] : Matrix _ _ ℚ) = 4 := by
  rw [orderOf_eq_iff zero_lt_four]
  constructor
  · rw [show 4 = 2 + 2 from rfl, pow_add, pow_two]
    ext i j : 2
    rw [Matrix.one_apply]
    rcases i with ⟨_|_|_, hi⟩ <;> rcases j with ⟨_|_|_, hj⟩
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
  · intros m hm _ H
    interval_cases m
    · simpa using congr_fun₂ H 0 0
    · simpa [pow_succ] using congr_fun₂ H 0 0
    · simpa [pow_succ] using congr_fun₂ H 0 0

lemma exercise112' : orderOf (!![0, 1; -1, -1] : Matrix _ _ ℚ) = 3 := by
  rw [orderOf_eq_iff zero_lt_three]
  constructor
  · rw [show 3 = 2 + 1 from rfl, pow_add, pow_two, pow_one]
    ext i j : 2
    rw [Matrix.one_apply]
    rcases i with ⟨_|_|_, hi⟩ <;> rcases j with ⟨_|_|_, hj⟩
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
    · simp [Nat.succ_eq_add_one, Nat.succ_lt_succ_iff] at hi hj
  · intros m hm _ H
    interval_cases m
    · simpa using congr_fun₂ H 0 0
    · simpa [pow_succ] using congr_fun₂ H 0 0

lemma exercise112'' (g h : Units (Matrix (Fin 2) (Fin 2) ℚ))
    (hg : g = ⟨!![0, -1; 1, 0],
      !![0, -1; 1, 0] ^ 3,
      by rw [←pow_succ, show 3 + 1 = 4 from rfl, ←exercise112, pow_orderOf_eq_one],
      by rw [←pow_succ', show 3 + 1 = 4 from rfl, ←exercise112, pow_orderOf_eq_one]⟩)
    (hh : h = ⟨!![0, 1; -1, -1],
      !![0, 1; -1, -1] ^ 2,
      by rw [←pow_succ, show 2 + 1 = 3 from rfl, ←exercise112', pow_orderOf_eq_one],
      by rw [←pow_succ', show 2 + 1 = 3 from rfl, ←exercise112', pow_orderOf_eq_one]⟩) :
    orderOf (g * h) = 0 := by
  rw [orderOf_eq_zero_iff']
  intros n hn
  have hm : ((g * h) : Matrix _ _ ℚ) = !![1, 1; 0, 1]
  · simp [hg, hh]
  suffices : ∀ n : ℕ, (Units.val (g * h) ^ n) = !![(1 : ℚ), n; 0, 1]
  · intro H
    specialize this n
    rw [←Units.val_pow_eq_pow_val, H] at this
    have this := congr_fun₂ this 0 1
    simp only [Units.val_one, ne_eq, Matrix.one_apply_ne, Matrix.of_apply, Matrix.cons_val',
               Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
               Matrix.cons_val_fin_one, Matrix.cons_val_zero] at this
    rw [←Nat.cast_zero, Nat.cast_inj] at this
    exact absurd this hn.ne
  rw [hm]
  clear hn n
  intro n
  induction' n with n IH
  · simp
  rw [pow_succ, Matrix.mul_eq_mul, IH]
  simp

-- 1.13. Give an example showing that |gh| is not necessarily equal to lcm(|g|, |h|),
-- even if g and h commute. [§1.6, 1.14]
example : ∃ (G : Type _) (inst : Group G) (g h : G),
    orderOf (g * h) ≠ Nat.lcm (orderOf g) (orderOf h) := by
  refine' ⟨Multiplicative (Fin 2), _, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1, _⟩
  infer_instance
  rw [Nat.lcm_self]
  change addOrderOf ((0 : Fin 2)) ≠ (addOrderOf (1 : Fin 2))
  rw [addOrderOf_zero, ne_comm, ne_eq, AddMonoid.addOrderOf_eq_one_iff]
  simp

-- 1.14. As a counterpoint to Exercise 1.13, prove that if g and h commute and gcd(|g|, |h|) = 1,
-- then |gh| = |g|*|h|. (Hint: Let N = |gh|; then g^N = (h⁻¹)^N.
-- What can you say about this element?) [§1.6, 1.15, §IV.2.5]
lemma exercise114 {G : Type _} [Group G] (g h : G) (hc : Commute g h)
    (hg : Nat.gcd (orderOf g) (orderOf h) = 1) : orderOf (g * h) = orderOf g * orderOf h := by
  have : orderOf (g * h) ∣ Nat.lcm (orderOf g) (orderOf h) := hc.orderOf_mul_dvd_lcm
  rw [Nat.coprime.lcm_eq_mul hg] at this
  refine' this.antisymm _
  refine' Nat.coprime.mul_dvd_of_dvd_of_dvd hg (Nat.coprime.dvd_of_dvd_mul_right hg _)
    (Nat.coprime.dvd_of_dvd_mul_left (Nat.coprime.symm hg) _)
  · rw [orderOf_dvd_iff_pow_eq_one, ←mul_left_inj (h ^ _), ←hc.mul_pow, pow_mul, pow_orderOf_eq_one,
        one_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_mul, one_pow]
  · rw [orderOf_dvd_iff_pow_eq_one, ←mul_left_inj (g ^ _), ←hc.symm.mul_pow, hc, mul_comm,
        pow_mul, pow_orderOf_eq_one, one_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_mul,
        one_pow]

-- 1.15. Let G be a commutative group, and let g ∈ G be an element of maximal finite order, that is,
-- such that if h ∈ G has finite order, then |h| ≤ |g|. Prove that in fact if h has finite order in
-- G, then |h| divides |g|. (Hint: Argue by contradiction. If |h| is finite but does not divide |g|,
-- then there its a prime integer p such that |g| = p^m * r, |h| = p^n * s, with r and s relatively
-- prime to p and m < n. Use Exercise 1.14 to compute the order of (g ^ (p ^ m)) * h ^ s.)
-- [§2.1, 4.11, IV.6.15]
lemma exercise115 {G : Type _} [CommGroup G] (g : G) (hg : IsOfFinOrder g)
    (hm : ∀ h : G, IsOfFinOrder h → orderOf h ≤ orderOf g) (h : G) (hh : IsOfFinOrder h) :
    orderOf h ∣ orderOf g := by
  have hl := hm h hh
  cases' hl.eq_or_lt with hl hl
  · simp [hl]
  have key : ∀ k l : ℕ, 1 < k → k < l → ¬ k ∣ l → ∃ p m n r s, l = p ^ m * r ∧ k = p ^ n * s ∧ Nat.Prime p ∧
    Nat.coprime p r ∧ Nat.coprime p s ∧ m < n
  · intros k
    induction' k using Nat.strongInductionOn with k IH
    intros l hk1 hkl hnd
    by_cases H : Nat.minFac k ∣ l
    · obtain ⟨x, hx⟩ := H
      by_cases hkp : Nat.Prime k
      · rw [hkp.minFac_eq] at hx
        exact absurd ⟨x, hx⟩ hnd
      specialize IH (k / Nat.minFac k) (Nat.div_lt_self (zero_lt_one.trans hk1)
        (Nat.Prime.one_lt (Nat.minFac_prime hk1.ne'))) x _ _ _
      · rw [Nat.lt_div_iff_mul_lt (Nat.minFac_dvd _), mul_one]
        exact (Nat.not_prime_iff_minFac_lt hk1).mp hkp
      · exact (Nat.div_lt_div_of_lt_of_dvd ⟨x, hx⟩ hkl).trans_le (Nat.div_le_of_le_mul hx.le)
      · refine' mt _ hnd
        rw [hx]
        intro H
        convert ((Nat.mul_dvd_mul_iff_left (Nat.minFac_pos _)).mpr H).trans (Nat.dvd_refl _)
        rw [Nat.mul_div_cancel' (Nat.minFac_dvd _)]
      obtain ⟨p, m, n, r, s, hr, hs, hp, hpr, hps, hmn⟩ := IH
      by_cases hp' : p = Nat.minFac k
      · refine' ⟨p, m + 1, n + 1, r, s, _, _, hp, hpr, hps, _⟩
        · rw [pow_succ, mul_assoc, ←hr, hp', hx]
        · rw [pow_succ, mul_assoc, ←hs, hp', Nat.mul_div_cancel' (Nat.minFac_dvd _)]
        · rwa [Nat.succ_lt_succ_iff]
      · refine' ⟨p, m, n, r * Nat.minFac k, s * Nat.minFac k, _, _, hp, hpr.mul_right _, hps.mul_right _, hmn⟩
        · rw [←mul_assoc, ←hr, mul_comm, hx]
        · rw [←mul_assoc, ←hs, Nat.div_mul_cancel (Nat.minFac_dvd _)]
        · exact hp.coprime_iff_not_dvd.mpr (mt ((Nat.prime_dvd_prime_iff_eq hp (Nat.minFac_prime hk1.ne')).mp) hp')
        · exact hp.coprime_iff_not_dvd.mpr (mt ((Nat.prime_dvd_prime_iff_eq hp (Nat.minFac_prime hk1.ne')).mp) hp')
    refine' ⟨Nat.minFac k, 0, Nat.factorization k (Nat.minFac k), l, k / (ord_proj[Nat.minFac k] k),
      _, _, Nat.minFac_prime hk1.ne', _, _, _⟩
    · simp
    · rw [Nat.mul_div_cancel']
      exact Nat.ord_proj_dvd _ _
    · rwa [(Nat.minFac_prime hk1.ne').coprime_iff_not_dvd]
    · exact Nat.coprime_ord_compl (Nat.minFac_prime hk1.ne') (zero_lt_one.trans hk1).ne'
    · exact (Nat.minFac_prime hk1.ne').factorization_pos_of_dvd (zero_lt_one.trans hk1).ne' (Nat.minFac_dvd _)
  cases' (Nat.succ_le_of_lt (orderOf_pos' hh) : 1 ≤ orderOf h).eq_or_lt with hh1 hh1
  · simp [←hh1]
  by_contra H
  obtain ⟨p, m, n, r, s, key⟩ := key (orderOf h) (orderOf g) hh1 hl H
  have hgo : orderOf (g ^ (p ^ m)) ∣ r
  · rw [orderOf_dvd_iff_pow_eq_one]
    rw [←pow_mul, ←key.left, pow_orderOf_eq_one]
  have hho : orderOf (h ^ s) ∣ p ^ n
  · rw [orderOf_dvd_iff_pow_eq_one]
    rw [←pow_mul, mul_comm, ←key.right.left, pow_orderOf_eq_one]
  have := exercise114 (g ^ (p ^ m)) (h ^ s) (mul_comm _ _)
    (((key.right.right.right.left.pow_left _).coprime_dvd_right hgo).coprime_dvd_left hho).symm
  rcases r.zero_le.eq_or_lt with rfl|rpos
  · simp [orderOf_eq_zero_iff, hg] at key
  rcases s.zero_le.eq_or_lt with rfl|spos
  · simp [orderOf_eq_zero_iff, hh] at key
  rw [orderOf_pow'' _ _ hg, orderOf_pow'' _ _ hh, key.left, key.right.left, Nat.gcd_mul_right_left,
      Nat.gcd_mul_left_left, Nat.mul_div_cancel _ spos,
      Nat.mul_div_cancel_left _ (pow_pos key.right.right.left.pos _)] at this
  specialize hm (g ^ p ^ m * h ^ s) _
  · rw [isOfFinOrder_iff_pow_eq_one]
    refine' ⟨r * p ^ n, mul_pos rpos (pow_pos key.right.right.left.pos _), _⟩
    rw [←this, pow_orderOf_eq_one]
  rw [this, key.left, mul_comm, mul_le_mul_right rpos,
      pow_le_pow_iff (Nat.lt_of_succ_le key.right.right.left.two_le)] at hm
  exact key.right.right.right.right.right.not_le hm
