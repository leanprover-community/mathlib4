/- ---------------------------------------------------------------------------------------------
     École thématique XIII _Philosophie et mathématiques_
     (22–26 juin 2026, Saint Ferréol)
     Antoine Chambert-Loir <antoine.chambert-loir@u-pariscite.fr>
     [https://webusers.imj-prg.fr/~antoine.chambert-loir/exposes/20260623-EcoleThematique.lean]
   --------------------------------------------------------------------------------------------- -/

import Mathlib

-- #check est une fonction de Lean qui affiche un type
#check ℕ

/-! ---------------------------------------------------------
    # Le 5e nombre de Fermat n'est pas premier (Euler, 1732)
    --------------------------------------------------------- -/

/-- Nombres de Fermat -/
def F (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

#check F

-- Fermat avait dit que F 1, F 2, F 3, F 4,… étaient des nombres premiers
#eval F 1
#eval Nat.Prime (F 1)

#eval F 2
#eval Nat.Prime (F 2)

#eval F 3
#eval Nat.Prime (F 3)

#eval F 4
#eval Nat.Prime (F 4)

#eval F 5
#eval Nat.Prime (F 5)

-- Mais F 5 n'est pas premier (Euler), il est divisible par 641
#eval Nat.minFac (F 5) -- 641

theorem eulerFermat5 : ¬ (Nat.Prime (F 5)) := by
  simp [F]; norm_num

theorem eulerFermat5' : ¬ (Nat.Prime (F 5)) := by
  intro h
  have h641 : 641 ∣ F 5 := by
    rw [F]
    norm_num
  have := Nat.Prime.eq_one_or_self_of_dvd h _ h641
  simp [F] at this

lemma euler1 : (641 : ℤ) = 2 ^ 7 * 5 + 1 := by rfl

lemma euler1' : 2 ^ 7 * 5 ≡ -1 [ZMOD 641] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd, Int.sub_neg, euler1]
  -- Lean conclut parce que `rfl` connaît `Int.ModEq.refl`

lemma euler1'' : 2 ^ 28 * 5 ^ 4 ≡ 1 [ZMOD 641] := by
  rw [show 28 = 7 * 4 from by rfl, pow_mul, ← mul_pow]
  trans
  · exact Int.ModEq.pow 4 euler1'
  · simp

lemma euler2 : (641 : ℤ) = 5 ^ 4 + 2 ^ 4 := by rfl

lemma euler2' : (5 : ℤ) ^ 4 ≡ - 2 ^ 4 [ZMOD 641] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd, Int.sub_neg, euler2]

theorem euler641 : 641 ∣ F 5 := by
  rw [← Nat.modEq_zero_iff_dvd, ← Int.natCast_modEq_iff]
  rw [F, show 2 ^ 5 = 32 from by rfl]
  rw [Int.natCast_add, Int.natCast_pow]
  rw [Nat.cast_ofNat, Int.natCast_one, Nat.cast_ofNat, Int.natCast_zero]
  apply Int.ModEq.add_right_cancel' (c := -1)
  rw [add_assoc, Int.add_right_neg, add_zero, zero_add]
  have := (Int.ModEq.mul_left (2 ^ 28) euler2').symm
  have := Int.ModEq.trans this euler1''
  rw [Int.mul_neg, ← pow_add] at this
  rw [show 28 + 4 = 32 from by rfl] at this
  have := this.neg
  rwa [neg_neg] at this

theorem fermatEuler5 : ¬ Nat.Prime (F 5) := by
  intro hF5
  have := Nat.Prime.eq_one_or_self_of_dvd hF5 _ euler641
  simp only [OfNat.ofNat_ne_one, false_or] at this
  simp [F] at this

/-! ---------------------------------------------
    # Principe de récurrence et nombres entiers
    --------------------------------------------- -/

-- la commande Lean `#print` affiche un type
#print Nat
/- Le type Nat (ℕ) des entiers est un type inductif ayant 2 constructeurs :
   - Nat.zero : ℕ
   - Nat.succ : ℕ → ℕ  -/

-- Le principe de récurrence pour ℕ
#check Nat.rec

/- Nous allons montrer comment la définition de ce type inductif permet
d'y définir les opérations algébriques.
Pour éviter l'interaction avec les définitions existantes sur le type `ℕ`,
nous définissons un autre type et repartons à zéro. -/

inductive nat
  | zero : nat
  | succ : nat → nat

namespace nat

-- Cette instance permet d'accéder à la notation `0` pour `nat.zero`.
instance : Zero nat := ⟨zero⟩
@[simp] theorem zero_eq : (zero : nat) = 0 := rfl

-- Nous introduisons la notation `⁺` pour le successeur.
local notation n"⁺" => succ n

/-- Définition de l'addition par récurrence sur la seconde variable -/
protected def add (m n : nat) : nat :=
  match n with
  | 0 => m
  | (succ n) => (nat.add m n)⁺

-- Cette instance permet d'utiliser la notation `+` (infixe) pour `nat.add`.
instance : Add nat := ⟨nat.add⟩

@[simp] theorem add_zero (m : nat) : m + 0 = m := rfl

theorem add_succ (m n : nat) : m + n⁺ = (m + n)⁺ := rfl

theorem add_assoc (m n p : nat) : m + n + p = m + (n + p) := by
  induction p with
  | zero =>
    calc
      m + n + 0 = m + n := by rw [add_zero]
      _ = m + (n + 0) := by rw [add_zero]
  | succ p ih =>
    calc
      m + n + p⁺ = (m + n + p)⁺ := by rw [add_succ]
      _ = (m + (n + p))⁺ := by rw [ih]
      _ = m + (n + p)⁺ := by rw [add_succ]

theorem zero_add (n : nat) : 0 + n = n := by
  induction n with
  | zero => rw [zero_eq, add_zero]
  | succ n ih =>
    calc
      0 + n⁺ = (0 + n)⁺ := by rw [add_succ]
      _ = n⁺ := by rw [ih]

theorem succ_add (m n : nat) : m⁺ + n = (m + n)⁺ := by
  induction n generalizing m with
  | zero => simp
  | succ n ih => rw [add_succ, ih, add_succ]

theorem add_comm (m n : nat) : m + n = n + m := by
  induction n generalizing m with
  | zero => rw [zero_eq, add_zero, zero_add]
  | succ n ih => rw [add_succ, ih, succ_add]

/-- Définition de la multiplication par récurrence sur la seconde variable -/
protected def mul (m n : nat) : nat :=
  match n with
  | 0 => 0
  | (succ n) => (nat.mul m n) + m

-- Cette instance permet d'accéder à la notation infixe `*`.
instance : Mul nat := ⟨nat.mul⟩

theorem mul_zero (m : nat) : m * 0 = 0 := rfl
theorem mul_succ (m n : nat) : m * n⁺ = m * n + m := rfl

theorem zero_mul (n : nat) : 0 * n = 0 := by
  induction n with
  | zero => rw [zero_eq, mul_zero]
  | succ n ih => rw [mul_succ, ih, zero_add]

-- Cette instance permet d'accéder à la notation `1` pour `0⁺`.
instance : One nat := ⟨0⁺⟩
theorem one_def : 1 = (0 : nat)⁺ := rfl
theorem zero_succ : (0 : nat)⁺ = 1 := rfl

theorem add_one (n : nat) : n⁺ = n + 1 := rfl

theorem mul_one (m : nat) : m * 1 = m := by
  rw [← zero_succ, mul_succ, mul_zero, zero_add]

theorem one_mul (n : nat) : 1 * n = n := by
  induction n with
  | zero => rfl -- rw [zero_eq, mul_zero]
  | succ n ih => rw [mul_succ, ih, add_one]

theorem mul_add (m n p : nat) : m * (n + p) = m * n + m * p := by
  induction p generalizing m n with
  | zero => rw [zero_eq, add_zero, mul_zero, add_zero]
  | succ p ih =>
    rw [add_succ, mul_succ, ih, mul_succ, add_assoc]

theorem add_mul (m n p : nat) : (m + n) * p = m * p + n * p := by
  induction p generalizing m n with
  | zero => rfl
  | succ p ih =>
    rw [mul_succ, mul_succ, mul_succ, add_assoc, ← add_assoc m,
      add_comm m (n * p), add_assoc (n * p), ← add_assoc (m * p),
      ← ih]

theorem mul_assoc (m n p : nat) : m * n * p = m * (n * p) := by
  induction p generalizing m n with
  | zero => rw [zero_eq, mul_zero, mul_zero, mul_zero] -- rfl
  | succ p ih => rw [mul_succ, mul_succ, mul_add, ih]

theorem mul_comm (m n : nat) : m * n = n * m := by
  induction n generalizing m with
  | zero => rw [zero_eq, mul_zero, zero_mul]
  | succ n ih => rw [mul_succ, ih, add_one, add_mul, one_mul]

-- Cette instance munit le type `nat` d'une structure de semi-anneau commutatif.
instance : CommSemiring nat where
  add_comm := nat.add_comm
  add_assoc := nat.add_assoc
  zero_add := nat.zero_add
  add_zero := nat.add_zero
  mul_comm := nat.mul_comm
  mul_assoc := nat.mul_assoc
  mul_zero := nat.mul_zero
  zero_mul := nat.zero_mul
  one_mul := nat.one_mul
  mul_one := nat.mul_one
  left_distrib := nat.mul_add
  right_distrib := nat.add_mul
  -- For Lean, a CommSemiring has an action of ℕ
  nsmul := nsmulRec

/- Par cette instance, Lean construit une fonction `Nat.cast : ℕ → n`
et sa version `Nat.castRingHom nat : ℕ →+* nat` qui est un morphisme d'anneaux. -/
example : ℕ →+* nat := by exact Nat.castRingHom nat
example : ℕ → nat := by exact Nat.cast

/-- Définition de la fonction puissance par récurrence sur la seconde variable. -/
protected def pow (m n : nat) : nat :=
  match n with
  | 0 => 1
  | (succ n) => (nat.pow m n) * m

-- Cette instance fournit la notation `^` pour `nat.pow`.
instance : Pow nat nat := ⟨nat.pow⟩

theorem pow_zero (m : nat) : m ^ (0 : nat) = 1 := rfl
theorem pow_succ (m n : nat) : m ^ n⁺ = m ^ n * m := rfl

theorem pow_one (m : nat) : m ^ (1 : nat) = m := by
  rw [one_def, pow_succ, pow_zero, one_mul]

theorem pow_add (m n p : nat) : m ^ (n + p) = m ^ n * m ^ p := by
  induction p with
  | zero => rw [zero_eq, add_zero, pow_zero, mul_one]
  | succ p ih => rw [add_succ, pow_succ, ih, mul_assoc, ← pow_succ]

example (m n : ℕ) : (m : nat) * n = ((m * n : ℕ) : nat) := by
  simp only [Nat.cast_mul]

theorem pow_cast (m : nat) (n : ℕ) : m ^ (n : nat) = m ^ n := by
  induction n with
  | zero => simp [pow_zero]
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, pow_add, pow_one]
    rw [ih, _root_.pow_succ]

-- La tactique `ring` permet de prouver une relation à partir des axiomes des (semi-)anneaux.
example (x y : nat) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

-- Dans cet exemple, les `2` sont de type `ℕ` !
-- On veut le prouver en insistant que `2 : nat`.

example (x y : nat) :
    (x + y) ^ (2 : nat) = x ^ (2 : nat) + (2 : nat) * x * y + y ^ (2 : nat) := by
  -- La tactique `ring` échoue, car elle n'a pas accès à la puissance `^ (2 : nat)`.
  -- Elle propose de se contenter d'une tactique `ring_nf` de normalisation.
  ring
  sorry

theorem one_succ : (1 : nat)⁺ = 2 := rfl

theorem mul_two (m : nat) : m * 2 = m + m := by
  rw [← one_succ, mul_succ, mul_one]

theorem two_mul (m : nat) : 2 * m = m + m := by
  rw [← one_succ, add_one, add_mul, one_mul]

theorem pow_two (m : nat) : m ^ (2 : nat) = m * m := by
  rw [← one_succ, pow_succ, pow_one]

example (x y : nat) :
    (x + y) ^ (2 : nat) = x ^ (2 : nat) + (2 : nat) * x * y + y ^ (2 : nat) := by
  rw [pow_two, add_mul, mul_add, mul_add]
  rw [← pow_two, ← pow_two, add_assoc, add_assoc]
  apply congr_arg₂ _ rfl
  rw [← add_assoc]
  apply congr_arg₂ _ _ rfl
  rw [mul_comm y, two_mul, add_mul]

end nat

/-! -------------------------
    # Fonctions et ensembles               -
    ------------------------- -/


#check Function.Injective
#print Function.Injective

variable {α β γ : Type*} (f : α → β) (g : β → γ)

example : Function.Injective (g ∘ f) → Function.Injective f := by
  intro H a a' h
  apply H
  rw [Function.comp_apply, Function.comp_apply, h]

example : Function.Injective f → Function.Injective g → Function.Injective (g ∘ f) := by
  intro H H' a a' h
  apply H
  apply H'
  -- simp only [Function.comp_apply] at h
  exact h

example : Function.Surjective (g ∘ f) → Function.Surjective g := by
  intro H c
  obtain ⟨a, h⟩ := H c
  rw [Function.comp_apply] at h
  use f a

example : Function.Surjective f → Function.Surjective g → Function.Surjective (g ∘ f):= by
  intro H H' c
  obtain ⟨b, h'⟩ := H' c
  obtain ⟨a, h⟩ := H b
  use a
  rw [Function.comp_apply, h, h']

example : Function.Injective (g ∘ f) →  Function.Surjective f → Function.Injective g := by
  intro H' H b b' hbb'
  obtain ⟨a, h⟩ := H b
  obtain ⟨a', h'⟩ := H b'
  rw [← h, ← h'] at hbb'
  replace H' := H' hbb'
  rw [← h, ← h', H']

example : Function.Surjective (g ∘ f) → Function.Injective g → Function.Surjective f := by
  intro H' H b
  obtain ⟨a, h⟩ := H' (g b)
  rw [Function.comp_apply] at h
  use a
  exact H h

-- Une bonne partie des preuves précédentes est automatisée par la tactique `aesop`

-- `Set α` est le type des parties d'un type `α`.
#check Set

#check Set.inter
#print Set.inter


-- Théorème de Cantor : il n'y a pas de surjection de `α` sur `Set α`.
theorem Cantor (f : α → Set α) : ¬ Function.Surjective f := by
  intro H
  set c := {a : α | a ∉ f a} with hc
  obtain ⟨a, ha⟩ := H c
  have : a ∈ c ↔ a ∉ c := by
    constructor
    · intro h
      rw [hc, Set.mem_setOf_eq]
      intro h'
      apply h'
      rwa [ha]
    · intro h
      let h' := h
      rw [hc, Set.mem_setOf_eq, ha] at h'
      exact (h' h).elim
  exact iff_not_self this

/- ---------------------------------------- -/




