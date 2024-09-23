/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec

/-!
# Degrees of unsolvability

This file introduces many-one reducibility (mapping reducibility) and
proves its basic properties.

We work with two classes of functions, C₀ (which includes both 𝓓₁ and 𝓓ₘ and
any monoid of functions)
C₁ (which fits 𝓓₁ and 𝓓ₘ but not as general as C₁)
and C₂ (which includes 𝓓ₘ but not 𝓓₁).

- We show over C₁ that the degrees are not rigid, using complementation.

- Over C₂ we show that the degrees form an upper semilattice and has
a peculiar automorphism that simply swaps ∅ₘ and ℕₘ.

- The halting problem `K` is defined in this context and
its basic degree-theoretic properties established.
-/


/-

## m-reducibility

The basic definitions at the level of sets.

monoid (C₀) vs. clone (C₂)

-/

/-- An arbitrary monoid. -/
structure C₀ where
  func : (ℕ → ℕ) → Prop
  id : func id
  comp : ∀ {f g}, func f → func g → func (f ∘ g)


/-- A monoid in which we can prove ⊕ is an upper bound, even if not the least one.
Perhaps dangerous to call the fields `inl` and `inr`.
Note that (join f₁ f₂) ∘ inl = f₁ in some sense.
-/
structure C₁ extends C₀ where
  inl : func (fun k => 2 * k)
  inr : func (fun k => 2 * k + 1)

def injClone : C₁ := {
  func := Function.Injective
  id := fun ⦃a₁ a₂⦄ a ↦ a
  comp := Function.Injective.comp
  inl := by refine mul_right_injective₀ ?ha;exact Ne.symm (Nat.zero_ne_add_one 1)
  inr := by
    apply Function.Injective.comp
    exact Nat.succ_injective
    simp
    refine mul_right_injective₀ ?ha
}


def m_reducible {C : C₀}  (A B : ℕ → Bool) := ∃ f : ℕ → ℕ, C.func f ∧ ∀ x, A x = B (f x)
def m_equivalent {C : C₀} (A B : ℕ → Bool) := @m_reducible C A B ∧ @m_reducible C B A



infix:50 " ≤ₘ " => m_reducible
infix:50 " ≡ₘ " => m_equivalent


/-

## Basic properties of ≤ₘ

-/

lemma m_refl {C : C₀} : Reflexive (@m_reducible C ):=
  fun _ => ⟨ id, ⟨C.id, fun _ => rfl⟩⟩

lemma m_trans {D : C₀} : Transitive (@m_reducible D) := by
  intro A B C ⟨g₁,hg₁⟩ ⟨g₂,hg₂⟩
  use g₂ ∘ g₁
  constructor
  apply D.comp
  exact hg₂.1
  exact hg₁.1
  intro x
  rw [hg₁.2 x, hg₂.2 (g₁ x)];rfl

instance {C : C₀} : Trans (@m_reducible C) (@m_reducible C) (@m_reducible C) := {
  trans := @m_trans C
}


/-

## Basic properties of ≡ₘ

-/

lemma m_equiv_refl {C : C₀} : Reflexive (@m_equivalent C) := fun _ => ⟨m_refl _, m_refl _⟩

lemma m_equiv_trans {C : C₀} : Transitive (@m_equivalent C) := by
  intro A B C h₁ h₂
  unfold m_equivalent at *
  constructor
  exact m_trans h₁.1 h₂.1
  exact m_trans h₂.2 h₁.2

lemma m_equiv_symm {C : C₀} : Symmetric (@m_equivalent C) := by
  intro A B h
  unfold m_equivalent at *
  constructor
  tauto;tauto

lemma m_equiv_equiv {C : C₀} : Equivalence (@m_equivalent C) :=
{
  refl := m_equiv_refl,
  symm := by have := @m_equiv_symm C; exact this,
  trans := by have := @m_equiv_trans C; exact this
}


/-

## The degree structure 𝓓ₘ, using quotients

`Quot` is like `Quotient` when the relation is not necessarily an equivalence.
We could do: def 𝓓ₘ' := Quot m_equivalent
-/
abbrev 𝓓ₘsetoid {C : C₀}: Setoid (ℕ → Bool) := {
  r := @m_equivalent C
  iseqv := m_equiv_equiv
}

/-- The many-one degrees. -/
abbrev 𝓓ₘ {C : C₀} := @Quotient (ℕ → Bool) <|@𝓓ₘsetoid C

/-- Equivalent reals have equal upper cones. -/
lemma upper_cones_eq {C : C₀} (A B : ℕ → Bool) (h : @m_equivalent C A B) :
    @m_reducible C A = @m_reducible C B :=
  Set.ext <| fun _ => Iff.intro (m_trans h.2) (m_trans h.1)

/-- Equivalent reals have equal degrees. -/
lemma degrees_eq {C : C₀} (A B : ℕ → Bool) (h : @m_equivalent C A B) :
    @m_equivalent C A = @m_equivalent C B :=
  Set.ext <| fun _ => Iff.intro (m_equiv_trans (m_equiv_symm h)) (m_equiv_trans h)

/-- As an auxiliary notion, we define [A]ₘ ≤ b to mean
that the degree of A is below the degree b. -/
def le_m' {E : C₀} (A : ℕ → Bool) (b : @𝓓ₘ E) : Prop := by
  apply Quot.lift
  · intro C D
    intro (hCD : m_equivalent C D)
    show @m_reducible E A C = @m_reducible E A D
    exact eq_iff_iff.mpr <| Iff.intro (fun h => m_trans h hCD.1) fun h => m_trans h hCD.2
  · exact b

/-- The ordering of the m-degrees. -/
def le_m {E : C₀} (a b : @𝓓ₘ E) : Prop := by
  apply Quot.lift
  · intro C D
    intro (hCD : C ≡ₘ D)
    show le_m' C b = le_m' D b
    simp
    unfold le_m'
    apply Eq.to_iff
    congr
    exact Set.ext fun A => ⟨m_trans hCD.2, m_trans hCD.1⟩
  · exact a

/-

## Basic properties of the m-degrees

-/

/-- The ordering of m-degrees is reflexive. -/
lemma le_m_refl {C : C₀} : Reflexive <|@le_m C :=
  Quot.ind <| fun _ => m_refl _

/-- The ordering of m-degrees is transitive. -/
lemma le_m_trans {C : C₀} : Transitive <|@le_m C :=
  Quot.ind fun _ => Quot.ind fun _ => Quot.ind fun _ h => m_trans h

def m_degrees_preorder {C : C₀} : Preorder (ℕ → Bool) :=
  @Preorder.mk (ℕ → Bool) {le := @m_reducible C}
  {lt := fun A B => m_reducible A B ∧ ¬ m_reducible B A}
    m_refl m_trans (by
      simp only;
      exact fun u v => by unfold m_reducible; trivial
    )

/-- For example 𝓓₁ is a partial order (if not a semilattice). -/
instance {E : C₀}: PartialOrder <|@𝓓ₘ E := {
  le := le_m
  le_refl := le_m_refl
  le_trans := le_m_trans
  le_antisymm := Quotient.ind <| fun A => Quotient.ind <| fun B h₁ h₂ => Quotient.sound ⟨h₁,h₂⟩
}

/-- AKA Quotient.mk 𝓓ₘsetoid (fun _ => false) -- or Quot.mk m_equivalent ... -/
def emp_m {E : C₀}: @𝓓ₘ E := ⟦ (fun _ => false) ⟧
def univ_m {E : C₀} : @𝓓ₘ E := ⟦ (fun _ => true) ⟧
def zero_m {E : C₀} : @𝓓ₘ E := ⟦ (fun k => ite (k=0) true false) ⟧

notation:60 " ∅ₘ " => emp_m

notation:60 " ℕₘ " => univ_m

/--

  ## The recursive join A ⊕ B.

(However, the symbol ⊕ has a different meaning in Lean.)
It is really a shuffle or ♯ (backslash sha).
-/
def join (A B : ℕ → Bool) := fun k => ite (Even k) (A (k/2)) <| B (k/2)

/-- Make sure ♯ binds stronger than ≤ₘ. -/
infix:70 " ⊕ " => join

lemma join_left {C : C₁}  (A B : ℕ → Bool) : @m_reducible C.toC₀ A (A ⊕ B) :=
  ⟨fun k => 2 * k, C.inl, fun k => by unfold join; simp⟩

lemma join_right {C : C₁} (A B : ℕ → Bool) : @m_reducible C.toC₀ B (A ⊕ B) :=
  ⟨fun k => 2 * k + 1, C.inr, fun k => by
    unfold join
    have : (2*k+1)/2 = (2*k)/2 := Nat.succ_div_of_not_dvd <| by simp
    rw [this]
    simp⟩




open Classical

noncomputable def botSwap {E : C₀} : @𝓓ₘ E → @𝓓ₘ E := fun a =>
  ite (a = ∅ₘ) (ℕₘ) (ite (a = ℕₘ) (∅ₘ) a)



theorem botSwap_inj {E : C₀} : Function.Injective fun a ↦
    if a = @emp_m E then ℕₘ else if a = ℕₘ then  ∅ₘ else a := by
  intro a b h
  simp_all
  split_ifs at h with g₀ g₁ g₂ g₃ g₄ g₅
  · apply Eq.trans;exact g₀
    exact g₁.symm
  · exfalso;
    rw [g₂] at g₁
    exact g₁ h
  · exfalso;exact g₂ h.symm
  · rw [g₃,h] at g₀
    exfalso;apply g₀;rfl
  · subst g₃;exact g₅.symm
  · exfalso;exact g₄ h.symm
  · exfalso;exact g₃ h
  · exfalso;exact g₀ h
  · exact h

theorem botSwap_surj {E : C₀} : Function.Surjective
    fun a ↦ if a = @emp_m E then  ℕₘ else if a = ℕₘ then  ∅ₘ else a := by
  · intro b
    simp
    by_cases H : b = ∅ₘ
    subst H
    use ℕₘ
    simp
    by_cases H : b = ℕₘ
    aesop
    aesop

lemma emp_not_below {E : C₀} : ¬ (@emp_m E) ≤ (ℕₘ) := by
  intro hc
  unfold emp_m univ_m at hc
  unfold 𝓓ₘ 𝓓ₘsetoid m_equivalent at hc
  obtain ⟨f,hf⟩ := hc
  simp at hf

lemma univ_not_below {E : C₀} : ¬ (@univ_m E) ≤ (∅ₘ) := by
  intro hc
  unfold emp_m univ_m at hc
  unfold 𝓓ₘ 𝓓ₘsetoid m_equivalent at hc
  obtain ⟨f,hf⟩ := hc
  simp at hf

theorem emp_min {E : C₀} : ∀ (a : @𝓓ₘ E), (h : a ≤ (∅ₘ)) →  a = ∅ₘ := by
  apply Quotient.ind
  intro A h
  obtain ⟨f,hf⟩ := h

  unfold emp_m at *
  unfold 𝓓ₘ 𝓓ₘsetoid m_equivalent m_reducible at *
  simp_all
  constructor
  use f
  use f
  simp_all

theorem univ_min {E : C₀} : ∀ (a : @𝓓ₘ E), (h : a ≤ (ℕₘ)) →  a = ℕₘ := by
  apply Quotient.ind
  intro A h
  obtain ⟨f,hf⟩ := h

  unfold univ_m at *
  unfold 𝓓ₘ 𝓓ₘsetoid m_equivalent m_reducible at *
  simp_all
  constructor
  use f
  use f
  simp_all


def automorphism {α : Type} [PartialOrder α] (π : α → α): Prop :=
  Function.Bijective π ∧ ∀ a b, a ≤ b ↔ π a ≤ π b

def cpl : (ℕ → Bool) → (ℕ → Bool) := fun A => (fun k => ! (A k))

def complementMap {E : C₀} : @𝓓ₘ E → @𝓓ₘ E := by
  apply Quotient.lift
  intro A B h
  show ⟦cpl A⟧ = ⟦cpl B⟧
  apply Quotient.sound
  obtain ⟨f₁,hf₁⟩ := h.1
  obtain ⟨f₂,hf₂⟩ := h.2
  constructor
  · use f₁
    unfold cpl
    constructor
    tauto
    intro x
    congr
    tauto
  · use f₂
    unfold cpl
    constructor
    tauto
    intro x
    congr
    tauto

lemma emp_univ_m_degree {E : C₀} : (@emp_m E) ≠ (ℕₘ) := by
  intro hc
  unfold emp_m univ_m at hc
  have : 𝓓ₘsetoid.r (fun _ => false) (fun _ => true) := Quotient.eq''.mp hc
  unfold 𝓓ₘsetoid m_equivalent at this
  simp at this
  obtain ⟨f,hf⟩ := this.1
  simp at hf

theorem botSwapNontrivial {E : C₀} : @botSwap E ≠ id := by
  intro hc
  have : ∀ a, @botSwap E a = id a := by exact fun a ↦ congrFun hc a
  specialize this (∅ₘ)

  unfold botSwap at this
  simp_all
  apply emp_univ_m_degree.symm
  exact this

def rigid (α : Type) [PartialOrder α] : Prop :=
  ∀ π, @automorphism α _ π → π  = id

/-

## Computability results needed for C₂
-/

lemma half_primrec : Primrec (fun k => k/2) :=
  Primrec.of_graph
    ⟨id, ⟨Primrec.id, by intro x;simp;omega⟩⟩
    (PrimrecRel.comp₂
      Primrec.eq
      (Primrec₂.comp₂ Primrec.nat_div Primrec₂.left <| Primrec₂.const 2)
      Primrec₂.right)

lemma comphalf_primrec {f : ℕ → ℕ} (hc : Computable f) :
    Computable (fun k => f (k / 2)) :=
  Computable.comp hc <|Primrec.to_comp half_primrec

lemma primrec_even_equiv : PrimrecPred fun k ↦ k / 2 * 2 = k := by
    apply PrimrecRel.comp
    exact Primrec.eq
    apply Primrec.of_graph
    use id
    simp only [Encodable.encode_nat, id_eq]
    exact ⟨Primrec.id, fun x => by omega⟩
    · exact (PrimrecRel.comp₂ Primrec.eq
      (Primrec₂.comp₂ Primrec.nat_mul
        (Primrec₂.comp₂ Primrec.nat_div Primrec₂.left <| Primrec₂.const 2) <| Primrec₂.const 2)
        Primrec₂.right)
    · exact Primrec.id

lemma even_div_two:
∀ (a : ℕ), a / 2 * 2 = a ↔ Even a := fun a => Iff.intro
      (fun h => ⟨a / 2, Eq.trans h.symm (mul_two (a/2))⟩) <| Nat.div_two_mul_two_of_even

lemma even_primrec : @PrimrecPred ℕ _ Even _ :=
  PrimrecPred.of_eq primrec_even_equiv even_div_two

theorem computable_join {f₁ f₂ : ℕ → ℕ} (hf₁ : Computable f₁) (hf₂ : Computable f₂) :
    Computable fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2) :=
  Computable.of_eq
    (Computable.cond (Primrec.to_comp even_primrec) (comphalf_primrec hf₁) (comphalf_primrec hf₂))
    (by intro n; simp)

theorem getHasIte {C : C₁}
  (hasIte₂ : ∀ {f₁ f₂}, C.func f₁ → C.func f₂ → C.func
    fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2)) :
   ∀ f, C.func f → C.func (fun k : ℕ => if Even k then f (k / 2) * 2 else k) := by
  intro f hf
  have : (fun k ↦ if Even k then ((fun a => a * 2) ∘ f) (k / 2) else
          (fun a => 2 * a + 1)  (k / 2))
        = fun k ↦ if Even k then f (k / 2) * 2 else k := by
    ext k
    split_ifs with g₀
    · rfl
    · show 2 * (k/2) + 1 = k
      obtain ⟨a,ha⟩ := odd_iff_exists_bit1.mp <| Nat.not_even_iff_odd.mp g₀
      subst ha
      omega
  rw [← this]
  exact @hasIte₂ ((fun a => a * 2) ∘ f) (fun a => 2 * a + 1)
    (C.comp (by simp_rw [mul_comm _ 2]; exact C.inl) hf) C.inr

/--

## C₂ : a monoid that is a "clone" and closer to closure under primitive recursion.

-/

def joinFun (f₁ f₂ : ℕ → ℕ) := fun k ↦ if Even k then f₁ (k / 2) else f₂ (k / 2)

structure C₂ extends C₁ where
  join : ∀ {f₁ f₂}, func f₁ → func f₂ → func (joinFun f₁ f₂)
  const : ∀ c, func (fun _ => c)

def comput : C₂ := {
  func  := Computable
  id    := Computable.id
  comp  := @Computable.comp ℕ ℕ ℕ _ _ _
  inl   := Primrec.to_comp Primrec.nat_double
  inr   := Primrec.to_comp <| Primrec.nat_double_succ
  join  := computable_join
  const := Computable.const
}

/-- The join A₀ ⊕ A₁ is monotone in A₀. -/
theorem join_le_join {C : C₂} {A₀ A₁ : ℕ → Bool} (h : @m_reducible C.toC₀ A₀ A₁) (B : ℕ → Bool) :
    @m_reducible C.toC₀ (A₀ ⊕ B) (A₁ ⊕ B) := by
  obtain ⟨f,hf⟩ := h
  use fun k => ite (Even k) (f (k/2) * 2) k
  constructor
  · exact getHasIte C.join _ hf.1
  · intro k
    unfold join
    split_ifs with g₀ g₁
    · rw [Nat.mul_div_left (f (k / 2)) Nat.zero_lt_two]
      exact hf.2 _
    · exact False.elim <| g₁ <| Nat.even_mul.mpr <| .inr <| Nat.even_iff.mpr rfl
    · rfl

/-- The join is bounded by each upper bound. -/
lemma join_le {E : C₂} {A B C : ℕ → Bool} (h₁ : @m_reducible E.toC₀ A C)
    (h₂ : @m_reducible E.toC₀ B C) :
    @m_reducible E.toC₀ (join A B) C := by
  obtain ⟨f₁,hf₁⟩ := h₁
  obtain ⟨f₂,hf₂⟩ := h₂
  use fun k => ite (Even k) (f₁ (k/2)) (f₂ (k/2))
  constructor
  · apply E.join
    exact hf₁.1
    exact hf₂.1
  · intro k
    unfold join
    split_ifs with h
    exact hf₁.2 (k/2)
    exact hf₂.2 (k/2)


/-- The m-degree `[A]ₘ ⊔ b`. -/
def join' {E : C₂} (A : ℕ → Bool) (b : Quot <|@m_equivalent E.toC₀) :
    Quot <|@m_equivalent E.toC₀ := by
  apply Quot.lift
  show ∀ B C, @m_equivalent E.toC₀ B C →
    Quot.mk m_equivalent (join A B) = Quot.mk m_equivalent (join A C)
  intro B C h;
  apply Quot.sound
  unfold m_equivalent at *
  constructor
  · apply join_le
    apply join_left
    calc
      B ≤ₘ C := h.1
      _ ≤ₘ _ := @join_right E.toC₁ _ _
  · apply join_le
    apply join_left
    calc
      C ≤ₘ B := h.2
      _ ≤ₘ _ := @join_right E.toC₁ _ _
  exact b



/-- 𝓓ₘ is a join-semilattice. -/
instance {E : C₂}: SemilatticeSup <|@𝓓ₘ E.toC₀ := {
  le := le_m
  le_refl := le_m_refl
  le_trans := le_m_trans
  le_antisymm := Quotient.ind <| fun A => Quotient.ind <| fun B h₁ h₂ => Quotient.sound ⟨h₁,h₂⟩

  le_sup_left  := Quotient.ind fun A => Quotient.ind fun B => by apply join_right
  le_sup_right := Quotient.ind fun A => Quotient.ind fun B => by apply join_left
  sup_le := Quotient.ind fun A => Quotient.ind fun B => Quotient.ind fun C h₁ h₂ => by
    exact join_le h₂ h₁
  sup := fun a => by
    apply Quotient.lift
    intro A B h
    show join' A a = join' B a
    unfold join'
    congr
    exact funext <| fun C => Quot.sound ⟨join_le_join h.1 C, join_le_join h.2 C⟩
}



/-- This is false for 1-degrees.
However, the complementing automorphism works there.
-/
theorem emp_univ {E : C₂} (B : ℕ → Bool) (h_2 : ¬⟦B⟧ = @emp_m E.toC₀ ) :
    (@univ_m E.toC₀) ≤ ⟦B⟧ := by
  unfold univ_m at *
  unfold 𝓓ₘ 𝓓ₘsetoid m_equivalent m_reducible at *
  by_cases H : B = (fun _ => false)
  · subst H
    exfalso
    apply h_2
    rfl
  · have : ∃ k, B k ≠ false := by
      contrapose H
      simp_all
      ext x;tauto
    obtain ⟨k,hk⟩ := this
    use fun _ => k
    simp_all
    exact E.const k

theorem univ_emp {E : C₂} (B : ℕ → Bool) (h_2 : ¬⟦B⟧ = @univ_m E.toC₀ ) : @emp_m E.toC₀ ≤ ⟦B⟧ := by
  unfold emp_m at *
  unfold 𝓓ₘ 𝓓ₘsetoid m_equivalent m_reducible at *
  by_cases H : B = (fun _ => true)
  subst H
  exfalso
  apply h_2
  rfl
  have : ∃ k, B k ≠ true := by
    contrapose H
    simp_all
    ext x;tauto
  obtain ⟨k,hk⟩ := this
  use fun _ => k
  simp_all
  exact E.const k


theorem complementMapIsNontrivial {E : C₀} : @complementMap E ≠ id := by
  intro hc
  have : @complementMap E (∅ₘ) = ∅ₘ := by
    rw [hc];simp
  unfold complementMap cpl emp_m at this
  simp at this
  obtain ⟨f,hf⟩ := this.1
  simp at hf


theorem complementMapIsAuto {E : C₀} : (@automorphism (@𝓓ₘ E)) complementMap := by
  unfold complementMap
  constructor
  constructor


  -- injective:
  apply Quotient.ind
  intro A
  apply Quotient.ind
  intro B
  intro h
  simp at h
  apply Quotient.sound
  unfold cpl at *
  obtain ⟨f₁,hf₁⟩ := h.1
  obtain ⟨f₂,hf₂⟩ := h.2
  constructor

  use f₁
  constructor
  · tauto
  · intro x
    have Q := hf₁.2 x
    simp at Q
    have : A x = ! ! A x := by simp
    rw [this]
    have : B (f₁ x) = ! ! B (f₁ x) := by simp
    rw [this]
    rw [Q]
  use f₂
  constructor
  · tauto
  · intro x
    have Q := hf₂.2 x
    simp at Q
    have : B x = ! ! B x := by simp
    rw [this]
    have : A (f₂ x) = ! ! A (f₂ x) := by simp
    rw [this]
    rw [Q]
  -- surjective:
  apply Quotient.ind
  intro A
  use ⟦ cpl A ⟧
  simp
  unfold cpl
  simp
  constructor
  use id
  constructor
  exact E.id
  tauto
  use id
  constructor
  exact E.id
  tauto
  -- preserves ≤ₘ
  apply Quotient.ind
  intro A
  apply Quotient.ind
  intro B
  constructor
  intro h
  simp at h
  unfold cpl
  obtain ⟨f,hf⟩ := h
  use f
  constructor
  tauto
  simp
  intro x
  congr
  tauto

  intro h
  simp at h
  unfold cpl at h
  obtain ⟨f,hf⟩ := h
  use f
  constructor
  tauto
  simp at hf
  intro x
  let Q := hf.2 x
  apply congrArg (fun b => !b) at Q
  simp at Q
  tauto

theorem notrigid {E : C₀} : ¬ rigid (@𝓓ₘ E) := by
  unfold rigid
  push_neg
  use complementMap
  constructor
  exact complementMapIsAuto
  exact complementMapIsNontrivial


/-- This result does not hold over C₁. -/
theorem botSwapIsAuto {E : C₂} : (@automorphism (@𝓓ₘ E.toC₀)) botSwap := by
  unfold automorphism botSwap
  constructor
  constructor
  exact botSwap_inj

  exact botSwap_surj
  apply Quotient.ind
  intro A
  apply Quotient.ind
  intro B
  split_ifs with g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇
  · rw [g₀,g₁];simp
  · rw [g₀,g₂]
    constructor
    exact fun h => False.elim <| emp_not_below h
    exact fun h => False.elim <| univ_not_below h
  · rw [g₀]
    constructor
    exact fun _ => emp_univ B g₁
    exact fun _ => univ_emp B g₂
  · rw [g₃,g₄]
    constructor
    exact fun h => False.elim <| univ_not_below h
    exact fun h => False.elim <| emp_not_below h
  · simp;rw [g₃, g₅];
  · rw [g₃]
    constructor
    exact fun _ => univ_emp B g₅
    exact fun _ => emp_univ B g₄
  · rw [g₆]
    constructor
    exact fun h => False.elim <|  g₀ <| emp_min ⟦A⟧ h
    exact fun h => False.elim <|  g₃ <| univ_min ⟦A⟧ h
  · rw [g₇]
    constructor
    exact fun h => False.elim <| g₃ <| univ_min ⟦A⟧ h
    exact fun h => False.elim <| g₀ <| emp_min ⟦A⟧ h
  · tauto




notation:50 " ⊥ₘ " => zero_m

example {E : C₂} : (@emp_m E.toC₀) < ( ⊥ₘ ) := by
  refine lt_of_le_not_le ?_ ?_
  · use fun _ => 1
    simp
    exact E.const 1
  · intro hc
    obtain ⟨f,hf⟩ := hc
    simp at hf

/-- The famous observation that ∅ and ℕ are the minimal elements of 𝓓ₘ. -/
lemma zero_one_m {E : C₂} {b : Bool} (A : ℕ → Bool) :
    A ≠ (fun _ => b) ↔ @m_reducible E.toC₀ (fun _ => !b) A := by
  constructor
  · intro hA
    unfold m_reducible
    simp
    contrapose hA
    simp_all
    ext n
    have ⟨_,ha⟩ := hA (fun _ ↦ n) (E.const _)
    exact ha.symm
  · intro hr hc
    obtain ⟨g,hg⟩ := hr
    subst hc
    simp_all


open Classical

/-- The eth r.e. set -/
noncomputable def φ {e : Nat.Partrec.Code} : ℕ → Bool := fun n => (Nat.Partrec.Code.eval e n).Dom


/-- Defining K as {e | φₑ(0)↓} -/
noncomputable def K : ℕ → Bool := fun e =>
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) 0).Dom

theorem K_re : RePred fun k ↦ (K k) = true := by
  unfold K
  have Q := ComputablePred.halting_problem_re 0
  simp_all
  show RePred fun l => (fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom)
    ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
  unfold RePred at *
  show Partrec fun l =>
    ( fun a : Nat.Partrec.Code ↦ Part.assert
      ((fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom) a) fun _ ↦ Part.some ())
    ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
  let f := ( fun a : Nat.Partrec.Code ↦ Part.assert
      ((fun c : Nat.Partrec.Code ↦ (c.eval 0).Dom) a) fun _ ↦ Part.some ())
  show Partrec fun l =>
    f
    ((fun k ↦ Denumerable.ofNat Nat.Partrec.Code k) l)
  apply Partrec.comp
  exact Q
  exact Computable.ofNat Nat.Partrec.Code

theorem Kbar_not_re : ¬RePred fun k ↦ (!K k) = true := by
  unfold K
  simp
  intro hc
  have h₀ : (fun c : Nat.Partrec.Code ↦ ¬(c.eval 0).Dom)
           = fun c ↦ ¬((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)).eval 0).Dom := by
    simp only [Denumerable.ofNat_encode]
  exact ComputablePred.halting_problem_not_re 0 <| h₀ ▸ Partrec.comp hc Computable.encode

theorem Kbar_not_computable : ¬ Computable fun k => ! K k := by
  intro hc
  have : ComputablePred fun k ↦ K k = false := by
    refine ComputablePred.computable_iff.mpr ?_
    use fun k => ! K k
    simp only [Bool.not_eq_true', and_true]
    exact hc
  exact Kbar_not_re <| ComputablePred.to_re (by simp_all)

theorem K_not_computable : ¬ Computable K :=
  fun hc => Kbar_not_computable
    <| Computable.cond hc (Computable.const false) (Computable.const true)

theorem compute_closed_m_downward (A B : ℕ → Bool) (h : Computable B)
    (h₀ : @m_reducible comput.toC₀ A B) : Computable A := by
  obtain ⟨f,hf⟩ := h₀
  have : A = B ∘ f := by ext k; simp_all
  rw [this]
  apply Computable.comp h
  exact hf.1

theorem re_closed_m_downward (A B : ℕ → Bool) (h : RePred (fun (k : ℕ) => (B k = true)))
    (h₀ : @m_reducible comput.toC₀ A B) : RePred (fun (k : ℕ) => (A k = true)) := by
  obtain ⟨f,hf⟩ := h₀
  have : A = B ∘ f := by ext k; simp_all
  rw [this]

  unfold RePred at *
  simp_all
  show Partrec fun a ↦ Part.assert (B (f a) = true) fun _ ↦ Part.some ()
  let g := (fun a ↦ Part.assert (B (a) = true) fun _ ↦ Part.some ())
  show Partrec <| fun b => g (f b)
  have hf' : Computable f := hf
  have : Partrec g := h
  exact Partrec.comp this hf'

theorem Kbar_not_below_K : ¬ @m_reducible comput.toC₀ (fun k ↦ (!K k) = true) K := by
  intro hc
  have : RePred (fun (k : ℕ) => (! K k = true)) := by
    apply re_closed_m_downward
    exact K_re
    simp_all
  have := Kbar_not_re
  simp_all
