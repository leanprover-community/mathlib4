/-
Copyright (c) 2024 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Characterizations for a ring of algebraic numbers having class number at most two
-/

open scoped BigOperators Classical NumberField
open Multiset (card)

class HalfFactorialMonoid (α : Type*) [CommMonoid α] : Prop where
  card_unique
    (f g : Multiset α)
    (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x)
    (h : f.prod = g.prod) :
      Multiset.card f = Multiset.card g

instance {α : Type*} [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
  HalfFactorialMonoid α where
    card_unique := fun _ _ hf hg h ↦
      Multiset.card_eq_card_of_rel <|
        UniqueFactorizationMonoid.factors_unique hf hg <|
          Associates.mk_eq_mk_iff_associated.mp <|
            congrArg Associates.mk h

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Fintype (ClassGroup R)]

theorem exists_prime (g : ClassGroup R) :
  ∃ (p : nonZeroDivisors (Ideal R)), ClassGroup.mk0 p = g ∧ p.val.IsPrime := sorry

lemma exists_pair_of_two_lt_card {T : Type*} {a : T} [Fintype T] (h : 2 < Fintype.card T) : ∃ b c : T, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have h : 1 < Fintype.card {x // x ≠ a} := by
    simp_all only [ne_eq, Fintype.card_subtype_compl, Fintype.card_ofSubsingleton]
    omega
  have ⟨⟨b, hba⟩, c, hbc⟩ := Fintype.exists_pair_of_one_lt_card h
  exact ⟨b, c, hba.symm, c.property.symm, by aesop⟩

-- two_lt_card_iff
example {T : Type} [Fintype T] (h : 2 < Fintype.card T) : ∃ a b c : T, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have nonempty := Fintype.card_pos_iff.mp <| Nat.zero_lt_of_lt h
  exact ⟨Classical.choice nonempty, exists_pair_of_two_lt_card h⟩

lemma one_lt_orderOf_iff {G : Type*} [Group G] {g : G} {h : IsOfFinOrder g} : 1 < orderOf g ↔ g ≠ 1 where
  mp := fun h ↦ orderOf_eq_one_iff.not.mp <| Nat.ne_of_lt' h
  mpr := fun hne ↦ Nat.lt_of_le_of_ne h.orderOf_pos <|
    fun a => orderOf_eq_one_iff.not.mpr hne a.symm

example : 1 < n → n ≠ 2 → 2 < n := fun a b => Nat.lt_of_le_of_ne a b.symm

theorem exists_prod_of_two_lt_card_classGroup (hcard : 2 < Fintype.card (ClassGroup R)) :
  ∃ α₁ α₂ β₁ β₂ β₃ : R,
    Irreducible α₁
    ∧ Irreducible α₂
    ∧ Irreducible β₁
    ∧ Irreducible β₂
    ∧ Irreducible β₃
    ∧ α₁ * α₂ = β₁ * β₂ * β₃ := by
      by_cases horder : ∀ {g : ClassGroup R}, 1 ≠ g → orderOf g = 2
      · have ⟨g₁, g₂, hg₁, hg₂, hg₁₂⟩ : ∃ g₁ g₂ : ClassGroup R, 1 ≠ g₁ ∧ 1 ≠ g₂ ∧ g₁ ≠ g₂ :=
          exists_pair_of_two_lt_card hcard
        set g₃ := g₁ * g₂
        have g₂₃ : g₂ ≠ g₃ := (mul_left_ne_self.mpr hg₁.symm).symm
        have g₁₃ : g₁ ≠ g₃ := self_ne_mul_right.mpr hg₂.symm
        have g₁ₒ : orderOf g₁ = 2 := horder hg₁
        have g₂ₒ : orderOf g₂ = 2 := horder hg₂
        have ⟨p₁, hgp₁, hp₁⟩ := exists_prime g₁
        have ⟨p₂, hgp₂, hp₂⟩ := exists_prime g₂
        have ⟨p₃, hgp₃, hp₃⟩ := exists_prime g₃
        have ⟨β₁, hβ₁ₛ, hβ₁⟩ : ∃ β₁ : R, p₁ * p₁ = Ideal.span {β₁} ∧ Irreducible β₁ := by
          refine ⟨?_, ?_, ?_⟩
          sorry
          sorry
          sorry
        have ⟨β₂, hβ₂ₛ, hβ₂⟩ : ∃ β₂ : R, p₂ * p₂ = Ideal.span {β₂} ∧ Irreducible β₂ := by sorry
        have ⟨β₃, hβ₃ₛ, hβ₃⟩ : ∃ β₃ : R, p₃ * p₃ = Ideal.span {β₃} ∧ Irreducible β₃ := by sorry
        have ⟨α, hαₛ, hα⟩ : ∃ α : R, p₁ * p₂ * p₃ = Ideal.span {α} ∧ Irreducible α := by sorry
        refine ⟨α, α, β₁, β₂, β₃, hα, hα, hβ₁, hβ₂, hβ₃, ?_⟩
        sorry
      · push_neg at horder
        rcases horder with ⟨g, hne, hg⟩
        have horder' := (Iff.mpr <| @one_lt_orderOf_iff _ _ _ (isOfFinOrder_of_finite g)) hne.symm
        have horder : 2 < orderOf g := Nat.lt_of_le_of_ne horder' hg.symm
        clear horder'
        set n := orderOf g
        have ⟨p₁, hgp₁, hp₁⟩ := exists_prime g
        have ⟨p₂, hgp₂, hp₂⟩ := exists_prime <| g ^ 2
        have ⟨p₃, hgp₃, hp₃⟩ := exists_prime <| g ^ (n - 2)
        have ⟨p₄, hgp₄, hp₄⟩ := exists_prime <| g ^ (n - 1)
        have ⟨α, hα, hαᵢ⟩ : ∃ r : R, Ideal.span {r} = p₁ * p₄ ∧ Irreducible r := by
          have hprincipal : (p₁ * p₄ : Ideal R).IsPrincipal := by sorry
          obtain ⟨α, h''⟩ := hprincipal.principal
          refine ⟨α, by simp only [h'', Ideal.submodule_span_eq], by sorry⟩

        have ⟨β, hβ, hβᵢ⟩ : ∃ r : R, Ideal.span {r} = p₁ ^ 2 * p₃ ∧ Irreducible r := by sorry
        have ⟨γ, hγ, hγᵢ⟩ : ∃ r : R, Ideal.span {r} = p₂ * p₃ ∧ Irreducible r := by sorry
        have ⟨δ, hδ, hδᵢ⟩ : ∃ r : R, Ideal.span {r} = p₂ * p₄ ^ 2 ∧ Irreducible r := by sorry
        use β, δ, α, α, γ, hβᵢ, hδᵢ, hαᵢ, hαᵢ, hγᵢ
        have : (p₁ ^ 2 * p₃) * (p₄ ^ 2 * p₂) = (p₁ * p₄) * (p₁ * p₄) * (p₂ * p₃) := by sorry
        sorry


/-- The class number of a half-factorial domain is `2`. -/
theorem card_classGroup_le_two [HalfFactorialMonoid R] : Fintype.card (ClassGroup R) ≤ 2 := by
  by_contra! h
  have ⟨α₁, α₂, β₁, β₂, β₃, _, _, _, _, _, hab⟩ := exists_prod_of_two_lt_card_classGroup h
  let a : Multiset R := {α₁, α₂}
  let b : Multiset R := {β₁, β₂, β₃}
  have ha : ∀ i ∈ a, Irreducible i := by simp_all [a]
  have hb : ∀ i ∈ b, Irreducible i := by simp_all [b]
  have := HalfFactorialMonoid.card_unique _ _ ha hb <| by simp_all [a, b, hab, mul_assoc]
  exact Nat.ne_of_beq_eq_false (by rfl) this

theorem nonzero_ne_zero (a : R) (ha : a ≠ 0) : Ideal.span ({a} : Set R) ≠ 0 := by
  simp_all only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, not_false_eq_true]

/-- The class number is `≤ 2` iff the ring of integers is a half-factorial domain. -/
theorem card_classGroup_le_two_iff : Fintype.card (ClassGroup R) ≤ 2 ↔ HalfFactorialMonoid R := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ card_classGroup_le_two⟩
  -- it suffices to prove this direction for card = 2, because otherwise R is a UFD
  by_cases hcard : Fintype.card (ClassGroup R) = 2
  · refine ⟨fun a b ha hb heq ↦ ?_⟩
    by_cases nonzero : a.prod = 0
    · exfalso
      exact not_irreducible_zero <| ha 0 <| (a.prod_eq_zero_iff).mp nonzero
    · let X := Ideal.span ({a.prod} : Set R)
      have ⟨F, hprime, hprod⟩ : ∃ (F : Multiset (Ideal R)), (∀ I ∈ F, I.IsPrime) ∧ F.prod = X := by
        have ⟨F', hprime', _, hu⟩ := UniqueFactorizationMonoid.exists_prime_factors X <| nonzero_ne_zero a.prod nonzero
        exact ⟨F', fun I a ↦ Ideal.isPrime_of_prime <| hprime' I a, by simp [← hu, units_eq_one]⟩
      set Q : Multiset (Ideal R) := F.filter Submodule.IsPrincipal
      set P := F - Q
      have : Q.prod * P.prod = X := by
        simp only [P, Q, Multiset.sub_filter_eq_filter_not, Multiset.prod_filter_mul_prod_filter_not, hprod]
      have hcard : ∀ (f : Multiset R), (∀ i ∈ f, Irreducible i) → f.prod = a.prod → card f = card Q + (card P / 2) := by
        intro f hf hfprod
        sorry
      exact hcard a ha rfl |>.trans (hcard b hb heq.symm).symm
  · have : IsPrincipalIdealRing R := card_classGroup_eq_one_iff.mp <| by
      have : 0 < Fintype.card (ClassGroup R) := Fintype.card_pos
      interval_cases (Fintype.card (ClassGroup R)) <;> aesop
    infer_instance
end

variable {K : Type*} [Field K] [NumberField K]

namespace NumberField

/-- The class number of a number field is `2` iff the ring of integers is a half factorial
    domain. -/
theorem classNumber_eq_two_iff : classNumber K ≤ 2 ↔ HalfFactorialMonoid (𝓞 K) :=
  card_classGroup_le_two_iff

variable {α β : 𝓞 K}

end NumberField
