/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.PageInfinity
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Order.Preorder.Finite

/-!
# Convergence of spectral sequences

-/

@[expose] public section

universe w₁ w₂ w₃ v u

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]
  (ι : Type w₁) {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

variable {σ : Type w₂} (α : σ → Type w₃) [∀ n, LinearOrder (α n)]

@[nolint checkUnivs]
structure ConvergenceStripes where
  pred (n : σ) (i : α n) : WithBot (α n)
  pred_lt n (i : α n) : pred n i < WithBot.some i := by aesop
  stripe : ι → σ
  position (n : σ) (i : α n) : ι
  stripe_position (n : σ) (i : α n) : stripe (position n i) = n := by aesop
  discrete (n : σ) (i j : α n) (h₁ : pred n i < WithBot.some j) : i ≤ j
  finite_segment (n : σ) (i j : α n) : Set.Finite (fun (k : α n) => i ≤ k ∧ k ≤ j)

variable {α}

@[simps]
def cohomologicalStripes : ConvergenceStripes (ℤ × ℤ) (fun (_ : ℤ) => ℤ) where
  stripe pq := pq.1 + pq.2
  position n i := ⟨n + 1 - i, i - 1⟩
  pred n i := WithBot.some (i - 1)
  pred_lt n i := by aesop
  finite_segment _ i j := by
    rw [Set.finite_def]
    by_cases hij : i ≤ j
    · obtain ⟨d, rfl⟩ := Int.le.dest hij
      refine ⟨Fintype.ofSurjective (fun (k : Fin (d + 1)) =>
        ⟨i + k, ⟨by lia, by have := k.is_lt; lia⟩⟩) ?_⟩
      rintro ⟨x, h₁, h₂⟩
      obtain ⟨k, rfl⟩ := Int.le.dest h₁
      exact ⟨⟨k, by lia⟩, rfl⟩
    · refine ⟨@Fintype.ofIsEmpty _ ⟨?_⟩⟩
      rintro ⟨x, h₁, h₂⟩
      lia
  discrete n (i j : ℤ) h := by
    simp at h
    lia

@[simps]
def cohomomologicalStripesFin (l : ℕ) : ConvergenceStripes (ℤ × Fin l) (fun (_ : ℤ) => Fin l) where
  stripe pq := pq.1 + pq.2.1
  pred _ j := match j with
    | ⟨0, _⟩   => ⊥
    | ⟨j+1, _⟩ => WithBot.some ⟨j, by lia⟩
  pred_lt n := by rintro ⟨_|i, _⟩ <;> simp
  position n i := ⟨n - i.1, i⟩
  discrete := by
    rintro n ⟨_|i, hi⟩ ⟨j, hj⟩ h
    · simp
    · simp only [WithBot.coe_lt_coe, Fin.mk_lt_mk, Fin.mk_le_mk] at h ⊢
      lia
  finite_segment _ _ _ := by
    rw [Set.finite_def]
    exact ⟨Fintype.ofInjective Subtype.val (by apply Subtype.ext)⟩

variable {ι}

namespace ConvergenceStripes

variable (s : ConvergenceStripes ι α)

attribute [simp] stripe_position

lemma stripe_eq (n : σ) (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    s.stripe pq = n := by
  rw [← hpq, s.stripe_position]

@[nolint unusedArguments]
def segment (_ : ConvergenceStripes ι α) (n : σ) (i j : α n) : Set (α n) :=
  fun k => i ≤ k ∧ k ≤ j

noncomputable instance (n : σ) (i j : α n) : Fintype (s.segment n i j) := by
  have h := s.finite_segment n i j
  rw [Set.finite_def] at h
  exact h.some

/-- Variant of `segment` but as `Set (WithBot (α n))`. -/
@[nolint unusedArguments]
def segment' (_ : ConvergenceStripes ι α) (n : σ) (i : α n)
    (j : WithBot (α n)) : Set (WithBot (α n)) :=
  fun k => WithBot.some i ≤ k ∧ k ≤ j

instance (n : σ) (i : α n) : Subsingleton (s.segment' n i ⊥) where
  allEq := by
    rintro ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    simp only [le_bot_iff] at ha' hb'
    subst ha' hb'
    rfl

noncomputable instance (n : σ) (i : α n) (j : WithBot (α n)) :
    Fintype (s.segment' n i j) := by
  obtain _ | j := j
  · let φ : s.segment' n i ⊥ → Fin 1 := fun _ => 0
    apply Fintype.ofInjective φ
    intro x₁ x₂ _
    apply Subsingleton.elim
  · let φ : s.segment n i j → s.segment' n i (WithBot.some j) := fun x =>
      ⟨WithBot.some x.1, by simpa using x.2.1, by simpa using x.2.2⟩
    apply Fintype.ofSurjective φ
    rintro ⟨x, hx, hx'⟩
    obtain _ | x := x
    · change WithBot.some i ≤ ⊥ at hx
      simp at hx
    · exact ⟨⟨x, WithBot.coe_le_coe.1 hx, WithBot.coe_le_coe.1 hx'⟩, rfl⟩

lemma pred_le (n : σ) (i : α n) : s.pred n i ≤ WithBot.some i :=
  (s.pred_lt n i).le

lemma pred_monotone (n : σ) (i j : α n) (hij : i ≤ j) :
    s.pred n i ≤ s.pred n j := by
  obtain _ | rfl := hij.lt_or_eq
  · by_contra!
    by_cases hi : ∃ (k : α n), k = s.pred n i
    · obtain ⟨k, hk⟩ := hi
      have hj := s.discrete n j k (by simpa only [← hk] using this)
      have hk' := s.pred_lt n i
      rw [← hk] at hk'
      replace hij : WithBot.some i ≤ WithBot.some j := WithBot.coe_le_coe.2 hij
      replace hj : WithBot.some j ≤ WithBot.some k := WithBot.coe_le_coe.2 hj
      have := lt_of_le_of_lt (hij.trans hj) hk'
      simp at this
    · rw [← WithBot.ne_bot_iff_exists, ne_eq, not_not] at hi
      rw [hi] at this
      simp at this
  · rfl

/-- `pred` on `WithBot (α n)`. -/
def pred' (n : σ) : WithBot (α n) → WithBot (α n)
  | ⊥ => ⊥
  | WithBot.some x => s.pred n x

@[simp]
lemma pred'_bot (n : σ) : s.pred' n ⊥ = ⊥ := rfl

@[simp]
lemma pred'_some (n : σ) (i : α n) :
    s.pred' n (WithBot.some i) = s.pred n i := rfl

lemma pred'_le (n : σ) (i : WithBot (α n)) :
    s.pred' n i ≤ i := by
  obtain _ | ⟨i⟩ := i
  · erw [pred'_bot]
    simp
  · erw [pred'_some]
    exact s.pred_le n i

lemma pred_injective (n : σ) (i j : α n) (hij : s.pred n i = s.pred n j) :
    i = j := by
  revert i j hij
  suffices ∀ (i j : α n) (_ : s.pred n i = s.pred n j) (_ : i ≤ j), i = j by
    intro i j hij
    obtain h | h := le_total i j
    · exact this i j hij h
    · exact (this j i hij.symm h).symm
  intro i j hij h
  exact le_antisymm h (s.discrete n j i (by simpa only [← hij] using s.pred_lt n i))

lemma pred'_monotone (n : σ) (i j : WithBot (α n)) (hij : i ≤ j) :
    s.pred' n i ≤ s.pred' n j := by
  induction j using WithBot.recBotCoe with
  | bot =>
    obtain rfl := le_bot_iff.1 hij
    rfl
  | coe j =>
    induction i using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe i => exact s.pred_monotone _ _ _ (by simpa using hij)

lemma le_pred'_of_lt (n : σ) (i j : WithBot (α n)) (hi : i < j) :
    i ≤ s.pred' n j := by
  induction i using WithBot.recBotCoe with
  | bot => simp
  | coe i =>
    induction j using WithBot.recBotCoe with
    | bot => simp at hi
    | coe j =>
      by_contra!
      have := lt_of_le_of_lt (s.discrete n j i this) (WithBot.coe_lt_coe.1 hi)
      simp at this

/-- `i < j ↔ i ≤ s.pred' n j`. -/
lemma lt_iff_le_pred' (n : σ) (i : α n) (j : WithBot (α n)) :
    i < j ↔ i ≤ s.pred' n j := by
  constructor
  · apply s.le_pred'_of_lt
  · intro h
    obtain _ | j := j
    · erw [pred'_bot] at h
      simp at h
    · exact lt_of_le_of_lt h (s.pred_lt n j)

/-- Substraction by `k : ℕ` on `WithBot (α n)`. -/
def sub' (n : σ) : ℕ → WithBot (α n) → WithBot (α n)
  | 0 => id
  | k + 1 => s.pred' n ∘ sub' n k

def sub (n : σ) (i : WithBot (α n)) (k : ℕ) : WithBot (α n) := s.sub' n k i

@[simp]
lemma sub_zero (n : σ) (i : WithBot (α n)) :
    s.sub n i 0 = i := rfl

lemma sub_one (n : σ) (i : WithBot (α n)) :
    s.sub n i 1 = s.pred' n i := rfl

lemma sub_succ (n : σ) (i : WithBot (α n)) (k : ℕ) :
    s.sub n i (k + 1) = s.pred' n (s.sub n i k) := rfl

lemma sub_sub (n : σ) (i : WithBot (α n)) (k₁ k₂ k : ℕ) (h : k₁ + k₂ = k) :
    s.sub n (s.sub n i k₁) k₂ = s.sub n i k := by
  revert k₁ k h
  induction k₂ with
  | zero =>
    intro k₁ k h
    obtain rfl : k₁ = k := by simpa using h
    simp
  | succ k₂ hk₂ =>
    intro k₁ k h
    obtain rfl : k₁ + k₂ + 1 = k := by simpa only [Nat.succ_eq_add_one, add_assoc] using h
    simp only [sub_succ, hk₂ k₁ _ rfl]

@[simp]
lemma sub_bot (n : σ) (k : ℕ) :
    s.sub n ⊥ k = ⊥ := by
  induction k with
  | zero => simp
  | succ k hk => simp [hk, sub_succ]

lemma sub_le_self (n : σ) (i : WithBot (α n)) (k : ℕ) :
    s.sub n i k ≤ i := by
  revert i
  induction k with
  | zero => simp
  | succ k hk =>
    intro i
    rw [sub_succ]
    exact (s.pred'_le n _).trans (hk _)

lemma sub_antitone (n : σ) (i : WithBot (α n)) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    s.sub n i k₂ ≤ s.sub n i k₁ := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  rw [← s.sub_sub n i k₁ k _ rfl]
  apply sub_le_self

lemma sub_succ_lt (n : σ) (i : α n) (k : ℕ) :
    s.sub n (WithBot.some i) (k + 1) < WithBot.some i :=
  lt_of_le_of_lt (s.sub_antitone n (WithBot.some i) 1 (k + 1) (by lia)) (by
    rw [sub_one, pred'_some]
    apply pred_lt)

lemma sub_eq_self_iff (n : σ) (i : WithBot (α n)) (k : ℕ) :
    s.sub n i k = i ↔ i = ⊥ ∨ k = 0 := by
  constructor
  · intro h
    obtain _ | i := i
    · exact Or.inl rfl
    · refine Or.inr ?_
      obtain _ | k := k
      · rfl
      · change s.sub n i (k + 1) = (WithBot.some i) at h
        simpa only [h, lt_self_iff_false] using s.sub_succ_lt n i k
  · rintro (rfl | rfl) <;> simp

lemma sub_injective (n : σ) (i : WithBot (α n)) (k₁ k₂ : ℕ)
    (h : s.sub n i k₁ = s.sub n i k₂) :
    s.sub n i k₁ = ⊥ ∨ k₁ = k₂ := by
  revert i k₁ k₂ h
  suffices ∀ (i : WithBot (α n)) (k₁ k₂ : ℕ) (_ : k₁ ≤ k₂) (_ : s.sub n i k₁ = s.sub n i k₂),
      s.sub n i k₁ = ⊥ ∨ k₁ = k₂ by
    intro i k₁ k₂ hk
    obtain h | h := le_total k₁ k₂
    · exact this i k₁ k₂ h hk
    · obtain h' | h' := this i k₂ k₁ h hk.symm
      · exact Or.inl (hk.trans h')
      · exact Or.inr h'.symm
  intro i k₁ k₂ hk h
  obtain ⟨d, rfl⟩ := Nat.le.dest hk
  replace h := h.symm
  rw [← s.sub_sub n i k₁ d _ rfl, sub_eq_self_iff] at h
  obtain h | rfl := h
  · exact Or.inl h
  · exact Or.inr (by simp)

lemma exists_sub_eq (n : σ) (i j : α n) (hij : i ≤ j) :
    ∃ (k : ℕ), s.sub n j k = i := by
  let S : Set ℕ := fun k => (WithBot.some i) ≤ s.sub n (WithBot.some j) k
  have hS : S.Finite := by
    let φ : S → s.segment' n i j := fun x => ⟨s.sub n j x.1, x.2, s.sub_le_self _ _ _⟩
    refine Finite.of_injective φ ?_
    intro k₁ k₂ h
    simp only [φ, Subtype.mk.injEq] at h
    obtain h' | h' := s.sub_injective n _ _ _ h
    · exfalso
      have h₁ : WithBot.some i ≤ s.sub n j k₁ := k₁.2
      simp only [h', le_bot_iff, WithBot.coe_ne_bot] at h₁
    · ext
      exact h'
  have hS' : S.Nonempty := ⟨0, by
    change WithBot.some i ≤ s.sub n j 0
    simpa only [s.sub_zero, WithBot.coe_le_coe] using hij⟩
  obtain ⟨l, hl⟩ := Set.Finite.exists_maximalFor id S hS hS'
  refine ⟨l, le_antisymm ?_ hl.prop⟩
  by_contra!
  rw [lt_iff_le_pred', ← sub_one, s.sub_sub n j l 1 _ rfl] at this
  have := hl.le_of_le this (by simp)
  simp at this

lemma exists_sub_le (n : σ) (i : WithBot (α n)) (j : α n) :
    ∃ (k : ℕ), s.sub n i k ≤ WithBot.some j := by
  induction i using WithBot.recBotCoe with
  | bot => exact ⟨0, by simp⟩
  | coe i =>
    obtain hij | hij := le_total i j
    · use 0
      simpa only [sub_zero] using WithBot.coe_le_coe.2 hij
    · obtain ⟨k, hk⟩ := s.exists_sub_eq n j i hij
      exact ⟨k, by rw [← hk]⟩

end ConvergenceStripes

variable (E : SpectralSequence C c r₀) (s : ConvergenceStripes ι α)

structure StronglyConvergesToInDegree (n : σ) (X : C) where
  hasPageInfinityAt : ∀ (pq : ι) (_ : s.stripe pq = n), E.HasPageInfinityAt pq
  filtration' : (WithBot (α n)) ⥤ MonoOver X
  exists_isZero' :
    ∃ (j : α n), IsZero ((filtration' ⋙ MonoOver.forget _ ⋙ Over.forget _).obj (s.pred n j))
  exists_isIso' : ∃ (j : α n), IsIso ((filtration' ⋙ MonoOver.forget _).obj j).hom
  π' (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    ((filtration' ⋙ MonoOver.forget _ ⋙ Over.forget _).obj (WithBot.some i)) ⟶ E.pageInfinity pq
  epi_π' (i : α n) (pq : ι) (hpq : s.position n i = pq) : Epi (π' i pq hpq) := by infer_instance
  comp_π' (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i)
    (pq : ι) (hpq : s.position n j = pq) :
    (filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).map
      (homOfLE (show i ≤ WithBot.some j by
        subst hij
        exact s.pred_le n j)) ≫ π' j pq hpq = 0
  exact_π' (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) (pq : ι)
    (hpq : s.position n j = pq) :
      (ShortComplex.mk _ _ (comp_π' i j hij pq hpq)).Exact

def StronglyConvergesTo (X : σ → C) := ∀ (n : σ), E.StronglyConvergesToInDegree s n (X n)

namespace StronglyConvergesToInDegree

variable {E s}

section

variable {n : σ} {X : C} (h : E.StronglyConvergesToInDegree s n X)

def filtration : WithBot (α n) ⥤ C := h.filtration' ⋙ MonoOver.forget X ⋙ Over.forget X

def filtrationι (i : WithBot (α n)) : h.filtration.obj i ⟶ X :=
  ((h.filtration' ⋙ MonoOver.forget X).obj i).hom

set_option backward.isDefEq.respectTransparency false in
instance (i : WithBot (α n)) : Mono (h.filtrationι i) := by
  dsimp [filtrationι]
  infer_instance

@[reassoc (attr := simp)]
lemma filtration_map_ι (i j : WithBot (α n)) (f : i ⟶ j) :
    h.filtration.map f ≫ h.filtrationι j = h.filtrationι i :=
  Over.w ((h.filtration' ⋙ MonoOver.forget X).map f)

instance {i j : WithBot (α n)} (f : i ⟶ j) :
    Mono (h.filtration.map f) :=
  mono_of_mono_fac (h.filtration_map_ι i j f)

lemma exists_isZero : ∃ (j : α n), IsZero (h.filtration.obj (s.pred n j)) :=
  h.exists_isZero'

lemma exists_isIso : ∃ (j : α n), IsIso (h.filtrationι j) :=
  h.exists_isIso'

def π (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    h.filtration.obj i ⟶ E.pageInfinity pq :=
  h.π' i pq hpq

instance (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    Epi (h.π i pq hpq) :=
  h.epi_π' i pq hpq

lemma comp_π (i : WithBot (α n)) (j : α n) (hij : i < j) (pq : ι) (hpq : s.position n j = pq) :
    h.filtration.map (homOfLE hij.le) ≫ h.π j pq hpq = 0 := by
  erw [show homOfLE hij.le = homOfLE (s.le_pred'_of_lt n _ _ hij) ≫
    homOfLE (s.pred_le n j) by rfl, h.filtration.map_comp, assoc,
    h.comp_π' _ j rfl pq hpq, comp_zero]

def ofIso {Y : C} (e : X ≅ Y) : E.StronglyConvergesToInDegree s n Y where
  hasPageInfinityAt := h.hasPageInfinityAt
  filtration' := h.filtration' ⋙ MonoOver.map e.hom
  exists_isZero' := h.exists_isZero'
  exists_isIso' := by
    obtain ⟨j, hj⟩ := h.exists_isIso'
    dsimp at hj
    exact ⟨j, by dsimp; infer_instance⟩
  π' := h.π'
  epi_π' := h.epi_π'
  comp_π' := h.comp_π'
  exact_π' := h.exact_π'

section

variable (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i)
  (pq : ι) (hpq : s.position n j = pq)

/-- Vanishing of `h.filtration.map _ ≫ h.π j pq hpq = 0`. -/
lemma comp_π'' :
    h.filtration.map (homOfLE (show i ≤ some j by subst hij; exact s.pred_le n j)) ≫
      h.π j pq hpq = 0 :=
  h.comp_π' i j hij pq hpq

@[simps]
noncomputable def shortComplex :
    ShortComplex C :=
  ShortComplex.mk _ _ (h.comp_π'' i j hij pq hpq)

instance : Mono (h.shortComplex i j hij pq hpq).f := by dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : Epi (h.shortComplex i j hij pq hpq).g := by dsimp; infer_instance

lemma shortExact :
    (h.shortComplex i j hij pq hpq).ShortExact where
  exact := h.exact_π' i j hij pq hpq

end

lemma isIso_filtration_map_from_pred_iff (i : WithBot (α n)) (j : α n)
    (φ : i ⟶ some j) (hij : s.pred n j = i) (pq : ι) (hpq : s.position n j = pq) :
    IsIso (h.filtration.map φ) ↔ IsZero (E.pageInfinity pq) :=
  (h.shortExact i j hij pq hpq).isIso_f_iff

lemma isIso_filtration_map_from_pred'_iff
    (i j : WithBot (α n)) (φ : i ⟶ j) (hij : s.pred' n j = i) :
    IsIso (h.filtration.map φ) ↔
      ∀ (k : α n) (_ : j = WithBot.some k) (pq : ι) (_ : s.position n k = pq),
        IsZero (E.pageInfinity pq) := by
  obtain _ | j := j
  · constructor
    · intro _ k (hk : ⊥ = WithBot.some k)
      simp at hk
    · intro
      obtain rfl : i = none := by
        have : i ≤ ⊥ := leOfHom φ
        simpa using this
      obtain rfl : φ = 𝟙 _ := rfl
      infer_instance
  · constructor
    · intro hφ k hk pq hpq
      obtain rfl : j = k := by
        change some j = some k at hk
        simpa only [Option.some.injEq] using hk
      exact (h.isIso_filtration_map_from_pred_iff i j φ hij pq hpq).1 inferInstance
    · intro H
      exact (h.isIso_filtration_map_from_pred_iff i j φ hij _ rfl).2 (H j rfl _ rfl)

lemma isIso_filtration_map_comp_iff (i j k : WithBot (α n)) (f : i ⟶ j) (g : j ⟶ k) :
    IsIso (h.filtration.map (f ≫ g)) ↔
      IsIso (h.filtration.map f) ∧ IsIso (h.filtration.map g) := by
  rw [Functor.map_comp]
  constructor
  · intro
    have : Epi (h.filtration.map g) := epi_of_epi (h.filtration.map f) _
    have : IsIso (h.filtration.map g) := isIso_of_mono_of_epi _
    have : IsIso (h.filtration.map f) := IsIso.of_isIso_comp_right _ (h.filtration.map g)
    constructor <;> infer_instance
  · rintro ⟨_, _⟩
    infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma isZero_of_isIso_filtration_map (i j : WithBot (α n)) (φ : i ⟶ j)
    (hφ : IsIso (h.filtration.map φ)) (k : α n)
    (h₁ : i ≤ s.pred n k) (h₂ : WithBot.some k ≤ j)
    (pq : ι) (hpq : s.position n k = pq) :
    IsZero (E.pageInfinity pq) := by
  obtain rfl : φ = homOfLE h₁ ≫ homOfLE (s.pred_le n k) ≫ homOfLE h₂ := rfl
  rw [isIso_filtration_map_comp_iff, isIso_filtration_map_comp_iff,
    h.isIso_filtration_map_from_pred_iff _ k _ rfl pq hpq] at hφ
  exact hφ.2.1

lemma isIso_filtration_map'_iff (i j : WithBot (α n)) (φ : j ⟶ i) (k : ℕ) (hk : s.sub n i k = j) :
    IsIso (h.filtration.map φ) ↔
      ∀ (d : ℕ) (_ : d < k) (j : α n) (_ : s.sub n i d = WithBot.some j)
          (pq : ι) (_ : s.position n j = pq),
        IsZero (E.pageInfinity pq) := by
  subst hk
  induction k with
  | zero =>
    simp only [ConvergenceStripes.sub_zero, not_lt_zero', forall_eq',
      IsEmpty.forall_iff, forall_const, iff_true]
    change IsIso (h.filtration.map (𝟙 _))
    infer_instance
  | succ k hk =>
    erw [h.isIso_filtration_map_comp_iff (s.sub n i (k + 1)) (s.sub n i k) i
      (homOfLE (s.sub_antitone _ _ _  _ (by lia))) (homOfLE (s.sub_le_self n i k)), hk,
      h.isIso_filtration_map_from_pred'_iff _ _ _ (by rw [s.sub_succ])]
    constructor
    · rintro ⟨h₁, h₂⟩ d hd j hj pq hpq
      have hd' : d ≤ k := by lia
      obtain hd'' | rfl := hd'.lt_or_eq
      · exact h₂ d hd'' j hj pq hpq
      · exact h₁ j hj pq hpq
    · intro H
      constructor
      · intro l hl pq hpq
        exact H k (by lia) l hl pq hpq
      · intro d hd j hj pq hpq
        exact H d (by lia) j hj pq hpq

lemma isZero_filtration_obj_none : IsZero (h.filtration.obj none) := by
  obtain ⟨j, hj⟩ := h.exists_isZero
  rw [IsZero.iff_id_eq_zero]
  let φ : ⊥ ⟶ s.pred n j := homOfLE bot_le
  rw [← cancel_mono (h.filtration.map φ)]
  apply hj.eq_of_tgt

lemma isZero_filtration_obj_iff (i : WithBot (α n)) :
    IsZero (h.filtration.obj i) ↔
      ∀ (j : α n) (_ : WithBot.some j ≤ i) (pq : ι) (_ : s.position n j = pq),
        IsZero (E.pageInfinity pq) := by
  constructor
  · intro hi j hj pq hpq
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (h.π j pq hpq)]
    apply IsZero.eq_of_src
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (h.filtration.map (homOfLE hj))]
    apply hi.eq_of_tgt
  · intro hi
    obtain ⟨j, hj⟩ := h.exists_isZero
    obtain ⟨k, hk⟩ := s.exists_sub_le n i j
    let φ : s.sub n i (k + 1) ⟶ i := homOfLE (s.sub_le_self n i (k + 1))
    have : IsIso (h.filtration.map φ) := by
      rw [h.isIso_filtration_map'_iff i _ _ (k + 1) rfl]
      intro d _ j hj pq hpq
      exact hi j (by rw [← hj]; apply s.sub_le_self) pq hpq
    refine IsZero.of_iso ?_ (asIso (h.filtration.map φ)).symm
    let α : s.sub n i (k + 1) ⟶ s.pred n j := homOfLE (by
      rw [s.sub_succ, ← s.pred'_some]
      exact s.pred'_monotone _ _ _ hk)
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (h.filtration.map α)]
    apply hj.eq_of_tgt

lemma isZero_filtration_obj_of_LE (i j : WithBot (α n)) (hij : i ≤ j)
    (hj : IsZero (h.filtration.obj j)) : IsZero (h.filtration.obj i) := by
  rw [isZero_filtration_obj_iff] at hj ⊢
  intro k hk pq hpq
  exact hj k (hk.trans hij) pq hpq

lemma isIso_filtration_map_iff (i j : WithBot (α n)) (φ : i ⟶ j) :
    IsIso (h.filtration.map φ) ↔
      ∀ (k : α n) (_ : i ≤ s.pred n k) (_ : WithBot.some k ≤ j)
        (pq : ι) (_ : s.position n k = pq), IsZero (E.pageInfinity pq) := by
  constructor
  · apply isZero_of_isIso_filtration_map
  · intro H
    obtain _ | j := j
    · obtain rfl : i = ⊥ := by
        have : i ≤ ⊥ := leOfHom φ
        simpa using this
      obtain rfl : φ = 𝟙 _ := rfl
      infer_instance
    · revert i φ H
      suffices ∀ (i : α n) (φ : WithBot.some i ⟶ WithBot.some j), (∀ (k : α n)
          (_ : WithBot.some i ≤ s.pred n k) (_ : k ≤ j) (pq : ι)
          (_ : s.position n k = pq), IsZero (E.pageInfinity pq)) → IsIso (h.filtration.map φ) by
        intro i φ H
        obtain _ | i := i
        · refine ⟨0, h.isZero_filtration_obj_none.eq_of_src _ _, IsZero.eq_of_src ?_ _ _⟩
          rw [isZero_filtration_obj_iff]
          intro k hk pq hpq
          exact H k bot_le hk pq hpq
        · apply this
          intro k h₁ h₂ pq hpq
          exact H k h₁ (WithBot.coe_le_coe.2 h₂) pq hpq
      intro i φ H
      have hij : i ≤ j := WithBot.coe_le_coe.1 (leOfHom φ)
      obtain ⟨k, hk⟩ := s.exists_sub_eq n i j hij
      rw [h.isIso_filtration_map'_iff j i φ k hk]
      intro d hd l hl pq hpq
      refine H l ?_ ?_ pq hpq
      · rw [← s.pred'_some, ← hl, ← s.sub_one, s.sub_sub n j d 1 _ rfl, ← hk]
        apply s.sub_antitone
        lia
      · rw [← WithBot.coe_le_coe]
        change (WithBot.some l) ≤ (WithBot.some j)
        rw [← hl]
        apply s.sub_le_self

lemma isIso_filtrationι_of_GE (i j : WithBot (α n)) (hij : i ≤ j)
    (hi : IsIso (h.filtrationι i)) :
    IsIso (h.filtrationι j) := by
  have := epi_of_epi_fac (h.filtration_map_ι _ _ (homOfLE hij))
  apply isIso_of_mono_of_epi

lemma isIso_filtation_map_of_isIso_filtrationι (i j : WithBot (α n)) (φ : i ⟶ j)
    (hi : IsIso (h.filtrationι i)) :
    IsIso (h.filtration.map φ) := by
  have := h.isIso_filtrationι_of_GE i j (leOfHom φ) hi
  exact IsIso.of_isIso_fac_right (h.filtration_map_ι _ _ φ)

lemma isIso_filtrationι_iff (i : WithBot (α n)) :
    IsIso (h.filtrationι i) ↔ ∀ (j : α n) (_ : i < j) (pq : ι) (_ : s.position n j = pq),
      IsZero (E.pageInfinity pq) := by
  constructor
  · intro hi j hij pq hpq
    rw [← h.isIso_filtration_map_from_pred_iff _ j (homOfLE (s.pred_le n j)) rfl pq hpq]
    apply h.isIso_filtation_map_of_isIso_filtrationι
    exact h.isIso_filtrationι_of_GE _ _ (s.le_pred'_of_lt n _ _ hij) hi
  · obtain ⟨j, hj⟩ := h.exists_isIso
    obtain hij | hij := le_total i (WithBot.some j)
    · intro hi
      rw [← h.filtration_map_ι _ _ (homOfLE hij)]
      have := (h.isIso_filtration_map_iff i j (homOfLE hij)).2 (by
        intro k hk _ pq hpq
        exact hi k (lt_of_le_of_lt hk (s.pred_lt n k)) pq hpq)
      infer_instance
    · intro
      exact h.isIso_filtrationι_of_GE _ _ hij hj

lemma isIso_filtrationι_of_isZero (i : WithBot (α n))
    (hi : ∀ (j : α n) (_ : i < j) (pq : ι) (_ : s.position n j = pq),
      IsZero (E.pageInfinity pq)) :
    IsIso (h.filtrationι i) :=
  (h.isIso_filtrationι_iff i).2 hi

/-- `IsIso (h.π i pq hpq) ↔ IsZero (h.filtration.obj (s.pred n i))`. -/
lemma isIso_π_iff' (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    IsIso (h.π i pq hpq) ↔ IsZero (h.filtration.obj (s.pred n i)) :=
  (h.shortExact _ i rfl pq hpq).isIso_g_iff

lemma isIso_π_iff (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    IsIso (h.π i pq hpq) ↔
      ∀ (j : α n) (_ : j < i) (pq : ι) (_ : s.position n j = pq),
        IsZero (E.pageInfinity pq) := by
  rw [isIso_π_iff', isZero_filtration_obj_iff]
  constructor
  · intro H j hj pq hpq
    exact H j (s.le_pred'_of_lt n j i (by simpa using hj)) pq hpq
  · intro H j hj pq hpq
    exact H j (by simpa using (s.lt_iff_le_pred' n j i).2 hj) pq hpq

lemma isIso_π_of_isZero (i : α n) (pq : ι) (hpq : s.position n i = pq)
    (hi : ∀ (j : α n) (_ : j < i) (pq : ι) (_ : s.position n j = pq),
        IsZero (E.pageInfinity pq)) :
    IsIso (h.π i pq hpq) :=
  (h.isIso_π_iff i pq hpq).2 hi

section

variable (i : WithBot (α n)) (hi : IsIso (h.filtrationι i))

@[simps! hom]
noncomputable def isoFiltrationι :
    (h.filtration.obj i) ≅ X :=
  asIso (h.filtrationι i)

@[reassoc (attr := simp)]
lemma isoFiltrationι_hom_inv_id :
    h.filtrationι i ≫ (h.isoFiltrationι i hi).inv = 𝟙 _ :=
  (h.isoFiltrationι i hi).hom_inv_id

@[reassoc (attr := simp)]
lemma isoFiltrationι_inv_hom_id :
    (h.isoFiltrationι i hi).inv ≫ h.filtrationι i = 𝟙 _ :=
  (h.isoFiltrationι i hi).inv_hom_id

end

section

variable (i j : WithBot (α n)) (φ : i ⟶ j) (hij : IsIso (h.filtration.map φ))

@[simps! hom]
noncomputable def isoFiltrationMap : h.filtration.obj i ≅ h.filtration.obj j :=
  asIso (h.filtration.map φ)

@[reassoc (attr := simp)]
lemma isoFiltrationMap_hom_inv_id :
    h.filtration.map φ ≫ (h.isoFiltrationMap i j φ hij).inv = 𝟙 _ :=
  (h.isoFiltrationMap i j φ hij).hom_inv_id

@[reassoc (attr := simp)]
lemma isoFiltrationMap_inv_hom_id :
    (h.isoFiltrationMap i j φ hij).inv ≫ h.filtration.map φ = 𝟙 _ :=
  (h.isoFiltrationMap i j φ hij).inv_hom_id

end

section

variable (i : α n) (pq : ι) (hpq : s.position n i = pq) (hi : IsIso (h.π i pq hpq))

@[simps! hom]
noncomputable def isoπ :
    (h.filtration.obj i) ≅ E.pageInfinity pq :=
  asIso (h.π i pq hpq)

@[reassoc (attr := simp)]
lemma isoπ_hom_inv_id :
    h.π i pq hpq ≫ (h.isoπ i pq hpq hi).inv = 𝟙 _ :=
  (h.isoπ i pq hpq hi).hom_inv_id

@[reassoc (attr := simp)]
lemma isoπ_inv_hom_id :
    (h.isoπ i pq hpq hi).inv ≫ h.π i pq hpq = 𝟙 _ :=
  (h.isoπ i pq hpq hi).inv_hom_id

end

section

variable (i : α n) (pq : ι) (hpq : s.position n i = pq)
  (hi : IsIso (h.filtrationι i))

noncomputable def pageInfinityπ :
    X ⟶ E.pageInfinity pq :=
  (h.isoFiltrationι i hi).inv ≫ h.π i pq hpq

instance : Epi (h.pageInfinityπ i pq hpq hi) := by
  dsimp [pageInfinityπ]
  apply epi_comp

@[reassoc (attr := simp)]
lemma filtrationι_pageInfinityπ :
    h.filtrationι i ≫ h.pageInfinityπ i pq hpq hi = h.π i pq hpq := by
  simp [pageInfinityπ]

end

section

variable (i : α n) (pq : ι) (hpq : s.position n i = pq)
  (hi : IsIso (h.π i pq hpq))

noncomputable def pageInfinityι :
    E.pageInfinity pq ⟶ X :=
  (h.isoπ i pq hpq hi).inv ≫ h.filtrationι i

instance : Mono (h.pageInfinityι i pq hpq hi) := by
  dsimp [pageInfinityι]
  infer_instance

@[reassoc (attr := simp)]
lemma π_pageInfinityι :
    h.π i pq hpq ≫ h.pageInfinityι i pq hpq hi = h.filtrationι i := by
  simp [pageInfinityι]

variable (hi' : IsIso (h.filtrationι i))

@[reassoc (attr := simp)]
lemma pageInfinityπ_ι :
    h.pageInfinityπ i pq hpq hi' ≫ h.pageInfinityι i pq hpq hi = 𝟙 _ := by
  simp [pageInfinityι, pageInfinityπ]

@[reassoc (attr := simp)]
lemma pageInfinityι_π :
    h.pageInfinityι i pq hpq hi ≫ h.pageInfinityπ i pq hpq hi' = 𝟙 _ := by
  simp [pageInfinityι, pageInfinityπ]

end

@[reassoc]
lemma pageInfinityι_π_eq_zero (i j : α n) (hij : i < j) (pqi pqj : ι)
    (hpqi : s.position n i = pqi) (hpqj : s.position n j = pqj)
    (hi : IsIso (h.π i pqi hpqi)) (hj : IsIso (h.filtrationι j)) :
    h.pageInfinityι i pqi hpqi hi ≫ h.pageInfinityπ j pqj hpqj hj = 0 := by
  dsimp [pageInfinityι, pageInfinityπ]
  simp only [assoc, IsIso.comp_left_eq_zero,
    ← h.filtration_map_ι i j (homOfLE (by simpa using hij.le)),
    isoFiltrationι_hom_inv_id_assoc,
    h.comp_π i j (by simpa using hij)]

section

class CollapsesAt (h : E.StronglyConvergesToInDegree s n X) (i : α n) : Prop where
  condition (k : α n) (_ : k ≠ i) : IsZero (E.pageInfinity (s.position n k))

lemma isZero_of_collapsesAt (i : α n) [H : h.CollapsesAt i] (k : α n) (hk : k ≠ i)
    (pq : ι) (hpq : s.position n k = pq) :
    IsZero (E.pageInfinity pq) := by
  subst hpq
  exact H.condition k hk

variable (i : α n) [h.CollapsesAt i]

instance : IsIso (h.filtrationι i) :=
  h.isIso_filtrationι_of_isZero i (fun j hij pq hpq =>
    h.isZero_of_collapsesAt i j (by rintro rfl; simp at hij) pq hpq)

variable (pq : ι) (hpq : s.position n i = pq)

instance : IsIso (h.π i pq hpq) :=
  h.isIso_π_of_isZero _ _ _ (fun j hij pq hpq =>
    h.isZero_of_collapsesAt i j (by rintro rfl; simp at hij) pq hpq)

@[simps!]
noncomputable def isoOfCollapsesAt : X ≅ E.pageInfinity pq where
  hom := h.pageInfinityπ i pq hpq inferInstance
  inv := h.pageInfinityι i pq hpq inferInstance

end

section

variable (i j : α n)

class CollapsesAsSESAt : Prop where
  hij : i < j
  isIso_π (pq : ι) (hpq : s.position n i = pq) : IsIso (h.π i pq hpq)
  isIso_filtration_map (k : WithBot (α n)) (hk : s.pred n j = k) :
    IsIso (h.filtration.map (homOfLE (by
      simpa only [← hk] using s.le_pred'_of_lt n i j (by simpa using hij)) :
        WithBot.some i ⟶ k))
  isIso_filtrationι : IsIso (h.filtrationι j) := by infer_instance

variable (i j : α n)

lemma collapsesAsSESAt_of_succ (hij : s.pred n j = i) (pq : ι) (hpq : s.position n i = pq)
    (hi : IsIso (h.π i pq hpq)) (hj : IsIso (h.filtrationι j)) :
    h.CollapsesAsSESAt i j where
  hij := by simpa [hij] using s.pred_lt n j
  isIso_π pq' hpq' := by
    obtain rfl : pq' = pq := hpq'.symm.trans hpq
    exact hi
  isIso_filtration_map k hk := by
    obtain rfl : k = i := hk.symm.trans hij
    erw [Functor.map_id]
    infer_instance

variable [H : h.CollapsesAsSESAt i j]
include H

lemma lt_of_collapsesAsSESAt : i < j := H.hij

lemma isIso_π_of_collapsesAsSESAt (pq : ι) (hpq : s.position n i = pq) :
    IsIso (h.π i pq hpq) :=
  H.isIso_π pq hpq

lemma isIso_filtrationι_of_collapsesAsSESAt :
    IsIso (h.filtrationι j) :=
  H.isIso_filtrationι

lemma isIso_filtration_map (k : WithBot (α n)) (hk : s.pred n j = k) :
    IsIso (h.filtration.map (homOfLE (by
      simpa only [← hk] using s.le_pred'_of_lt n i j
          (by simpa using h.lt_of_collapsesAsSESAt i j)) :
        WithBot.some i ⟶ k)) := H.isIso_filtration_map k hk

variable (pqi pqj : ι) (hpqi : s.position n i = pqi) (hpqj : s.position n j = pqj)

@[simps]
noncomputable def shortComplexOfCollapses : ShortComplex C :=
  ShortComplex.mk _ _ (h.pageInfinityι_π_eq_zero i j
    (h.lt_of_collapsesAsSESAt i j) pqi pqj hpqi hpqj
    (h.isIso_π_of_collapsesAsSESAt i j pqi hpqi) (h.isIso_filtrationι_of_collapsesAsSESAt i j))

instance : Mono (h.shortComplexOfCollapses i j pqi pqj hpqi hpqj).f := by
  dsimp
  infer_instance

instance : Epi (h.shortComplexOfCollapses i j pqi pqj hpqi hpqj).g := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
noncomputable def shortComplexOfCollapsesIso
    (k : WithBot (α n)) (hk : s.pred n j = k) :
    h.shortComplex k j hk pqj hpqj ≅ h.shortComplexOfCollapses i j pqi pqj hpqi hpqj :=
  ShortComplex.isoMk ((h.isoFiltrationMap i k _ (h.isIso_filtration_map i j k hk)).symm ≪≫
    h.isoπ i pqi hpqi (h.isIso_π_of_collapsesAsSESAt i j pqi hpqi))
      (h.isoFiltrationι j (h.isIso_filtrationι_of_collapsesAsSESAt i j)) (Iso.refl _) (by
        dsimp
        rw [← cancel_epi (h.isoFiltrationMap i k _ (h.isIso_filtration_map i j k hk)).hom,
          isoFiltrationMap_hom, assoc, isoFiltrationMap_hom_inv_id_assoc,
          ← Functor.map_comp_assoc, homOfLE_comp]
        erw [h.filtration_map_ι, π_pageInfinityι]) (by simp)

lemma shortExact_of_collapses :
    (h.shortComplexOfCollapses i j pqi pqj hpqi hpqj).ShortExact :=
  ShortComplex.shortExact_of_iso
    (h.shortComplexOfCollapsesIso i j pqi pqj hpqi hpqj _ rfl)
    (by apply h.shortExact)

end

end

section

variable {E E' : SpectralSequence C c r₀}
  {n : σ} {X X' : C} (h : E.StronglyConvergesToInDegree s n X)
  (h' : E'.StronglyConvergesToInDegree s n X')
  (f : E ⟶ E')

structure Hom where
  φ : X ⟶ X'
  τ : h.filtration ⟶ h'.filtration
  commι (i : WithBot (α n)) :
    h.filtrationι i ≫ φ = τ.app i ≫ h'.filtrationι i
  commπ (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    h.π i pq hpq ≫ Hom.mapPageInfinity f pq =
      τ.app i ≫ h'.π i pq hpq

lemma _root_.CategoryTheory.SpectralSequence.StronglyConvergesToInDegree.exists_isIso_aux :
    ∃ (k : α n), IsIso (h.filtrationι k) ∧ IsIso (h'.filtrationι k) := by
  obtain ⟨k₁, hk₁⟩ := h.exists_isIso
  obtain ⟨k₂, hk₂⟩ := h'.exists_isIso
  exact ⟨max k₁ k₂, ⟨h.isIso_filtrationι_of_GE _ _ (by simp) hk₁,
    h'.isIso_filtrationι_of_GE _ _ (by simp) hk₂⟩⟩

lemma _root_.CategoryTheory.SpectralSequence.StronglyConvergesToInDegree.exists_isZero_aux :
    ∃ (k : α n), IsZero (h.filtration.obj (s.pred n k)) ∧
      IsZero (h'.filtration.obj (s.pred n k)) := by
  obtain ⟨k₁, hk₁⟩ := h.exists_isZero
  obtain ⟨k₂, hk₂⟩ := h'.exists_isZero
  obtain H | H := le_total k₁ k₂
  · exact ⟨k₁, hk₁, h'.isZero_filtration_obj_of_LE (s.pred n k₁) (s.pred n k₂)
      (s.pred_monotone _ _ _ H) hk₂⟩
  · exact ⟨k₂, h.isZero_filtration_obj_of_LE (s.pred n k₂) (s.pred n k₁)
      (s.pred_monotone _ _ _ H) hk₁, hk₂⟩

variable {h h' f}

lemma hom_ext {α₁ α₂ : h.Hom h' f} (h : α₁.τ = α₂.τ) : α₁ = α₂ := by
  obtain ⟨φ₁, τ, commι₁, commπ₁⟩ := α₁
  obtain ⟨φ₂, τ₂, commι₂, commπ₂⟩ := α₂
  subst h
  dsimp at commι₂ commπ₂
  simp only [Hom.mk.injEq, and_true]
  obtain ⟨k, _, _⟩ := exists_isIso_aux h h'
  rw [← cancel_epi (h.filtrationι k), commι₁, commι₂]

@[simps]
noncomputable def Hom.mapShortComplex (β : h.Hom h' f) (i : WithBot (α n)) (j : α n)
    (hij : s.pred n j = i) (pq : ι) (hpq : s.position n j = pq) :
    h.shortComplex i j hij pq hpq ⟶ h'.shortComplex i j hij pq hpq where
  τ₁ := β.τ.app i
  τ₂ := β.τ.app (WithBot.some j)
  τ₃ := Hom.mapPageInfinity f pq
  comm₁₂ := (β.τ.naturality _).symm
  comm₂₃ := (β.commπ _ _ _).symm

lemma Hom.isIso_τ_succ (β : h.Hom h' f) (i : WithBot (α n)) (j : α n)
    (hij : s.pred n j = i) (pq : ι) (hpq : s.position n j = pq)
    (hf : IsIso (Hom.mapPageInfinity f pq)) (hα : IsIso (β.τ.app i)) :
    IsIso (β.τ.app (WithBot.some j)) :=
  ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' (β.mapShortComplex i j hij pq hpq)
    (h.shortExact i j hij pq hpq) (h'.shortExact i j hij pq hpq) hα hf

lemma Hom.isIso_φ_of_isIso_τ (α : h.Hom h' f) (hα : IsIso α.τ) :
    IsIso α.φ := by
  obtain ⟨k, _, _⟩ := exists_isIso_aux h h'
  exact IsIso.of_isIso_fac_left (α.commι k)

instance (α : h.Hom h' f) : IsIso (α.τ.app ⊥) :=
  ⟨0, h.isZero_filtration_obj_none.eq_of_src _ _,
    h'.isZero_filtration_obj_none.eq_of_src _ _⟩

section

variable (β : h.Hom h' f) (hβ : ∀ (pq : ι) (_ : s.stripe pq = n), IsIso (Hom.mapPageInfinity f pq))
-- note: the assumption hβ could be slightly sharper in the next lemma below

include hβ

lemma Hom.isIso_τ_of_sub (i j : WithBot (α n)) (k : ℕ)
    (hk : s.sub n j k = i) (hi : IsIso (β.τ.app i)) :
    IsIso (β.τ.app j) := by
  revert i j hi
  induction k with
  | zero =>
    intro i j hij _
    obtain rfl : j = i := by simpa using hij
    infer_instance
  | succ k hk =>
    intro i j hij _
    have := hβ
    rw [← s.sub_sub n j 1 k _ (add_comm _ _)] at hij
    have := hk _ _ hij inferInstance
    have : ∀ (l : WithBot (α n)) (_ : s.sub n j 1 = l)
      (_ : IsIso (β.τ.app l)), IsIso (β.τ.app j) := fun l hl hl' => by
        by_cases hj : j = ⊥
        · subst hj
          infer_instance
        · obtain ⟨j, rfl⟩ :=  WithBot.ne_bot_iff_exists.1 hj
          exact β.isIso_τ_succ l j hl _ rfl (hβ _ (by simp)) hl'
    exact this _ rfl inferInstance

lemma Hom.isIso_τ_of_isIso_mapPageInfinity :
    IsIso β.τ := by
  suffices ∀ j, IsIso (β.τ.app j) from NatIso.isIso_of_isIso_app _
  intro j
  obtain _ | j := j
  · change IsIso (β.τ.app ⊥)
    infer_instance
  · obtain ⟨k, z, z'⟩ := exists_isZero_aux h h'
    obtain ⟨d, hd⟩ := s.exists_sub_le n j k
    let l := (s.sub n j (d + 1))
    have hlk : l ≤ s.pred n k := by
      dsimp [l]
      rw [← s.sub_sub n j d 1 _ rfl, ← s.pred'_some, s.sub_one]
      exact s.pred'_monotone _ _ _ hd
    have : IsIso (β.τ.app l) := ⟨0, (h.isZero_filtration_obj_of_LE l _ hlk z).eq_of_src _ _,
      (h'.isZero_filtration_obj_of_LE l _ hlk z').eq_of_src _ _⟩
    exact β.isIso_τ_of_sub hβ l j (d + 1) rfl this

lemma Hom.isIso_φ_of_isIso_mapPageInfinity :
    IsIso β.φ :=
  β.isIso_φ_of_isIso_τ (β.isIso_τ_of_isIso_mapPageInfinity hβ)

end

end

end StronglyConvergesToInDegree

end SpectralSequence

end CategoryTheory
