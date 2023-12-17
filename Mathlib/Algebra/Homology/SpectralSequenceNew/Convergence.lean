import Mathlib.Algebra.Homology.SpectralSequenceNew.PageInfinity
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

universe w₁ w₂ w₃ v u

lemma Nat.eq_add_of_le {i j : ℕ} (hij : i ≤ j) :
    ∃ (d : ℕ), j = i + d :=
  ⟨j - i, by rw [← Nat.sub_eq_iff_eq_add' hij]⟩

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
  (ι : Type w₁) {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

@[nolint checkUnivs]
structure ConvergenceStripes where
  σ : Type w₂
  α (n : σ) : Type w₃
  hα (n : σ) : LinearOrder (α n) := by infer_instance
  pred (n : σ) (i : α n) : WithBot (α n)
  pred_lt n (i : α n) : pred n i < WithBot.some i := by aesop
  stripe : ι → σ
  position (n : σ) (i : α n) : ι
  stripe_position (n : σ) (i : α n) : stripe (position n i) = n := by aesop
  discrete (n : σ) (i j : α n) (h₁ : pred n i < WithBot.some j) : i ≤ j
  finite_segment (n : σ) (i j : α n) : Set.Finite (fun (k : α n) => i ≤ k ∧ k ≤ j)

attribute [instance] ConvergenceStripes.hα

def cohomologicalStripes : ConvergenceStripes (ℤ × ℤ) where
  σ := ℤ
  α _ := ℤ
  stripe pq := pq.1 + pq.2
  position n i := ⟨n + 1 - i, i - 1⟩
  pred n i := some (i - 1)
  pred_lt := by
    dsimp [WithBot.some]
    aesop
  finite_segment n i j := by
    rw [Set.finite_def]
    by_cases hij : i ≤ j
    · obtain ⟨d, rfl⟩ := Int.eq_add_ofNat_of_le hij
      refine ⟨Fintype.ofSurjective (fun (k : Fin (d + 1)) =>
        ⟨i + k, ⟨by linarith, by linarith [k.is_lt]⟩⟩) ?_⟩
      rintro ⟨x, h₁, h₂⟩
      obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h₁
      exact ⟨⟨k, by linarith⟩, rfl⟩
    · refine ⟨@Fintype.ofIsEmpty _ ⟨?_⟩⟩
      rintro ⟨x, h₁, h₂⟩
      linarith
  discrete n (i j : ℤ) h := by
    linarith [show i - 1 < j from WithBot.some_lt_some.1 h]

variable {ι}

variable (s : ConvergenceStripes ι)

namespace ConvergenceStripes

lemma stripe_eq (n : s.σ) (i : s.α n) (pq : ι) (hpq : s.position n i = pq) :
    s.stripe pq = n := by
  rw [← hpq, s.stripe_position]

def segment (n : s.σ) (i j : s.α n) : Set (s.α n) :=
  fun k => i ≤ k ∧ k ≤ j

noncomputable instance (n : s.σ) (i j : s.α n) : Fintype (s.segment n i j) := by
  have h := s.finite_segment n i j
  rw [Set.finite_def] at h
  exact h.some

def segment' (n : s.σ) (i : s.α n) (j : WithBot (s.α n)) : Set (WithBot (s.α n)) :=
  fun k => WithBot.some i ≤ k ∧ k ≤ j

instance (n : s.σ) (i : s.α n) : Subsingleton (s.segment' n i ⊥) where
  allEq := by
    rintro ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    simp only [le_bot_iff] at ha' hb'
    subst ha' hb'
    rfl

noncomputable instance (n : s.σ) (i : s.α n) (j : WithBot (s.α n)) :
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

lemma pred_le (n : s.σ) (i : s.α n) : s.pred n i ≤ WithBot.some i :=
  (s.pred_lt n i).le

lemma pred_monotone (n : s.σ) (i j : s.α n) (hij : i ≤ j) :
    s.pred n i ≤ s.pred n j := by
  obtain _ | rfl := hij.lt_or_eq
  · by_contra!
    by_cases hi : ∃ (k : s.α n), k = s.pred n i
    · obtain ⟨k, hk⟩ := hi
      have hj := s.discrete n j k (by simpa only [← hk] using this)
      have hk' := s.pred_lt n i
      rw [← hk] at hk'
      replace hij : WithBot.some i ≤ WithBot.some j := WithBot.some_le_some.2 hij
      replace hj : WithBot.some j ≤ WithBot.some k := WithBot.some_le_some.2 hj
      have := lt_of_le_of_lt (hij.trans hj) hk'
      simp at this
    · rw [← WithBot.ne_bot_iff_exists, ne_eq, not_not] at hi
      rw [hi] at this
      simp at this
  · rfl

def pred' (n : s.σ) : WithBot (s.α n) → WithBot (s.α n)
  | ⊥ => ⊥
  | WithBot.some x => s.pred n x

@[simp]
lemma pred'_bot (n : s.σ) : s.pred' n ⊥ = ⊥ := rfl

@[simp]
lemma pred'_some (n : s.σ) (i : s.α n) :
    s.pred' n (WithBot.some i) = s.pred n i := rfl

lemma pred'_le (n : s.σ) (i : WithBot (s.α n)) :
    s.pred' n i ≤ i := by
  cases' i with i
  · erw [pred'_bot]
    rfl
  · erw [pred'_some]
    exact s.pred_le n i

lemma pred_injective (n : s.σ) (i j : s.α n) (hij : s.pred n i = s.pred n j) :
    i = j := by
  revert i j hij
  suffices ∀ (i j : s.α n) (_ : s.pred n i = s.pred n j) (_ : i ≤ j), i = j by
    intro i j hij
    obtain h | h := le_total i j
    · exact this i j hij h
    · exact (this j i hij.symm h).symm
  intro i j hij h
  exact le_antisymm h (s.discrete n j i (by simpa only [← hij] using s.pred_lt n i))

lemma pred'_monotone (n : s.σ) (i j : WithBot (s.α n)) (hij : i ≤ j) :
    s.pred' n i ≤ s.pred' n j := by
  obtain _ | j := j
  · obtain rfl :=le_bot_iff.1 hij
    rfl
  · obtain _ | i := i
    · exact bot_le
    · exact s.pred_monotone _ _ _ (by simpa using hij)

lemma le_pred'_of_lt (n : s.σ) (i j : WithBot (s.α n)) (hi : i < j) :
    i ≤ s.pred' n j := by
  obtain _ | i := i
  · simp
  · obtain _ | j := j
    · simp at hi
    · by_contra!
      simp only [not_le] at this
      have := lt_of_le_of_lt (s.discrete n j i this) (WithBot.some_lt_some.1 hi)
      simp at this

lemma lt_iff_le_pred' (n : s.σ) (i : s.α n) (j : WithBot (s.α n)) :
    i < j ↔ i ≤ s.pred' n j := by
  constructor
  · apply s.le_pred'_of_lt
  · intro h
    obtain _ | j := j
    · erw [pred'_bot] at h
      simp at h
    · exact lt_of_le_of_lt h (s.pred_lt n j)

def sub' (n : s.σ) : ℕ → WithBot (s.α n) → WithBot (s.α n)
  | 0 => id
  | k + 1 => s.pred' n ∘ sub' n k

def sub (n : s.σ) (i : WithBot (s.α n)) (k : ℕ) : WithBot (s.α n) := s.sub' n k i

@[simp]
lemma sub_zero (n : s.σ) (i : WithBot (s.α n)) :
    s.sub n i 0 = i := rfl

lemma sub_one (n : s.σ) (i : WithBot (s.α n)) :
    s.sub n i 1 = s.pred' n i := rfl

lemma sub_succ (n : s.σ) (i : WithBot (s.α n)) (k : ℕ) :
    s.sub n i (k + 1) = s.pred' n (s.sub n i k) := rfl

lemma sub_sub (n : s.σ) (i : WithBot (s.α n)) (k₁ k₂ k : ℕ) (h : k₁ + k₂ = k) :
    s.sub n (s.sub n i k₁) k₂ = s.sub n i k := by
  revert k₁ k h
  induction' k₂ with k₂ hk₂
  · intro k₁ k h
    obtain rfl : k₁ = k := by simpa using h
    simp
  · intro k₁ k h
    obtain rfl : k₁ + k₂ + 1 = k := by simpa only [Nat.succ_eq_add_one, add_assoc] using h
    simp only [sub_succ, hk₂ k₁ _ rfl]

@[simp]
lemma sub_bot (n : s.σ) (k : ℕ) :
    s.sub n ⊥ k = ⊥ := by
  induction' k with k hk
  · simp
  · simp [hk, sub_succ]

lemma sub_le_self (n : s.σ) (i : WithBot (s.α n)) (k : ℕ) :
    s.sub n i k ≤ i := by
  revert i
  induction' k with k hk
  · simp
  · intro i
    rw [sub_succ]
    exact (s.pred'_le n _).trans (hk _)

lemma sub_antitone (n : s.σ) (i : WithBot (s.α n)) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    s.sub n i k₂ ≤ s.sub n i k₁ := by
  obtain ⟨k, rfl⟩ := Nat.eq_add_of_le h
  rw [← s.sub_sub n i k₁ k _ rfl]
  apply sub_le_self

lemma sub_succ_lt (n : s.σ) (i : s.α n) (k : ℕ) :
    s.sub n (WithBot.some i) (k + 1) < WithBot.some i :=
  lt_of_le_of_lt (s.sub_antitone n (WithBot.some i) 1 (k + 1) (by linarith)) (by
    rw [sub_one, pred'_some]
    apply pred_lt)

lemma sub_eq_self_iff (n : s.σ) (i : WithBot (s.α n)) (k : ℕ) :
    s.sub n i k = i ↔ i = ⊥ ∨ k = 0 := by
  constructor
  · intro h
    obtain _ | i := i
    · exact Or.inl rfl
    · refine' Or.inr _
      obtain _ | k := k
      · rfl
      · change s.sub n i (k + 1) = (WithBot.some i) at h
        simpa only [h, lt_self_iff_false] using s.sub_succ_lt n i k
  · rintro (rfl | rfl) <;> simp

lemma sub_injective (n : s.σ) (i : WithBot (s.α n)) (k₁ k₂ : ℕ)
    (h : s.sub n i k₁ = s.sub n i k₂) :
    s.sub n i k₁ = ⊥ ∨ k₁ = k₂ := by
  revert i k₁ k₂ h
  suffices ∀ (i : WithBot (s.α n)) (k₁ k₂ : ℕ) (_ : k₁ ≤ k₂) (_ : s.sub n i k₁ = s.sub n i k₂),
      s.sub n i k₁ = ⊥ ∨ k₁ = k₂ by
    intro i k₁ k₂ hk
    obtain h | h := le_total k₁ k₂
    · exact this i k₁ k₂ h hk
    · obtain h' | h' := this i k₂ k₁ h hk.symm
      · exact Or.inl (hk.trans h')
      · exact Or.inr h'.symm
  intro i k₁ k₂ hk h
  obtain ⟨d, rfl⟩ := Nat.eq_add_of_le hk
  replace h := h.symm
  rw [← s.sub_sub n i k₁ d _ rfl, sub_eq_self_iff] at h
  obtain h | rfl := h
  · exact Or.inl h
  · exact Or.inr (by simp)

lemma exists_sub_eq (n : s.σ) (i j : s.α n) (hij : i ≤ j) :
    ∃ (k : ℕ), s.sub n j k = i := by
  let S : Set ℕ := fun k => (WithBot.some i) ≤ s.sub n (WithBot.some j) k
  have hS : S.Finite := by
    let φ : S → s.segment' n i j := fun x => ⟨s.sub n j x.1, x.2, s.sub_le_self _ _ _⟩
    refine' ⟨Fintype.ofInjective φ _⟩
    intro k₁ k₂ h
    simp only [Subtype.mk.injEq] at h
    obtain h' | h' := s.sub_injective n _ _ _ h
    · exfalso
      have h₁ : WithBot.some i ≤ s.sub n j k₁ := k₁.2
      simp only [h', le_bot_iff, WithBot.coe_ne_bot] at h₁
    · ext
      exact h'
  have hS' : S.Nonempty := ⟨0, by
    change WithBot.some i ≤ s.sub n j 0
    simpa only [s.sub_zero, WithBot.coe_le_coe] using hij⟩
  obtain ⟨l, hl, hl'⟩ := Set.Finite.exists_maximal_wrt id S hS hS'
  refine ⟨l, le_antisymm ?_ hl⟩
  by_contra!
  rw [lt_iff_le_pred', ← sub_one, s.sub_sub n j l 1 _ rfl] at this
  have := hl' (l + 1) this (by simp)
  simp at this

lemma exists_sub_le (n : s.σ) (i : WithBot (s.α n)) (j : s.α n) :
    ∃ (k : ℕ), s.sub n i k ≤ WithBot.some j := by
  obtain _ | i := i
  · exact ⟨0, by simp⟩
  · obtain hij | hij := le_total i j
    · use 0
      simpa only [sub_zero] using WithBot.some_le_some.2 hij
    · obtain ⟨k, hk⟩ := s.exists_sub_eq n j i hij
      use k
      rw [← hk]
      rfl

end ConvergenceStripes

variable (E : SpectralSequence C c r₀)

class CollapsesAt (n : s.σ) (i : s.α n) : Prop where
  condition : ∀ (k : s.α n) (_ : k ≠ i), IsZero (E.pageInfinity (s.position n k))

lemma isZero_of_collapsesAt (n : s.σ) (i : s.α n) [h : E.CollapsesAt s n i]
    (k : s.α n) (hk : k ≠ i) : IsZero (E.pageInfinity (s.position n k)) :=
  h.condition k hk

lemma isZero_of_collapsesAt_of_LT (n : s.σ) (i : s.α n) [h : E.CollapsesAt s n i]
    (k : s.α n) (hk : k < i) : IsZero (E.pageInfinity (s.position n k)) :=
  h.condition k (by
    rintro rfl
    simp only [lt_self_iff_false] at hk)

lemma isZero_of_collapsesAt_of_GT (n : s.σ) (i : s.α n) [h : E.CollapsesAt s n i]
    (k : s.α n) (hk : i < k) : IsZero (E.pageInfinity (s.position n k)) :=
  h.condition k (by
    rintro rfl
    simp only [lt_self_iff_false] at hk)

structure StronglyConvergesToInDegree (n : s.σ) (X : C) where
  hasPageInfinityAt : ∀ (pq : ι) (_ : s.stripe pq = n), E.HasPageInfinityAt pq
  filtration' : (WithBot (s.α n)) ⥤ MonoOver X
  exists_isZero' :
    ∃ (j : s.α n), IsZero ((filtration' ⋙ MonoOver.forget _ ⋙ Over.forget _).obj (s.pred n j))
  exists_isIso' : ∃ (j : s.α n), IsIso ((filtration' ⋙ MonoOver.forget _).obj j).hom
  π' (i : s.α n) (pq : ι) (hpq : s.position n i = pq) :
    ((filtration' ⋙ MonoOver.forget _ ⋙ Over.forget _).obj (WithBot.some i)) ⟶ E.pageInfinity pq
  epi_π' (i : s.α n) (pq : ι) (hpq : s.position n i = pq) : Epi (π' i pq hpq)
  comp_π' (i : WithBot (s.α n)) (j : s.α n) (hij : s.pred n j = i) (pq : ι) (hpq : s.position n j = pq) :
    (filtration' ⋙ MonoOver.forget X ⋙ Over.forget X).map
      (homOfLE (show i ≤ WithBot.some j by
        subst hij
        exact s.pred_le n j)) ≫ π' j pq hpq = 0
  exact_π' (i : WithBot (s.α n)) (j : s.α n) (hij : s.pred n j = i) (pq : ι)
    (hpq : s.position n j = pq) :
      (ShortComplex.mk _ _ (comp_π' i j hij pq hpq)).Exact

namespace StronglyConvergesToInDegree

variable {E s}
variable {n : s.σ} {X : C} (h : E.StronglyConvergesToInDegree s n X)

def filtration : WithBot (s.α n) ⥤ C := h.filtration' ⋙ MonoOver.forget X ⋙ Over.forget X

def filtrationι (i : WithBot (s.α n)) : h.filtration.obj i ⟶ X :=
  ((h.filtration' ⋙ MonoOver.forget X).obj i).hom

instance (i : WithBot (s.α n)) : Mono (h.filtrationι i) := by
  dsimp [filtrationι]
  infer_instance

@[reassoc (attr := simp)]
lemma filtration_map_ι {i j : WithBot (s.α n)} (f : i ⟶ j) :
    h.filtration.map f ≫ h.filtrationι j = h.filtrationι i :=
  Over.w ((h.filtration' ⋙ MonoOver.forget X).map f)

instance {i j : WithBot (s.α n)} (f : i ⟶ j) :
    Mono (h.filtration.map f) :=
  mono_of_mono_fac (h.filtration_map_ι f)

lemma exists_isZero : ∃ (j : s.α n), IsZero (h.filtration.obj (s.pred n j)) :=
  h.exists_isZero'

lemma exists_isIso : ∃ (j : s.α n), IsIso (h.filtrationι j) :=
  h.exists_isIso'

def π (i : s.α n) (pq : ι) (hpq : s.position n i = pq) :
    h.filtration.obj i ⟶ E.pageInfinity pq :=
  h.π' i pq hpq

instance (i : s.α n) (pq : ι) (hpq : s.position n i = pq) :
    Epi (h.π i pq hpq) :=
  h.epi_π' i pq hpq

section

variable (i : WithBot (s.α n)) (j : s.α n) (hij : s.pred n j = i)
  (pq : ι) (hpq : s.position n j = pq)

lemma comp_π :
    h.filtration.map (homOfLE (show i ≤ some j by subst hij; exact s.pred_le n j)) ≫
      h.π j pq hpq = 0 :=
  h.comp_π' i j hij pq hpq

@[simps]
noncomputable def shortComplex :
    ShortComplex C :=
  ShortComplex.mk _ _ (h.comp_π i j hij pq hpq)

instance : Mono (h.shortComplex i j hij pq hpq).f := by dsimp; infer_instance

instance : Epi (h.shortComplex i j hij pq hpq).g := by dsimp; infer_instance

lemma shortExact :
    (h.shortComplex i j hij pq hpq).ShortExact where
  exact := h.exact_π' i j hij pq hpq

end

lemma isIso_filtration_map_from_pred_iff (i : WithBot (s.α n)) (j : s.α n)
    (φ : i ⟶ some j) (hij : s.pred n j = i) (pq : ι) (hpq : s.position n j = pq) :
    IsIso (h.filtration.map φ) ↔ IsZero (E.pageInfinity pq) :=
  (h.shortExact i j hij pq hpq).isIso_f_iff

lemma isIso_filtration_map_from_pred'_iff
    (i j : WithBot (s.α n)) (φ : i ⟶ j) (hij : s.pred' n j = i) :
    IsIso (h.filtration.map φ) ↔
      ∀ (k : s.α n) (_ : j = WithBot.some k) (pq : ι) (_ : s.position n k = pq),
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

lemma isIso_filtration_map_comp_iff (i j k : WithBot (s.α n)) (f : i ⟶ j) (g : j ⟶ k) :
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

lemma isZero_of_isIso_filtration_map (i j : WithBot (s.α n)) (φ : i ⟶ j)
    (hφ : IsIso (h.filtration.map φ)) (k : s.α n)
    (h₁ : i ≤ s.pred n k) (h₂ : WithBot.some k ≤ j)
    (pq : ι) (hpq : s.position n k = pq) :
    IsZero (E.pageInfinity pq) := by
  obtain rfl : φ = homOfLE h₁ ≫ homOfLE (s.pred_le n k) ≫ homOfLE h₂ := rfl
  rw [isIso_filtration_map_comp_iff, isIso_filtration_map_comp_iff,
    h.isIso_filtration_map_from_pred_iff _ k _ rfl pq hpq] at hφ
  exact hφ.2.1

lemma isIso_filtration_map'_iff (i j : WithBot (s.α n)) (φ : j ⟶ i) (k : ℕ) (hk : s.sub n i k = j) :
    IsIso (h.filtration.map φ) ↔
      ∀ (d : ℕ) (_ : d < k) (j : s.α n) (_ : s.sub n i d = WithBot.some j)
          (pq : ι) (_ : s.position n j = pq),
        IsZero (E.pageInfinity pq) := by
  subst hk
  induction' k with k hk
  · simp only [Nat.zero_eq, ConvergenceStripes.sub_zero, not_lt_zero', forall_eq',
      IsEmpty.forall_iff, forall_const, iff_true]
    change IsIso (h.filtration.map (𝟙 _))
    infer_instance
  · erw [h.isIso_filtration_map_comp_iff (s.sub n i (k + 1)) (s.sub n i k) i
      (homOfLE (s.sub_antitone _ _ _  _ (by linarith))) (homOfLE (s.sub_le_self n i k)), hk,
      h.isIso_filtration_map_from_pred'_iff _ _ _ (by rw [s.sub_succ])]
    constructor
    · rintro ⟨h₁, h₂⟩ d hd j hj pq hpq
      have hd' : d ≤ k := by linarith
      obtain hd'' | rfl := hd'.lt_or_eq
      · exact h₂ d hd'' j hj pq hpq
      · exact h₁ j hj pq hpq
    · intro H
      constructor
      · intro l hl pq hpq
        exact H k (by linarith) l hl pq hpq
      · intro d hd j hj pq hpq
        exact H d (by linarith) j hj pq hpq

lemma isZero_filtration_obj_none : IsZero (h.filtration.obj none) := by
  obtain ⟨j, hj⟩ := h.exists_isZero
  rw [IsZero.iff_id_eq_zero]
  let φ : ⊥ ⟶ s.pred n j := homOfLE bot_le
  rw [← cancel_mono (h.filtration.map φ)]
  apply hj.eq_of_tgt

lemma isZero_filtration_obj_iff (i : WithBot (s.α n)) :
    IsZero (h.filtration.obj i) ↔
      ∀ (j : s.α n) (_ : WithBot.some j ≤ i) (pq : ι) (_ : s.position n j = pq),
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

lemma isIso_filtration_map_iff (i j : WithBot (s.α n)) (φ : i ⟶ j) :
    IsIso (h.filtration.map φ) ↔
      ∀ (k : s.α n) (_ : i ≤ s.pred n k) (_ : WithBot.some k ≤ j)
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
      suffices ∀ (i : s.α n) (φ : WithBot.some i ⟶ WithBot.some j), (∀ (k : s.α n)
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
          exact H k h₁ (WithBot.some_le_some.2 h₂) pq hpq
      intro i φ H
      have hij : i ≤ j := WithBot.some_le_some.1 (leOfHom φ)
      obtain ⟨k, hk⟩ := s.exists_sub_eq n i j hij
      rw [h.isIso_filtration_map'_iff j i φ k hk]
      intro d hd l hl pq hpq
      refine' H l ?_ ?_ pq hpq
      · rw [← s.pred'_some, ← hl, ← s.sub_one, s.sub_sub n j d 1 _ rfl, ← hk]
        apply s.sub_antitone
        linarith
      · rw [← WithBot.some_le_some]
        change (WithBot.some l) ≤ (WithBot.some j)
        rw [← hl]
        apply s.sub_le_self

lemma isIso_filtrationι_of_GE (i j : WithBot (s.α n)) (hij : i ≤ j)
    (hi : IsIso (h.filtrationι i)) :
    IsIso (h.filtrationι j) := by
  have := epi_of_epi_fac (h.filtration_map_ι (homOfLE hij))
  apply isIso_of_mono_of_epi

lemma isIso_filtation_map_of_isIso_filtrationι (i j : WithBot (s.α n)) (φ : i ⟶ j)
    (hi : IsIso (h.filtrationι i)) :
    IsIso (h.filtration.map φ) := by
  have := h.isIso_filtrationι_of_GE i j (leOfHom φ) hi
  exact IsIso.of_isIso_fac_right (h.filtration_map_ι φ)

lemma isIso_filtrationι_iff (i : WithBot (s.α n)) :
    IsIso (h.filtrationι i) ↔ ∀ (j : s.α n) (_ : i < j) (pq : ι) (_ : s.position n j = pq),
      IsZero (E.pageInfinity pq) := by
  constructor
  · intro hi j hij pq hpq
    rw [← h.isIso_filtration_map_from_pred_iff _ j (homOfLE (s.pred_le n j)) rfl pq hpq]
    apply h.isIso_filtation_map_of_isIso_filtrationι
    exact h.isIso_filtrationι_of_GE _ _ (s.le_pred'_of_lt n _ _ hij) hi
  · obtain ⟨j, hj⟩ := h.exists_isIso
    obtain hij | hij := le_total i (WithBot.some j)
    · intro hi
      rw [← h.filtration_map_ι (homOfLE hij)]
      have := (h.isIso_filtration_map_iff i j (homOfLE hij)).2 (by
        intro k hk _ pq hpq
        exact hi k (lt_of_le_of_lt hk (s.pred_lt n k)) pq hpq)
      infer_instance
    · intro
      exact h.isIso_filtrationι_of_GE _ _ hij hj

end StronglyConvergesToInDegree

end SpectralSequence

end CategoryTheory

#lint
