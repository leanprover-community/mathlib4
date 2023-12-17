import Mathlib.Algebra.Homology.SpectralSequenceNew.PageInfinity
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

lemma Nat.eq_add_of_le {i j : ℕ} (hij : i ≤ j) :
    ∃ (d : ℕ), j = i + d :=
  ⟨j - i, by rw [← Nat.sub_eq_iff_eq_add' hij]⟩

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [Abelian C]
  (ι : Type*) {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

structure ConvergenceStripes where
  σ : Type*
  α (n : σ) : Type*
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

/-lemma exists_sub_le (n : s.σ) (i : WithBot (s.α n)) (j : s.α n) :
    ∃ (k : ℕ), s.sub n i k ≤ WithBot.some j := by
  obtain _ | i := i
  · exact ⟨0, by simp⟩
  · by_cases hi : ∃ (k : ℕ), s.sub n (WithBot.some i) k = ⊥
    · obtain ⟨k, hk⟩ := hi
      refine ⟨k, ?_⟩
      erw [hk]
      apply bot_le
    · let S : Set ℕ := fun k => (WithBot.some j) < s.sub n (WithBot.some i) k
      have hS : S.Finite := by
        let X : Set (s.α n) := fun k => j ≤ k ∧ k ≤ i
        let φ : S → s.segment' n j i :=
          fun x => ⟨s.sub n i x.1, LT.lt.le x.2, s.sub_le_self _ _ _⟩
        refine' ⟨Fintype.ofInjective φ _⟩
        intro k₁ k₂ h
        simp only [Subtype.mk.injEq] at h
        obtain h | h := s.sub_injective n _ _ _ h
        · exfalso
          exact hi ⟨_, h⟩
        · ext
          exact h
      obtain ⟨k, hk⟩ : ∃ (k : ℕ), ∀ (x : S), x < k := by
        sorry
      refine' ⟨k, _⟩
      by_contra!
      have h := hk ⟨k, this⟩
      simp at h-/

end ConvergenceStripes

variable (E : SpectralSequence C c r₀)

class CollapsesAt (n : s.σ) (i : s.α n) where
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

/-lemma isIso_filtration_map_iff (i j : WithBot (s.α n)) (φ : i ⟶ j) :
    IsIso (h.filtration.map φ) ↔
      ∀ (k : s.α n) (h₁ : i ≤ s.pred n k) (h₂ : WithBot.some k ≤ j)
        (pq : ι) (hpq : s.position n k = pq), IsZero (E.pageInfinity pq) := by
  constructor
  · apply isZero_of_isIso_filtration_map
  · sorry-/

end StronglyConvergesToInDegree

end SpectralSequence

end CategoryTheory
