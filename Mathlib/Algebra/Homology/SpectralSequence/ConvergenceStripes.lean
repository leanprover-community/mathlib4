/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.SpectralSequence.PageInfinity
public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# Convergence of spectral sequences

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C]
  (ι : Type*) {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

variable {σ : Type*} (α : σ → Type*) [∀ n, LinearOrder (α n)]

structure ConvergenceStripes where
  pred (n : σ) (i : α n) : WithBot (α n)
  pred_lt n (i : α n) : pred n i < WithBot.some i := by aesop
  stripe : ι → σ
  position (n : σ) (i : α n) : ι
  stripe_position (n : σ) (i : α n) : stripe (position n i) = n := by grind
  discrete (n : σ) (i j : α n) (h₁ : pred n i < WithBot.some j) : i ≤ j
  finite_icc' (n : σ) (i j : α n) (hij : i ≤ j) : (Set.Icc i j).Finite

variable {α}

@[simps, implicit_reducible]
def cohomologicalStripes :
    ConvergenceStripes (ℤ × ℤ) (fun (_ : ℤ) ↦ ℤ) where
  stripe pq := pq.1 + pq.2
  position n i := ⟨n + 1 - i, i - 1⟩
  pred n i := WithBot.some (i - 1)
  discrete n (i j : ℤ) h := by simp at h; lia
  finite_icc' _ i j hij := by
    obtain ⟨d, rfl⟩ := Int.le.dest hij
    refine Finite.of_surjective
      (fun (k : Fin (d + 1)) ↦ ⟨i + k, ⟨by lia, by have := k.is_lt; lia⟩⟩)
      (fun ⟨x, h₁, h₂⟩ ↦ ?_)
    obtain ⟨k, rfl⟩ := Int.le.dest h₁
    exact ⟨⟨k, by lia⟩, rfl⟩

@[simps, implicit_reducible]
def cohomomologicalStripesFin (l : ℕ) :
    ConvergenceStripes (ℤ × Fin l) (fun (_ : ℤ) ↦ Fin l) where
  stripe pq := pq.1 + pq.2.val
  pred _ j := match j with
    | ⟨0, _⟩   => ⊥
    | ⟨j + 1, _⟩ => WithBot.some ⟨j, by lia⟩
  pred_lt n := by rintro ⟨_ | _⟩ <;> simp
  position n i := ⟨n - i.val, i⟩
  discrete := by rintro n _ ⟨_, _⟩ _; aesop
  finite_icc' _ _ _ _ := .of_injective Subtype.val (fun _ _ _ ↦ by grind)

@[simps, implicit_reducible]
def cohomologicalStripesNat :
    ConvergenceStripes (ℕ × ℕ) (fun (n : ℕ) ↦ Fin (n + 1)) where
  stripe pq := pq.1 + pq.2
  pred n i := match i with
    | 0 => ⊥
    | ⟨j + 1, _⟩ => WithBot.some ⟨j, by omega⟩
  pred_lt n i := by obtain ⟨_ | _, _⟩ := i <;> aesop
  position n i := ⟨n - i.val, i.val⟩
  discrete := by rintro n ⟨_ | _, _⟩ ⟨_, _⟩ _ <;> aesop
  finite_icc' n i j hij := Set.toFinite _

variable {ι}

namespace ConvergenceStripes

variable (s : ConvergenceStripes ι α)

attribute [simp] stripe_position

lemma stripe_eq (n : σ) (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    s.stripe pq = n := by
  simp [← hpq]

include s in
lemma finite_icc (n : σ) (i j : α n) : (Set.Icc i j).Finite := by
  by_cases hij : i ≤ j
  · exact s.finite_icc' n i j hij
  · simp [Set.Icc_eq_empty hij]

lemma pred_le (n : σ) (i : α n) : s.pred n i ≤ WithBot.some i :=
  (s.pred_lt n i).le

lemma pred_monotone (n : σ) : Monotone (s.pred n) := by
  intro i j hij
  obtain _ | rfl := hij.lt_or_eq
  · by_contra!
    by_cases hi : ∃ (k : α n), k = s.pred n i
    · obtain ⟨k, hk⟩ := hi
      have hj := s.discrete n j k (by grind)
      have hk' := s.pred_lt n i
      rw [← WithBot.coe_le_coe] at hij hj
      grind
    · rw [← WithBot.ne_bot_iff_exists, ne_eq, not_not] at hi
      simp [hi] at this
  · rfl

end ConvergenceStripes

section

variable (E : SpectralSequence C c r₀) (s : ConvergenceStripes ι α)

structure VeryStronglyConvergesToInDegree (n : σ) (X : C) where
  hasPageInfinityAt (pq : ι) (_ : s.stripe pq = n) : E.HasPageInfinityAt pq
  filtration : Filtration X (WithBot (α n))
  exists_isZero : ∃ (j : α n), IsZero (filtration.obj (s.pred n j))
  exists_isIso : ∃ (j : α n), IsIso (filtration.ι.app j)
  π (i : α n) (pq : ι) (hpq : s.position n i = pq) : filtration.obj i ⟶ E.pageInfinity pq
  epi_π (i : α n) (pq : ι) (hpq : s.position n i = pq) : Epi (π i pq hpq)
  comp_π (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) (pq : ι)
      (hpq : s.position n j = pq) :
    filtration.diagram.map (homOfLE (show i ≤ j by simpa [hij] using s.pred_le n j)) ≫
      (π j pq hpq) = 0
  exact_π (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) (pq : ι)
      (hpq : s.position n j = pq) :
    (ShortComplex.mk _ _ (comp_π i j hij pq hpq)).Exact

abbrev VeryStronglyConvergesTo (X : σ → C) :=
  ∀ (n : σ), E.VeryStronglyConvergesToInDegree s n (X n)

namespace VeryStronglyConvergesToInDegree

variable {E s} {n : σ} {X : C}
  (h : E.VeryStronglyConvergesToInDegree s n X)

abbrev filteredObject : FilteredObject C (WithBot (α n)) where
  X := X
  filtration := h.filtration

end VeryStronglyConvergesToInDegree

end

namespace VeryStronglyConvergesToInDegree

variable {E E' E'' : SpectralSequence C c r₀} {s : ConvergenceStripes ι α} {n : σ}
  {X X' X'' : C} {h : E.VeryStronglyConvergesToInDegree s n X}
  {h' : E'.VeryStronglyConvergesToInDegree s n X'}
  {h'' : E''.VeryStronglyConvergesToInDegree s n X''}
  {f : E ⟶ E'}

variable (h h' f) in
structure Hom where
  hom : h.filteredObject ⟶ h'.filteredObject
  commπ (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    dsimp% h.π i pq hpq ≫ f.mapPageInfinity pq =
      hom.natTrans.app i ≫ h'.π i pq hpq := by cat_disch

namespace Hom

attribute [reassoc] commπ

@[simps]
def ofEq (φ : Hom h h' f) (g : E ⟶ E') (hg : f = g) : Hom h h' g where
  hom := φ.hom
  commπ i pq hpq := by simp [← hg, φ.commπ]

@[simps]
noncomputable def id : Hom h h (𝟙 E) where
  hom := 𝟙 _

def comp {g : E' ⟶ E''} (φ : Hom h h' f) (ψ : Hom h' h'' g) :
    Hom h h'' (f ≫ g) where
  hom := φ.hom ≫ ψ.hom
  commπ i pq hpq := by
    have := h'.hasPageInfinityAt pq (by simp [← hpq])
    simp [φ.commπ_assoc i, ψ.commπ]

variable (φ : Hom h h' f)

lemma isIso_hom_hom_of_isIso_natTrans (hφ : IsIso φ.hom.natTrans := by infer_instance) :
    IsIso φ.hom.hom := by
  obtain ⟨j, _⟩ := h.exists_isIso
  obtain ⟨j', _⟩ := h'.exists_isIso
  have : Mono φ.hom.hom := by
    rw [← mono_comp_iff_of_isIso (h.filtration.ι.app j), ← φ.hom.comm j]
    infer_instance
  have := epi_of_epi_fac (φ.hom.comm j').symm
  apply Balanced.isIso_of_mono_of_epi

variable (hφ : ∀ (pq : ι), s.stripe pq = n → IsIso (f.mapPageInfinity pq))

lemma isIso_natTrans_of_isIso_mapPageInfinity :
    IsIso φ.hom := by
  sorry

end Hom

end VeryStronglyConvergesToInDegree

end SpectralSequence

end CategoryTheory
