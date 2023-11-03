import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.ComposableArrows

namespace CategoryTheory

open Limits

namespace ComposableArrows

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ}
  (S : ComposableArrows C n)

structure IsComplex : Prop where
  zero (i : ℕ) (hi : i + 2 ≤ n) :
    S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

variable {S}

lemma IsComplex.zero' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    S.map' i j ≫ S.map' j k = 0 := by
  subst hij hjk
  exact hS.zero i hk

lemma isComplex_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) :
    S₂.IsComplex where
  zero i hi := by
    rw [← cancel_epi (ComposableArrows.app' e.hom i), comp_zero,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality,
      reassoc_of% (h₁.zero i hi), zero_comp]

lemma isComplex_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.IsComplex ↔ S₂.IsComplex :=
  ⟨isComplex_of_iso e, isComplex_of_iso e.symm⟩

lemma isComplex₀ (S : ComposableArrows C 0) : S.IsComplex where
  zero i hi := by simp at hi

lemma isComplex₁ (S : ComposableArrows C 1) : S.IsComplex where
  zero i hi := by exfalso; linarith

variable (S)

@[simps!]
def sc' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    ShortComplex C :=
  ShortComplex.mk (S.map' i j) (S.map' j k) (hS.zero' i j k)

abbrev sc (hS : S.IsComplex) (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    ShortComplex C :=
    S.sc' hS i (i + 1) (i + 2)

structure Exact extends S.IsComplex : Prop where
  exact (i : ℕ) (hi : i + 2 ≤ n) : (S.sc toIsComplex i).Exact

variable {S}

lemma IsExact.exact' (hS : S.Exact) (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    (S.sc' hS.toIsComplex i j k).Exact := by
  subst hij hjk
  exact hS.exact i hk

@[simps]
def sc'Map {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    S₁.sc' h₁ i j k ⟶ S₂.sc' h₂ i j k where
  τ₁ := φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _

@[simps!]
def scMap {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    S₁.sc h₁ i ⟶ S₂.sc h₂ i :=
  sc'Map φ h₁ h₂ i (i + 1) (i + 2)

@[simps]
def sc'MapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    S₁.sc' h₁ i j k ≅ S₂.sc' h₂ i j k where
  hom := sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> dsimp <;> simp
  inv_hom_id := by ext <;> dsimp <;> simp

@[simps]
def scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    S₁.sc h₁ i ≅ S₂.sc h₂ i where
  hom := scMap e.hom h₁ h₂ i
  inv := scMap e.inv h₂ h₁ i
  hom_inv_id := by ext <;> dsimp <;> simp
  inv_hom_id := by ext <;> dsimp <;> simp

lemma exact_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) :
    S₂.Exact where
  toIsComplex := isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (scMapIso e h₁.toIsComplex
    (isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)

lemma exact_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

lemma exact₀ (S : ComposableArrows C 0) : S.Exact where
  toIsComplex := S.isComplex₀
  exact i hi := by simp at hi

lemma exact₁ (S : ComposableArrows C 1) : S.Exact where
  toIsComplex := S.isComplex₁
  exact i hi := by exfalso; linarith

end ComposableArrows

end CategoryTheory
