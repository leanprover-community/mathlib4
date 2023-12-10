/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! The mapping cone

In this file, we construct the mapping cone `mappingCone φ` of a morphism
`φ : F ⟶ G` between cochain complexes. The definition makes sense for
cochain complexes indexed by any `ι : Type*` with `[AddRightCancelSemigroup ι]`
and `[One ι]`.

In case of cochain complexes indexed by `ℤ`, the mapping cone can be studied
using the complex of homomorphisms `HomComplex`: we introduce definitions
`inl φ : Cochain F (mappingCone φ) (-1)`, `inr φ : G ⟶ mappingCone φ`,
`fst φ : Cocycle (mappingCone φ) F 1` and `snd φ : Cochain (mappingCone φ) G 0`.

-/

open CategoryTheory Category Limits

variable {C : Type*} [Category C] [Preadditive C]

namespace CochainComplex

section

variable {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
  {F G : CochainComplex C ι} (φ : F ⟶ G)

/-- A morphism `φ : F ⟶ G` has a mapping cone when the binary biproducts
`F.X (p + 1)) ⊞ (G.X p` exist. -/
@[nolint unusedArguments]
abbrev HasMappingCone (_ : F ⟶ G) := ∀ p, HasBinaryBiproduct (F.X (p + 1)) (G.X p)

variable [HasMappingCone φ] [DecidableEq ι]

/-- The mapping cone of a morphism `φ : F ⟶ G`. In degree `i`, it consists
of `F.X (i + 1) ⊞ G.X i`. -/
noncomputable def mappingCone : CochainComplex C ι where
  X i := F.X (i + 1) ⊞ G.X i
  d i j :=
    if h : i + 1 = j
      then -biprod.fst ≫ F.d _ _ ≫ biprod.inl +
        biprod.fst ≫ eqToHom (by rw [h]) ≫ φ.f j ≫ biprod.inr +
        biprod.snd ≫ G.d _ _ ≫ biprod.inr
      else 0
  shape i j (hij : i + 1 ≠ j) := dif_neg hij
  d_comp_d' := by rintro i _ _ rfl rfl; simp

namespace mappingCone

@[simp]
lemma isZero_X_iff (i : ι) :
    IsZero ((mappingCone φ).X i) ↔ IsZero (F.X (i + 1)) ∧ IsZero (G.X i) := by
  apply biprod_isZero_iff

/-- The left injection `F.X i ⟶ (mappingCone φ).X j` when `j + 1 = i`. -/
noncomputable def inlX (i j : ι) (h : j + 1 = i) : F.X i ⟶ (mappingCone φ).X j :=
  eqToHom (by rw [h]) ≫ biprod.inl

/-- The right injection `G.X i ⟶ (mappingCone φ).X i`. -/
noncomputable def inrX (i : ι) : G.X i ⟶ (mappingCone φ).X i := biprod.inr

/-- The first projection `(mappingCone φ).X i ⟶ F.X j` when `i + 1 = j`. -/
noncomputable def fstX (i j : ι) (h : i + 1 = j) : (mappingCone φ).X i ⟶ F.X j :=
  biprod.fst ≫ eqToHom (by rw [h])

/-- The second projection `(mappingCone φ).X i ⟶ G.X i`. -/
noncomputable def sndX (i : ι) : (mappingCone φ).X i ⟶ G.X i := biprod.snd

@[reassoc (attr := simp)]
lemma inlX_fstX (i j : ι) (h : j + 1 = i) :
    inlX φ i j h ≫ fstX φ j i h = 𝟙 _ := by
  subst h
  simp [inlX, fstX]

@[reassoc (attr := simp)]
lemma inlX_sndX (i j : ι) (h : j + 1 = i) :
    inlX φ i j h ≫ sndX φ j = 0 := by
  subst h
  simp [inlX, sndX]

@[reassoc (attr := simp)]
lemma inrX_fstX (i j : ι) (h : i + 1 = j) :
    inrX φ i ≫ fstX φ i j h = 0 := by
  subst h
  simp [inrX, fstX]

@[reassoc (attr := simp)]
lemma inrX_sndX (i : ι) :
    inrX φ i ≫ sndX φ i = 𝟙 _ := by
  simp [inrX, sndX]

@[reassoc]
lemma inlX_d (i j k : ι) (h : j + 1 = i) (h' : i + 1 = k) :
    inlX φ i j h ≫ (mappingCone φ).d j i = -F.d i k ≫ inlX φ k i h' + φ.f i ≫ inrX φ i := by
  subst h h'
  simp [inlX, inrX, mappingCone]

@[reassoc]
lemma inrX_d (i j : ι) (h : i + 1 = j) :
    inrX φ i ≫ (mappingCone φ).d i j = G.d i j ≫ inrX φ j := by
  subst h
  simp [inrX, mappingCone]

lemma id_X (i j : ι) (h : i + 1 = j) :
    𝟙 ((mappingCone φ).X i) = fstX φ i j h ≫ inlX φ j i h + sndX φ i ≫ inrX φ i := by
  subst h
  simp only [fstX, eqToHom_refl, comp_id, inlX, id_comp, sndX, inrX]
  symm
  apply biprod.total

lemma extX (i j : ι) (h : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X i}
    (h₁ : f ≫ fstX φ i j h = g ≫ fstX φ i j h) (h₂ : f ≫ sndX φ i = g ≫ sndX φ i) :
    f = g := by
  subst h
  apply biprod.hom_ext
  · simpa [fstX] using h₁
  · simpa using h₂

lemma extX' (i j : ι) (h : j + 1 = i) {A : C} {f g : (mappingCone φ).X j ⟶ A}
    (h₁ : inlX φ i j h ≫ f = inlX φ i j h ≫ g) (h₂ : inrX φ j ≫ f = inrX φ j ≫ g) :
    f = g := by
  subst h
  apply biprod.hom_ext'
  · simpa [inlX] using h₁
  · simpa using h₂

attribute [irreducible] mappingCone inlX inrX fstX sndX

/-- The bilimit binary bicone expressing that `(mappingCone φ).X i` identifies to the binary
biproduct of `F.X j` and `G.X i` when `i + 1 = j`. -/
@[simps]
noncomputable def binaryBicone (i j : ι) (h : i + 1 = j) : BinaryBicone (F.X j) (G.X i) where
  pt := (mappingCone φ).X i
  fst := fstX φ i j h
  snd := sndX φ i
  inl := inlX φ j i h
  inr := inrX φ i

/-- `(mappingCone φ).X i` identifies to the binary biproduct of
`F.X j` and `G.X i` when `i + 1 = j`. -/
noncomputable def binaryBiconeIsBilimit (i j : ι) (h : i + 1 = j) :
    (binaryBicone φ i j h).IsBilimit :=
  isBinaryBilimitOfTotal _ (by simp [id_X φ i j h])

/-- The right injection `G ⟶ mappingCone φ`. -/
@[simps]
noncomputable def inr : G ⟶ mappingCone φ where
  f i := inrX φ i
  comm' i j hij := inrX_d φ i j hij

end mappingCone

end

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) [HasMappingCone φ]

open HomComplex

namespace mappingCone

/-- The left injection, as a cochain in `Cochain F (mappingCone φ) (-1)`. -/
noncomputable def inl : Cochain F (mappingCone φ) (-1) :=
  Cochain.mk (fun p q hpq => inlX φ p q  (by linarith))

@[simp]
lemma inl_v (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq = inlX φ p q (by linarith) := rfl

/-- The first projection, as a cocycle in `Cocycle (mappingCone φ) F 1`. -/
noncomputable def fst : Cocycle (mappingCone φ) F 1 :=
  Cocycle.mk (Cochain.mk (fstX φ)) 2 (by linarith) (by
    ext p _ rfl
    rw [δ_v 1 2 (by linarith) _ p (p + 2) rfl (p + 1) (p + 1) (by linarith) rfl]
    apply extX' _ _ _ rfl
    · simp [inlX_d_assoc φ (p + 1) p (p + 2) rfl (by linarith),
        show Int.negOnePow 2 = 1 from rfl]
    · simp [inrX_d_assoc φ p (p + 1) rfl])

@[simp]
lemma fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (fst φ).1.v p q hpq = fstX φ p q hpq := rfl

/-- The second projection, as a cochain in `Cochain (mappingCone φ) G 0`. -/
noncomputable def snd : Cochain (mappingCone φ) G 0 :=
  Cochain.ofHoms (sndX φ)

lemma snd_v (i : ℤ) : (snd φ).v i i (add_zero i) = sndX φ i := by
  simp only [snd, Cochain.ofHoms_v]

end mappingCone

end CochainComplex
