/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! The homotopy cofiber of a morphism of homological complexes

In this file, we construct the homotopy cofiber of a morphism `φ : F ⟶ G`
between homological complexes in `HomologicalComplex C c`. In degree `i`,
it is isomorphic to `(F.X j) ⊞ (G.X i)` if there is a `j` such that `c.Rel i j`,
and `G.X i` otherwise. (This is also known as the mapping cone of `φ`. Under
the name `CochainComplex.mappingCone`, a specific API shall be developed
for the case of cochain complexes indexed by `ℤ`.)

When we assume `hc : ∀ j, ∃ i, c.Rel i j` (which holds in the case of chain complexes,
or cochain complexes indexed by `ℤ`), then for any homological complex `K`,
there is a bijection `HomologicalComplex.homotopyCofiber.descEquiv φ K hc`
between `homotopyCofiber φ ⟶ K` and the tuples `(α, hα)` with
`α : G ⟶ K` and `hα : Homotopy (φ ≫ α) 0`.

We shall also study the cylinder of a homological complex `K`: this is the
homotopy cofiber of the morphism  `biprod.lift (𝟙 K) (-𝟙 K) : K ⟶ K ⊞ K`.
Then, a morphism `K.cylinder ⟶ M` is determined by the data of two
morphisms `φ₀ φ₁ : K ⟶ M` and a homotopy `h : Homotopy φ₀ φ₁`,
see `cylinder.desc`. There is also a homotopy equivalence
`cylinder.homotopyEquiv K : HomotopyEquiv K.cylinder K`. From the construction of
the cylinder, we deduce the lemma `Homotopy.map_eq_of_inverts_homotopyEquivalences`
which asserts that if a functor inverts homotopy equivalences, then the images of
two homotopic maps are equal.

-/

@[expose] public section


open CategoryTheory Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

/-- A morphism of homological complexes `φ : F ⟶ G` has a homotopy cofiber if for all
indices `i` and `j` such that `c.Rel i j`, the binary biproduct `F.X j ⊞ G.X i` exists. -/
class HasHomotopyCofiber (φ : F ⟶ G) : Prop where
  hasBinaryBiproduct (i j : ι) (hij : c.Rel i j) : HasBinaryBiproduct (F.X j) (G.X i)

instance [HasBinaryBiproducts C] : HasHomotopyCofiber φ where
  hasBinaryBiproduct _ _ _ := inferInstance

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

namespace homotopyCofiber

/-- The `X` field of the homological complex `homotopyCofiber φ`. -/
noncomputable def X (i : ι) : C :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (F.X (c.next i)) ⊞ (G.X i)
  else G.X i

/-- The canonical isomorphism `(homotopyCofiber φ).X i ≅ F.X j ⊞ G.X i` when `c.Rel i j`. -/
noncomputable def XIsoBiprod (i j : ι) (hij : c.Rel i j) [HasBinaryBiproduct (F.X j) (G.X i)] :
    X φ i ≅ F.X j ⊞ G.X i :=
  eqToIso (by
    obtain rfl := c.next_eq' hij
    apply dif_pos hij)

/-- The canonical isomorphism `(homotopyCofiber φ).X i ≅ G.X i` when `¬ c.Rel i (c.next i)`. -/
noncomputable def XIso (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    X φ i ≅ G.X i :=
  eqToIso (dif_neg hi)

/-- The second projection `(homotopyCofiber φ).X i ⟶ G.X i`. -/
noncomputable def sndX (i : ι) : X φ i ⟶ G.X i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (XIsoBiprod φ _ _ hi).hom ≫ biprod.snd
  else
    (XIso φ i hi).hom

/-- The right inclusion `G.X i ⟶ (homotopyCofiber φ).X i`. -/
noncomputable def inrX (i : ι) : G.X i ⟶ X φ i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    biprod.inr ≫ (XIsoBiprod φ _ _ hi).inv
  else
    (XIso φ i hi).inv

@[reassoc (attr := simp)]
lemma inrX_sndX (i : ι) : inrX φ i ≫ sndX φ i = 𝟙 _ := by
  dsimp [sndX, inrX]
  split_ifs with hi <;> simp

@[reassoc]
lemma sndX_inrX (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    sndX φ i ≫ inrX φ i = 𝟙 _ := by
  dsimp [sndX, inrX]
  simp only [dif_neg hi, Iso.hom_inv_id]

/-- The first projection `(homotopyCofiber φ).X i ⟶ F.X j` when `c.Rel i j`. -/
noncomputable def fstX (i j : ι) (hij : c.Rel i j) : X φ i ⟶ F.X j :=
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  (XIsoBiprod φ i j hij).hom ≫ biprod.fst

/-- The left inclusion `F.X i ⟶ (homotopyCofiber φ).X j` when `c.Rel j i`. -/
noncomputable def inlX (i j : ι) (hij : c.Rel j i) : F.X i ⟶ X φ j :=
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  biprod.inl ≫ (XIsoBiprod φ j i hij).inv

@[reassoc (attr := simp)]
lemma inlX_fstX (i j : ι) (hij : c.Rel j i) :
    inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _ := by
  simp [inlX, fstX]

@[reassoc (attr := simp)]
lemma inlX_sndX (i j : ι) (hij : c.Rel j i) :
    inlX φ i j hij ≫ sndX φ j = 0 := by
  obtain rfl := c.next_eq' hij
  simp [inlX, sndX, dif_pos hij]

@[reassoc (attr := simp)]
lemma inrX_fstX (i j : ι) (hij : c.Rel i j) :
    inrX φ i ≫ fstX φ i j hij = 0 := by
  obtain rfl := c.next_eq' hij
  simp [inrX, fstX, dif_pos hij]

/-- The `d` field of the homological complex `homotopyCofiber φ`. -/
noncomputable def d (i j : ι) : X φ i ⟶ X φ j :=
  if hij : c.Rel i j
  then
    (if hj : c.Rel j (c.next j) then -fstX φ i j hij ≫ F.d _ _ ≫ inlX φ _ _ hj else 0) +
      fstX φ i j hij ≫ φ.f j ≫ inrX φ j + sndX φ i ≫ G.d i j ≫ inrX φ j
  else
    0

lemma ext_to_X (i j : ι) (hij : c.Rel i j) {A : C} {f g : A ⟶ X φ i}
    (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hij) (h₂ : f ≫ sndX φ i = g ≫ sndX φ i) :
    f = g := by
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_mono (XIsoBiprod φ i j hij).hom]
  apply biprod.hom_ext
  · simpa using h₁
  · obtain rfl := c.next_eq' hij
    simpa [sndX, dif_pos hij] using h₂

lemma ext_to_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i}
    (h : f ≫ sndX φ i = g ≫ sndX φ i) : f = g := by
  rw [← cancel_mono (XIso φ i hi).hom]
  simpa only [sndX, dif_neg hi] using h

lemma ext_from_X (i j : ι) (hij : c.Rel j i) {A : C} {f g : X φ j ⟶ A}
    (h₁ : inlX φ i j hij ≫ f = inlX φ i j hij ≫ g) (h₂ : inrX φ j ≫ f = inrX φ j ≫ g) :
    f = g := by
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_epi (XIsoBiprod φ j i hij).inv]
  apply biprod.hom_ext'
  · simpa [inlX] using h₁
  · obtain rfl := c.next_eq' hij
    simpa [inrX, dif_pos hij] using h₂

lemma ext_from_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : X φ i ⟶ A}
    (h : inrX φ i ≫ f = inrX φ i ≫ g) : f = g := by
  rw [← cancel_epi (XIso φ i hi).inv]
  simpa only [inrX, dif_neg hi] using h

@[reassoc]
lemma d_fstX (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    d φ i j ≫ fstX φ j k hjk = -fstX φ i j hij ≫ F.d j k := by
  obtain rfl := c.next_eq' hjk
  simp [d, dif_pos hij, dif_pos hjk]

@[reassoc]
lemma d_sndX (i j : ι) (hij : c.Rel i j) :
    d φ i j ≫ sndX φ j = fstX φ i j hij ≫ φ.f j + sndX φ i ≫ G.d i j := by
  dsimp [d]
  split_ifs with hij <;> simp

@[reassoc]
lemma inlX_d (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    inlX φ j i hij ≫ d φ i j = -F.d j k ≫ inlX φ k j hjk + φ.f j ≫ inrX φ j := by
  apply ext_to_X φ j k hjk
  · simp [d_fstX φ _ _ _ hij hjk]
  · simp [d_sndX φ _ _ hij]

@[reassoc]
lemma inlX_d' (i j : ι) (hij : c.Rel i j) (hj : ¬ c.Rel j (c.next j)) :
    inlX φ j i hij ≫ d φ i j = φ.f j ≫ inrX φ j := by
  apply ext_to_X' _ _ hj
  simp [d_sndX φ i j hij]

lemma shape (i j : ι) (hij : ¬ c.Rel i j) :
    d φ i j = 0 :=
  dif_neg hij

@[reassoc (attr := simp)]
lemma inrX_d (i j : ι) :
    inrX φ i ≫ d φ i j = G.d i j ≫ inrX φ j := by
  by_cases hij : c.Rel i j
  · by_cases hj : c.Rel j (c.next j)
    · apply ext_to_X _ _ _ hj
      · simp [d_fstX φ _ _ _ hij]
      · simp [d_sndX φ _ _ hij]
    · apply ext_to_X' _ _ hj
      simp [d_sndX φ _ _ hij]
  · rw [shape φ _ _ hij, G.shape _ _ hij, zero_comp, comp_zero]

end homotopyCofiber

/-- The homotopy cofiber of a morphism of homological complexes,
also known as the mapping cone. -/
@[simps]
noncomputable def homotopyCofiber : HomologicalComplex C c where
  X i := homotopyCofiber.X φ i
  d i j := homotopyCofiber.d φ i j
  shape i j hij := homotopyCofiber.shape φ i j hij
  d_comp_d' i j k hij hjk := by
    apply homotopyCofiber.ext_from_X φ j i hij
    · dsimp
      simp only [comp_zero, homotopyCofiber.inlX_d_assoc φ i j k hij hjk,
        add_comp, assoc, homotopyCofiber.inrX_d, Hom.comm_assoc, neg_comp]
      by_cases hk : c.Rel k (c.next k)
      · simp [homotopyCofiber.inlX_d φ j k _ hjk hk]
      · simp [homotopyCofiber.inlX_d' φ j k hjk hk]
    · simp

namespace homotopyCofiber

/-- The right inclusion `G ⟶ homotopyCofiber φ`. -/
@[simps!]
noncomputable def inr : G ⟶ homotopyCofiber φ where
  f i := inrX φ i

section

set_option backward.isDefEq.respectTransparency false in
/-- The composition `φ ≫ mappingCone.inr φ` is homotopic to `0`. -/
noncomputable def inrCompHomotopy (hc : ∀ j, ∃ i, c.Rel i j) :
    Homotopy (φ ≫ inr φ) 0 where
  hom i j :=
    if hij : c.Rel j i then inlX φ i j hij else 0
  zero _ _ hij := dif_neg hij
  comm j := by
    obtain ⟨i, hij⟩ := hc j
    rw [prevD_eq _ hij, dif_pos hij]
    by_cases hj : c.Rel j (c.next j)
    · simp only [comp_f, homotopyCofiber_d, zero_f, add_zero,
        inlX_d φ i j _ hij hj, dNext_eq _ hj, dif_pos hj,
        add_neg_cancel_left, inr_f]
    · rw [dNext_eq_zero _ _ hj, zero_add, zero_f, add_zero, homotopyCofiber_d,
        inlX_d' _ _ _ _ hj, comp_f, inr_f]

variable (hc : ∀ j, ∃ i, c.Rel i j)

lemma inrCompHomotopy_hom (i j : ι) (hij : c.Rel j i) :
    (inrCompHomotopy φ hc).hom i j = inlX φ i j hij := dif_pos hij

lemma inrCompHomotopy_hom_eq_zero (i j : ι) (hij : ¬ c.Rel j i) :
    (inrCompHomotopy φ hc).hom i j = 0 := dif_neg hij

end

section

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

/-- The morphism `homotopyCofiber φ ⟶ K` that is induced by a morphism `α : G ⟶ K`
and a homotopy `hα : Homotopy (φ ≫ α) 0`. -/
noncomputable def desc :
    homotopyCofiber φ ⟶ K where
  f j :=
    if hj : c.Rel j (c.next j)
    then fstX φ j _ hj ≫ hα.hom _ j + sndX φ j ≫ α.f j
    else sndX φ j ≫ α.f j
  comm' j k hjk := by
    obtain rfl := c.next_eq' hjk
    simp [dif_pos hjk]
    have H := hα.comm (c.next j)
    simp only [comp_f, zero_f, add_zero, prevD_eq _ hjk] at H
    split_ifs with hj
    · simp only [comp_add, d_sndX_assoc _ _ _ hjk, add_comp, assoc, H,
        d_fstX_assoc _ _ _ _ hjk, neg_comp, dNext, AddMonoidHom.mk'_apply]
      abel
    · simp only [d_sndX_assoc _ _ _ hjk, add_comp, assoc, H, dNext_eq_zero _ _ hj, zero_add]

lemma desc_f (j k : ι) (hjk : c.Rel j k) :
    (desc φ α hα).f j = fstX φ j _ hjk ≫ hα.hom _ j + sndX φ j ≫ α.f j := by
  obtain rfl := c.next_eq' hjk
  apply dif_pos hjk

lemma desc_f' (j : ι) (hj : ¬ c.Rel j (c.next j)) :
    (desc φ α hα).f j = sndX φ j ≫ α.f j := by
  apply dif_neg hj

@[reassoc (attr := simp)]
lemma inlX_desc_f (i j : ι) (hjk : c.Rel j i) :
    inlX φ i j hjk ≫ (desc φ α hα).f j = hα.hom i j := by
  obtain rfl := c.next_eq' hjk
  dsimp [desc]
  rw [dif_pos hjk, comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]

@[reassoc (attr := simp)]
lemma inrX_desc_f (i : ι) :
    inrX φ i ≫ (desc φ α hα).f i = α.f i := by
  dsimp [desc]
  split_ifs <;> simp

@[reassoc (attr := simp)]
lemma inr_desc :
    inr φ ≫ desc φ α hα = α := by cat_disch

@[reassoc (attr := simp)]
lemma inrCompHomotopy_hom_desc_hom (hc : ∀ j, ∃ i, c.Rel i j) (i j : ι) :
    (inrCompHomotopy φ hc).hom i j ≫ (desc φ α hα).f j = hα.hom i j := by
  by_cases hij : c.Rel j i
  · dsimp
    simp only [inrCompHomotopy_hom φ hc i j hij, desc_f φ α hα _ _ hij,
      comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]
  · simp only [Homotopy.zero _ _ _ hij, zero_comp]

lemma eq_desc (f : homotopyCofiber φ ⟶ K) (hc : ∀ j, ∃ i, c.Rel i j) :
    f = desc φ (inr φ ≫ f) (Homotopy.trans (Homotopy.ofEq (by simp))
      (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))) := by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ _ _ hj
    · simp [inrCompHomotopy_hom _ _ _ _ hj]
    · simp
  · apply ext_from_X' φ _ hj
    simp

end

omit [DecidableRel c.Rel] in
lemma descSigma_ext_iff {φ : F ⟶ G} {K : HomologicalComplex C c}
    (x y : Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) :
    x = y ↔ x.1 = y.1 ∧ (∀ (i j : ι) (_ : c.Rel j i), x.2.hom i j = y.2.hom i j) := by
  constructor
  · rintro rfl
    tauto
  · obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    rintro ⟨rfl, h⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    ext i j
    by_cases hij : c.Rel j i
    · exact h _ _ hij
    · simp only [Homotopy.zero _ _ _ hij]

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms `homotopyCofiber φ ⟶ K` are uniquely determined by
a morphism `α : G ⟶ K` and a homotopy from `φ ≫ α` to `0`. -/
noncomputable def descEquiv (K : HomologicalComplex C c) (hc : ∀ j, ∃ i, c.Rel i j) :
    (Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) ≃ (homotopyCofiber φ ⟶ K) where
  toFun := fun ⟨α, hα⟩ => desc φ α hα
  invFun f := ⟨inr φ ≫ f, Homotopy.trans (Homotopy.ofEq (by simp))
    (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))⟩
  right_inv f := (eq_desc φ f hc).symm
  left_inv := fun ⟨α, hα⟩ => by
    rw [descSigma_ext_iff]
    cat_disch

end homotopyCofiber

section

variable (K)
variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

/-- The cylinder object of a homological complex `K` is the homotopy cofiber
of the morphism  `biprod.lift (𝟙 K) (-𝟙 K) : K ⟶ K ⊞ K`. -/
noncomputable abbrev cylinder := homotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

namespace cylinder

/-- The left inclusion `K ⟶ K.cylinder`. -/
noncomputable def ι₀ : K ⟶ K.cylinder := biprod.inl ≫ homotopyCofiber.inr _

/-- The right inclusion `K ⟶ K.cylinder`. -/
noncomputable def ι₁ : K ⟶ K.cylinder := biprod.inr ≫ homotopyCofiber.inr _

variable {K}

section

variable (φ₀ φ₁ : K ⟶ F) (h : Homotopy φ₀ φ₁)

/-- The morphism `K.cylinder ⟶ F` that is induced by two morphisms `φ₀ φ₁ : K ⟶ F`
and a homotopy `h : Homotopy φ₀ φ₁`. -/
noncomputable def desc : K.cylinder ⟶ F :=
  homotopyCofiber.desc _ (biprod.desc φ₀ φ₁)
    (Homotopy.trans (Homotopy.ofEq (by
      simp only [biprod.lift_desc, id_comp, neg_comp, sub_eq_add_neg]))
      ((Homotopy.equivSubZero h)))

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ K ≫ desc φ₀ φ₁ h = φ₀ := by simp [ι₀, desc]

@[reassoc (attr := simp)]
lemma ι₁_desc : ι₁ K ≫ desc φ₀ φ₁ h = φ₁ := by simp [ι₁, desc]

end

variable (K)

/-- The projection `π : K.cylinder ⟶ K`. -/
noncomputable def π : K.cylinder ⟶ K := desc (𝟙 K) (𝟙 K) (Homotopy.refl _)

@[reassoc (attr := simp)]
lemma ι₀_π : ι₀ K ≫ π K = 𝟙 K := by simp [π]

@[reassoc (attr := simp)]
lemma ι₁_π : ι₁ K ≫ π K = 𝟙 K := by simp [π]

/-- The left inclusion `K.X i ⟶ K.cylinder.X j` when `c.Rel j i`. -/
noncomputable abbrev inlX (i j : ι) (hij : c.Rel j i) : K.X i ⟶ K.cylinder.X j :=
  homotopyCofiber.inlX (biprod.lift (𝟙 K) (-𝟙 K)) i j hij

/-- The right inclusion `(K ⊞ K).X i ⟶ K.cylinder.X i`. -/
noncomputable abbrev inrX (i : ι) : (K ⊞ K).X i ⟶ K.cylinder.X i :=
  homotopyCofiber.inrX (biprod.lift (𝟙 K) (-𝟙 K)) i

@[reassoc (attr := simp)]
lemma inlX_π (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (π K).f j = 0 := by
  simp [HomologicalComplex.cylinder.π, HomologicalComplex.cylinder.desc, Homotopy.equivSubZero]

@[reassoc (attr := simp)]
lemma inrX_π (i : ι) :
    inrX K i ≫ (π K).f i = (biprod.desc (𝟙 _) (𝟙 K)).f i :=
  homotopyCofiber.inrX_desc_f _ _ _ _

section

variable (hc : ∀ j, ∃ i, c.Rel i j)

namespace πCompι₀Homotopy

/-- A null homotopic map `K.cylinder ⟶ K.cylinder` which identifies to
`π K ≫ ι₀ K - 𝟙 _`, see `nullHomotopicMap_eq`. -/
noncomputable def nullHomotopicMap : K.cylinder ⟶ K.cylinder :=
  Homotopy.nullHomotopicMap'
    (fun i j hij => homotopyCofiber.sndX (biprod.lift (𝟙 K) (-𝟙 K)) i ≫
      (biprod.snd : K ⊞ K ⟶ K).f i ≫ inlX K i j hij)

/-- The obvious homotopy from `nullHomotopicMap K` to zero. -/
noncomputable def nullHomotopy : Homotopy (nullHomotopicMap K) 0 :=
  Homotopy.nullHomotopy' _

set_option backward.isDefEq.respectTransparency false in
lemma inlX_nullHomotopy_f (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (nullHomotopicMap K).f j =
      inlX K i j hij ≫ (π K ≫ ι₀ K - 𝟙 _).f j := by
  dsimp [nullHomotopicMap]
  by_cases! hj : ∃ (k : ι), c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f hjk hij, homotopyCofiber_X, homotopyCofiber_d,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc, zero_comp, add_zero, comp_sub, inlX_π_assoc, comp_id,
      zero_sub, ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f,
      neg_comp, id_comp]
  · simp only [Homotopy.nullHomotopicMap'_f_of_not_rel_right hij hj,
      homotopyCofiber_X, homotopyCofiber_d, assoc, comp_sub, comp_id,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, zero_comp, add_zero,
      homotopyCofiber.inlX_fstX_assoc, homotopyCofiber.inlX_sndX_assoc,
      ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f, neg_comp,
      id_comp, inlX_π_assoc, zero_sub]

include hc

set_option backward.isDefEq.respectTransparency false in
lemma inrX_nullHomotopy_f (j : ι) :
    inrX K j ≫ (nullHomotopicMap K).f j = inrX K j ≫ (π K ≫ ι₀ K - 𝟙 _).f j := by
  have : biprod.lift (𝟙 K) (-𝟙 K) = biprod.inl - biprod.inr :=
    biprod.hom_ext _ _ (by simp) (by simp)
  obtain ⟨i, hij⟩ := hc j
  dsimp [nullHomotopicMap]
  by_cases hj : ∃ (k : ι), c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Homotopy.nullHomotopicMap'_f hij hjk,
      homotopyCofiber_X, homotopyCofiber_d, assoc, comp_add,
      homotopyCofiber.inrX_d_assoc, homotopyCofiber.inrX_sndX_assoc, comp_sub,
      inrX_π_assoc, comp_id, ← Hom.comm_assoc, homotopyCofiber.inlX_d _ _ _ _ _ hjk,
      comp_neg, add_neg_cancel_left]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp [ι₀]
    · dsimp
      simp only [inr_biprodXIso_inv_assoc, biprod_inr_snd_f_assoc, comp_sub,
        biprod_inr_desc_f_assoc, id_f, id_comp, ι₀, comp_f, this,
        sub_f_apply, sub_comp, homotopyCofiber_X, homotopyCofiber.inr_f]
  · simp only [not_exists] at hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f_of_not_rel_left hij hj, homotopyCofiber_X,
      homotopyCofiber_d, homotopyCofiber.inlX_d' _ _ _ _ (hj _), homotopyCofiber.inrX_sndX_assoc,
      comp_sub, inrX_π_assoc, comp_id, ι₀, comp_f, homotopyCofiber.inr_f]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp
    · simp [this]

lemma nullHomotopicMap_eq : nullHomotopicMap K = π K ≫ ι₀ K - 𝟙 _ := by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact homotopyCofiber.ext_from_X (biprod.lift (𝟙 K) (-𝟙 K)) (c.next i) i hi
      (inlX_nullHomotopy_f _ _ _ _) (inrX_nullHomotopy_f _ hc _)
  · exact homotopyCofiber.ext_from_X' (biprod.lift (𝟙 K) (-𝟙 K)) _ hi (inrX_nullHomotopy_f _ hc _)

end πCompι₀Homotopy

/-- The homotopy between `π K ≫ ι₀ K` and `𝟙 K.cylinder`. -/
noncomputable def πCompι₀Homotopy : Homotopy (π K ≫ ι₀ K) (𝟙 K.cylinder) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (πCompι₀Homotopy.nullHomotopicMap_eq K hc).symm).trans
      (πCompι₀Homotopy.nullHomotopy K))

/-- The homotopy equivalence between `K.cylinder` and `K`. -/
noncomputable def homotopyEquiv : HomotopyEquiv K.cylinder K where
  hom := π K
  inv := ι₀ K
  homotopyHomInvId := πCompι₀Homotopy K hc
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- The homotopy between `cylinder.ι₀ K` and `cylinder.ι₁ K`. -/
noncomputable def homotopy₀₁ : Homotopy (ι₀ K) (ι₁ K) :=
  (Homotopy.ofEq (by simp)).trans (((πCompι₀Homotopy K hc).compLeft (ι₁ K)).trans
    (Homotopy.ofEq (by simp)))

include hc in
lemma map_ι₀_eq_map_ι₁ {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map (ι₀ K) = H.map (ι₁ K) := by
  have : IsIso (H.map (cylinder.π K)) := hH _ ⟨homotopyEquiv K hc, rfl⟩
  simp only [← cancel_mono (H.map (cylinder.π K)), ← H.map_comp, ι₀_π, H.map_id, ι₁_π]

end

end cylinder

omit [DecidableRel c.Rel] in
/-- If a functor inverts homotopy equivalences, it sends homotopic maps to the same map. -/
lemma _root_.Homotopy.map_eq_of_inverts_homotopyEquivalences
    {φ₀ φ₁ : F ⟶ G} (h : Homotopy φ₀ φ₁) (hc : ∀ j, ∃ i, c.Rel i j)
    [∀ i, HasBinaryBiproduct (F.X i) (F.X i)]
    [HasHomotopyCofiber (biprod.lift (𝟙 F) (-𝟙 F))]
    {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map φ₀ = H.map φ₁ := by
  classical
  simp only [← cylinder.ι₀_desc _ _ h, ← cylinder.ι₁_desc _ _ h, H.map_comp,
    cylinder.map_ι₀_eq_map_ι₁ _ hc _ hH]

end

end HomologicalComplex
