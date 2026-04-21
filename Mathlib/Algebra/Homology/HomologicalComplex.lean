/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Homological complexes.

A `HomologicalComplex V c` with a "shape" controlled by `c : ComplexShape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.Rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.

We provide `ChainComplex V α` for
`α`-indexed chain complexes in which `d i j ≠ 0` only if `j + 1 = i`,
and similarly `CochainComplex V α`, with `i = j + 1`.

There is a category structure, where morphisms are chain maps.

For `C : HomologicalComplex V c`, we define `C.xNext i`, which is either `C.X j` for some
arbitrarily chosen `j` such that `c.r i j`, or `C.X i` if there is no such `j`.
Similarly we have `C.xPrev j`.
Defined in terms of these we have `C.dFrom i : C.X i ⟶ C.xNext i` and
`C.dTo j : C.xPrev j ⟶ C.X j`, which are either defined as `C.d i j`, or zero, as needed.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι : Type*}
variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

/-- A `HomologicalComplex V c` with a "shape" controlled by `c : ComplexShape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.Rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.
-/
structure HomologicalComplex (c : ComplexShape ι) where
  X : ι → V
  d : ∀ i j, X i ⟶ X j
  shape : ∀ i j, ¬c.Rel i j → d i j = 0 := by cat_disch
  d_comp_d' : ∀ i j k, c.Rel i j → c.Rel j k → d i j ≫ d j k = 0 := by cat_disch

namespace HomologicalComplex

attribute [simp] shape

variable {V} {c : ComplexShape ι}

@[reassoc (attr := simp)]
theorem d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0 := by
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]

theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X)
    (h_d :
      ∀ i j : ι,
        c.Rel i j → C₁.d i j ≫ eqToHom (congr_fun h_X j) = eqToHom (congr_fun h_X i) ≫ C₂.d i j) :
    C₁ = C₂ := by
  obtain ⟨X₁, d₁, s₁, h₁⟩ := C₁
  obtain ⟨X₂, d₂, s₂, h₂⟩ := C₂
  dsimp at h_X
  subst h_X
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext i j
  by_cases hij : c.Rel i j
  · simpa only [comp_id, id_comp, eqToHom_refl] using h_d i j hij
  · rw [s₁ i j hij, s₂ i j hij]

/-- The obvious isomorphism `K.X p ≅ K.X q` when `p = q`. -/
def XIsoOfEq (K : HomologicalComplex V c) {p q : ι} (h : p = q) : K.X p ≅ K.X q :=
  eqToIso (by rw [h])

@[simp]
lemma XIsoOfEq_rfl (K : HomologicalComplex V c) (p : ι) :
    K.XIsoOfEq (rfl : p = p) = Iso.refl _ := rfl

@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₁₂.trans h₂₃)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₁₂.trans h₃₂.symm)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
lemma XIsoOfEq_inv_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₂₁.symm.trans h₂₃)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
lemma XIsoOfEq_inv_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₃₂.trans h₂₁).symm).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_comp_d (K : HomologicalComplex V c) {p₁ p₂ : ι} (h : p₁ = p₂) (p₃ : ι) :
    (K.XIsoOfEq h).hom ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
lemma XIsoOfEq_inv_comp_d (K : HomologicalComplex V c) {p₂ p₁ : ι} (h : p₂ = p₁) (p₃ : ι) :
    (K.XIsoOfEq h).inv ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
lemma d_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₂ = p₃) (p₁ : ι) :
    K.d p₁ p₂ ≫ (K.XIsoOfEq h).hom = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
lemma d_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₃ = p₂) (p₁ : ι) :
    K.d p₁ p₂ ≫ (K.XIsoOfEq h).inv = K.d p₁ p₃ := by subst h; simp

end HomologicalComplex

/-- An `α`-indexed chain complex is a `HomologicalComplex`
in which `d i j ≠ 0` only if `j + 1 = i`.
-/
abbrev ChainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.down α)

/-- An `α`-indexed cochain complex is a `HomologicalComplex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
abbrev CochainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.up α)

namespace ChainComplex

@[simp]
theorem prev (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.down α).prev i = i + 1 :=
  (ComplexShape.down α).prev_eq' rfl

@[simp]
theorem next (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.down α).next i = i - 1 :=
  (ComplexShape.down α).next_eq' <| sub_add_cancel _ _

@[simp]
theorem next_nat_zero : (ComplexShape.down ℕ).next 0 = 0 := by
  classical
    refine dif_neg ?_
    push Not
    intro
    apply Nat.noConfusion

@[simp]
theorem next_nat_succ (i : ℕ) : (ComplexShape.down ℕ).next (i + 1) = i :=
  (ComplexShape.down ℕ).next_eq' rfl

end ChainComplex

namespace CochainComplex

@[simp]
theorem prev (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.up α).prev i = i - 1 :=
  (ComplexShape.up α).prev_eq' <| sub_add_cancel _ _

@[simp]
theorem next (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.up α).next i = i + 1 :=
  (ComplexShape.up α).next_eq' rfl

@[simp]
theorem prev_nat_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  classical
    refine dif_neg ?_
    push Not
    intro
    apply Nat.noConfusion

@[simp]
theorem prev_nat_succ (i : ℕ) : (ComplexShape.up ℕ).prev (i + 1) = i :=
  (ComplexShape.up ℕ).prev_eq' rfl

end CochainComplex

namespace HomologicalComplex

variable {V}
variable {c : ComplexShape ι} (C : HomologicalComplex V c)

/-- A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
@[ext]
structure Hom (A B : HomologicalComplex V c) where
  f : ∀ i, A.X i ⟶ B.X i
  comm' : ∀ i j, c.Rel i j → f i ≫ B.d i j = A.d i j ≫ f j := by cat_disch

@[reassoc (attr := simp)]
theorem Hom.comm {A B : HomologicalComplex V c} (f : A.Hom B) (i j : ι) :
    f.f i ≫ B.d i j = A.d i j ≫ f.f j := by
  by_cases hij : c.Rel i j
  · exact f.comm' i j hij
  · rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]

instance (A B : HomologicalComplex V c) : Inhabited (Hom A B) :=
  ⟨{ f := fun _ => 0 }⟩

/-- Identity chain map. -/
def id (A : HomologicalComplex V c) : Hom A A where f _ := 𝟙 _

/-- Composition of chain maps. -/
def comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A C where
  f i := φ.f i ≫ ψ.f i

section

attribute [local simp] id comp

instance : Category (HomologicalComplex V c) where
  Hom := Hom
  id := id
  comp := comp _ _ _

end

@[ext]
lemma hom_ext {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (h : ∀ i, f.f i = g.f i) : f = g := by
  apply Hom.ext
  funext
  apply h

@[simp]
theorem id_f (C : HomologicalComplex V c) (i : ι) : Hom.f (𝟙 C) i = 𝟙 (C.X i) :=
  rfl

@[simp, reassoc]
theorem comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    (f ≫ g).f i = f.f i ≫ g.f i :=
  rfl

@[simp]
theorem eqToHom_f {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι) :
    HomologicalComplex.Hom.f (eqToHom h) n =
      eqToHom (congr_fun (congr_arg HomologicalComplex.X h) n) := by
  subst h
  rfl

-- We'll use this later to show that `HomologicalComplex V c` is preadditive when `V` is.
theorem hom_f_injective {C₁ C₂ : HomologicalComplex V c} :
    Function.Injective fun f : Hom C₁ C₂ => f.f := by cat_disch

instance (X Y : HomologicalComplex V c) : Zero (X ⟶ Y) :=
  ⟨{ f := fun _ => 0}⟩

@[simp]
theorem zero_f (C D : HomologicalComplex V c) (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

instance : HasZeroMorphisms (HomologicalComplex V c) where

open ZeroObject

/-- The zero complex -/
noncomputable def zero [HasZeroObject V] : HomologicalComplex V c where
  X _ := 0
  d _ _ := 0

theorem isZero_zero [HasZeroObject V] : IsZero (zero : HomologicalComplex V c) := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  all_goals
    ext
    dsimp only [zero]
    subsingleton

instance [HasZeroObject V] : HasZeroObject (HomologicalComplex V c) :=
  ⟨⟨zero, isZero_zero⟩⟩

noncomputable instance [HasZeroObject V] : Inhabited (HomologicalComplex V c) :=
  ⟨zero⟩

theorem congr_hom {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι) :
    f.f i = g.f i :=
  congr_fun (congr_arg Hom.f w) i

lemma mono_of_mono_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : ∀ i, Mono (φ.f i)) : Mono φ where
  right_cancellation g h eq := by
    ext i
    rw [← cancel_mono (φ.f i)]
    exact congr_hom eq i

lemma epi_of_epi_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : ∀ i, Epi (φ.f i)) : Epi φ where
  left_cancellation g h eq := by
    ext i
    rw [← cancel_epi (φ.f i)]
    exact congr_hom eq i

section

variable (V c)

/-- The functor picking out the `i`-th object of a complex. -/
@[simps]
def eval (i : ι) : HomologicalComplex V c ⥤ V where
  obj C := C.X i
  map f := f.f i

instance (i : ι) : (eval V c i).PreservesZeroMorphisms where

/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps]
def forget : HomologicalComplex V c ⥤ GradedObject ι V where
  obj C := C.X
  map f := f.f

instance : (forget V c).Faithful where
  map_injective h := by
    ext i
    exact congr_fun h i

/-- Forgetting the differentials than picking out the `i`-th object is the same as
just picking out the `i`-th object. -/
@[simps!]
def forgetEval (i : ι) : forget V c ⋙ GradedObject.eval i ≅ eval V c i :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The differential as a natural transformation between `eval`. -/
@[simps] def dNatTrans (i j : ι) :
    HomologicalComplex.eval V c i ⟶ HomologicalComplex.eval V c j where
  app X := X.d i j

end

noncomputable section

@[reassoc]
lemma XIsoOfEq_hom_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n') :
    φ.f n ≫ (L.XIsoOfEq h).hom = (K.XIsoOfEq h).hom ≫ φ.f n' := by subst h; simp

@[reassoc]
lemma XIsoOfEq_inv_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n') :
    φ.f n' ≫ (L.XIsoOfEq h).inv = (K.XIsoOfEq h).inv ≫ φ.f n := by subst h; simp

/-- If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eqToHom`.
-/
@[simp]
theorem d_comp_eqToHom {i j j' : ι} (rij : c.Rel i j) (rij' : c.Rel i j') :
    C.d i j' ≫ eqToHom (congr_arg C.X (c.next_eq rij' rij)) = C.d i j := by
  obtain rfl := c.next_eq rij rij'
  simp only [eqToHom_refl, comp_id]

/-- If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eqToHom`.
-/
@[simp]
theorem eqToHom_comp_d {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j) :
    eqToHom (congr_arg C.X (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j := by
  obtain rfl := c.prev_eq rij rij'
  simp only [eqToHom_refl, id_comp]

theorem kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j') :
    kernelSubobject (C.d i j) = kernelSubobject (C.d i j') := by
  rw [← d_comp_eqToHom C r r']
  apply kernelSubobject_comp_mono

theorem image_eq_image [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j)
    (r' : c.Rel i' j) : imageSubobject (C.d i j) = imageSubobject (C.d i' j) := by
  rw [← eqToHom_comp_d C r r']
  apply imageSubobject_iso_comp

section

/-- Either `C.X i`, if there is some `i` with `c.Rel i j`, or `C.X j`. -/
abbrev xPrev (j : ι) : V :=
  C.X (c.prev j)

/-- If `c.Rel i j`, then `C.xPrev j` is isomorphic to `C.X i`. -/
def xPrevIso {i j : ι} (r : c.Rel i j) : C.xPrev j ≅ C.X i :=
  eqToIso <| by rw [← c.prev_eq' r]

/-- If there is no `i` so `c.Rel i j`, then `C.xPrev j` is isomorphic to `C.X j`. -/
def xPrevIsoSelf {j : ι} (h : ¬c.Rel (c.prev j) j) : C.xPrev j ≅ C.X j :=
  eqToIso <|
    congr_arg C.X
      (by
        dsimp [ComplexShape.prev]
        rw [dif_neg]
        push Not; intro i hi
        have : c.prev j = i := c.prev_eq' hi
        rw [this] at h; contradiction)

/-- Either `C.X j`, if there is some `j` with `c.rel i j`, or `C.X i`. -/
abbrev xNext (i : ι) : V :=
  C.X (c.next i)

/-- If `c.Rel i j`, then `C.xNext i` is isomorphic to `C.X j`. -/
def xNextIso {i j : ι} (r : c.Rel i j) : C.xNext i ≅ C.X j :=
  eqToIso <| by rw [← c.next_eq' r]

/-- If there is no `j` so `c.Rel i j`, then `C.xNext i` is isomorphic to `C.X i`. -/
def xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) : C.xNext i ≅ C.X i :=
  eqToIso <|
    congr_arg C.X
      (by
        dsimp [ComplexShape.next]
        rw [dif_neg]; rintro ⟨j, hj⟩
        have : c.next i = j := c.next_eq' hj
        rw [this] at h; contradiction)

/-- The differential mapping into `C.X j`, or zero if there isn't one.
-/
abbrev dTo (j : ι) : C.xPrev j ⟶ C.X j :=
  C.d (c.prev j) j

/-- The differential mapping out of `C.X i`, or zero if there isn't one.
-/
abbrev dFrom (i : ι) : C.X i ⟶ C.xNext i :=
  C.d i (c.next i)

theorem dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = (C.xPrevIso r).hom ≫ C.d i j := by
  obtain rfl := c.prev_eq' r
  exact (Category.id_comp _).symm

theorem dTo_eq_zero {j : ι} (h : ¬c.Rel (c.prev j) j) : C.dTo j = 0 := by
  simp [h]

theorem dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).inv := by
  obtain rfl := c.next_eq' r
  exact (Category.comp_id _).symm

theorem dFrom_eq_zero {i : ι} (h : ¬c.Rel i (c.next i)) : C.dFrom i = 0 := by
  simp [h]

@[reassoc (attr := simp)]
theorem xPrevIso_comp_dTo {i j : ι} (r : c.Rel i j) : (C.xPrevIso r).inv ≫ C.dTo j = C.d i j := by
  simp [C.dTo_eq r]

@[reassoc]
theorem xPrevIsoSelf_comp_dTo {j : ι} (h : ¬c.Rel (c.prev j) j) :
    (C.xPrevIsoSelf h).inv ≫ C.dTo j = 0 := by simp [h]

@[reassoc (attr := simp)]
theorem dFrom_comp_xNextIso {i j : ι} (r : c.Rel i j) :
    C.dFrom i ≫ (C.xNextIso r).hom = C.d i j := by
  simp [C.dFrom_eq r]

@[reassoc]
theorem dFrom_comp_xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) :
    C.dFrom i ≫ (C.xNextIsoSelf h).hom = 0 := by simp [h]

-- This is not a simp lemma; the LHS already simplifies.
theorem dTo_comp_dFrom (j : ι) : C.dTo j ≫ C.dFrom j = 0 :=
  C.d_comp_d _ _ _

theorem kernel_from_eq_kernel [HasKernels V] {i j : ι} (r : c.Rel i j) :
    kernelSubobject (C.dFrom i) = kernelSubobject (C.d i j) := by
  rw [C.dFrom_eq r]
  apply kernelSubobject_comp_mono

theorem image_to_eq_image [HasImages V] [HasEqualizers V] {i j : ι} (r : c.Rel i j) :
    imageSubobject (C.dTo j) = imageSubobject (C.d i j) := by
  rw [C.dTo_eq r]
  apply imageSubobject_iso_comp

end

namespace Hom

variable {C₁ C₂ C₃ : HomologicalComplex V c}

/-- The `i`-th component of an isomorphism of chain complexes. -/
@[simps!]
def isoApp (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
  (eval V c i).mapIso f

/-- Construct an isomorphism of chain complexes from isomorphism of the objects
which commute with the differentials. -/
@[simps]
def isoOfComponents (f : ∀ i, C₁.X i ≅ C₂.X i)
    (hf : ∀ i j, c.Rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom := by cat_disch) :
    C₁ ≅ C₂ where
  hom :=
    { f := fun i => (f i).hom
      comm' := hf }
  inv :=
    { f := fun i => (f i).inv
      comm' := fun i j hij =>
        calc
          (f i).inv ≫ C₁.d i j = (f i).inv ≫ (C₁.d i j ≫ (f j).hom) ≫ (f j).inv := by simp
          _ = (f i).inv ≫ ((f i).hom ≫ C₂.d i j) ≫ (f j).inv := by rw [hf i j hij]
          _ = C₂.d i j ≫ (f j).inv := by simp }
  hom_inv_id := by
    ext i
    exact (f i).hom_inv_id
  inv_hom_id := by
    ext i
    exact (f i).inv_hom_id

@[simp]
theorem isoOfComponents_app (f : ∀ i, C₁.X i ≅ C₂.X i)
    (hf : ∀ i j, c.Rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) (i : ι) :
    isoApp (isoOfComponents f hf) i = f i := by
  ext
  simp

theorem isIso_of_components (f : C₁ ⟶ C₂) [∀ n : ι, IsIso (f.f n)] : IsIso f :=
  (HomologicalComplex.Hom.isoOfComponents fun n => asIso (f.f n)).isIso_hom

/-! Lemmas relating chain maps and `dTo`/`dFrom`. -/


/-- `f.prev j` is `f.f i` if there is some `r i j`, and `f.f j` otherwise. -/
abbrev prev (f : Hom C₁ C₂) (j : ι) : C₁.xPrev j ⟶ C₂.xPrev j :=
  f.f _

theorem prev_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.prev j = (C₁.xPrevIso w).hom ≫ f.f i ≫ (C₂.xPrevIso w).inv := by
  obtain rfl := c.prev_eq' w
  simp only [xPrevIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

/-- `f.next i` is `f.f j` if there is some `r i j`, and `f.f j` otherwise. -/
abbrev next (f : Hom C₁ C₂) (i : ι) : C₁.xNext i ⟶ C₂.xNext i :=
  f.f _

theorem next_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.next i = (C₁.xNextIso w).hom ≫ f.f j ≫ (C₂.xNextIso w).inv := by
  obtain rfl := c.next_eq' w
  simp only [xNextIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

@[reassoc, elementwise]
theorem comm_from (f : Hom C₁ C₂) (i : ι) : f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i :=
  f.comm _ _

attribute [simp] comm_from_apply

@[reassoc, elementwise]
theorem comm_to (f : Hom C₁ C₂) (j : ι) : f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j :=
  f.comm _ _

attribute [simp] comm_to_apply

/-- A morphism of chain complexes
induces a morphism of arrows of the differentials out of each object.
-/
def sqFrom (f : Hom C₁ C₂) (i : ι) : Arrow.mk (C₁.dFrom i) ⟶ Arrow.mk (C₂.dFrom i) :=
  Arrow.homMk _ _ (f.comm_from i)

@[simp]
theorem sqFrom_left (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).left = f.f i :=
  rfl

@[simp]
theorem sqFrom_right (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).right = f.next i :=
  rfl

@[simp]
theorem sqFrom_id (C₁ : HomologicalComplex V c) (i : ι) : sqFrom (𝟙 C₁) i = 𝟙 _ :=
  rfl

@[simp]
theorem sqFrom_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    sqFrom (f ≫ g) i = sqFrom f i ≫ sqFrom g i :=
  rfl

/-- A morphism of chain complexes
induces a morphism of arrows of the differentials into each object.
-/
def sqTo (f : Hom C₁ C₂) (j : ι) : Arrow.mk (C₁.dTo j) ⟶ Arrow.mk (C₂.dTo j) :=
  Arrow.homMk _ _ (f.comm_to j)

@[simp]
theorem sqTo_left (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).left = f.prev j :=
  rfl

@[simp]
theorem sqTo_right (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).right = f.f j :=
  rfl

end Hom

end

end HomologicalComplex

namespace ChainComplex

section Of

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/-- Construct an `α`-indexed chain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) : ChainComplex V α :=
  { X := X
    d := fun i j => if h : i = j + 1 then eqToHom (by rw [h]) ≫ d j else 0
    shape := fun i j w => by
      rw [dif_neg (Ne.symm w)]
    d_comp_d' := fun i j k hij hjk => by
      dsimp at hij hjk
      substs hij hjk
      simp only [eqToHom_refl, id_comp, dite_eq_ite, ite_true, sq] }

variable (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0)

@[simp]
theorem of_x (n : α) : (of X d sq).X n = X n :=
  rfl

@[simp]
theorem of_d (j : α) : (of X d sq).d (j + 1) j = d j := by
  dsimp [of]
  rw [if_pos rfl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem of_d_ne {i j : α} (h : i ≠ j + 1) : (of X d sq).d i j = 0 := by
  dsimp [of]
  rw [dif_neg h]

end Of

section OfHom

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
variable (X : α → V) (d_X : ∀ n, X (n + 1) ⟶ X n) (sq_X : ∀ n, d_X (n + 1) ≫ d_X n = 0) (Y : α → V)
  (d_Y : ∀ n, Y (n + 1) ⟶ Y n) (sq_Y : ∀ n, d_Y (n + 1) ≫ d_Y n = 0)

set_option backward.isDefEq.respectTransparency false in
/-- A constructor for chain maps between `α`-indexed chain complexes built using `ChainComplex.of`,
from a dependently typed collection of morphisms.
-/
@[simps]
def ofHom (f : ∀ i : α, X i ⟶ Y i) (comm : ∀ i : α, f (i + 1) ≫ d_Y i = d_X i ≫ f i) :
    of X d_X sq_X ⟶ of Y d_Y sq_Y :=
  { f
    comm' := fun n m => by
      by_cases h : n = m + 1
      · subst h
        simpa using comm m
      · rw [of_d_ne X _ _ h, of_d_ne Y _ _ h]
        simp }

end OfHom

section Mk

variable {V}


variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₃ : V) (d₂ : X₃ ⟶ S.X₁), d₂ ≫ S.f = 0)

/-- Auxiliary definition for `mk`. -/
def mkAux : ℕ → ShortComplex V
  | 0 => ShortComplex.mk _ _ s
  | n + 1 => ShortComplex.mk _ _ (succ (mkAux n)).2.2

/-- An inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropriately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : ChainComplex V ℕ :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₃) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).g)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ :=
  rfl

@[simp]
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ :=
  rfl

@[simp]
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ :=
  rfl

@[simp]
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl, Category.id_comp]

@[simp]
theorem mk_d_2_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁ := by
  change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁
  rw [if_pos rfl, Category.id_comp]

lemma mk_congr_succ_X₃ {S S' : ShortComplex V} (h : S = S') :
    (succ S).1 = (succ S').1 := by rw [h]

lemma mk_congr_succ_d₂ {S S' : ShortComplex V} (h : S = S') :
    (succ S).2.1 = eqToHom (by subst h; rfl) ≫ (succ S').2.1 ≫ eqToHom (by subst h; rfl) := by
  subst h
  simp

lemma mkAux_eq_shortComplex_mk_d_comp_d (n : ℕ) :
    mkAux X₀ X₁ X₂ d₀ d₁ s succ n =
      ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n) := by
  change ShortComplex.mk _ _ (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero = _
  dsimp [mk, of, mkAux]
  simp

/-- The isomorphism from `(mk X₀ X₁ X₂ d₀ d₁ s succ).X (n + 3)` that is given by
the inductive construction. -/
def mkXIso (n : ℕ) :
    (mk X₀ X₁ X₂ d₀ d₁ s succ).X (n + 3) ≅
      (succ (ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n))).1 :=
  eqToIso (by
    rw [← mk_congr_succ_X₃ succ
      (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)]
    rfl)

set_option backward.isDefEq.respectTransparency false in
lemma mk_d (n : ℕ) :
    (mk X₀ X₁ X₂ d₀ d₁ s succ).d (n + 3) (n + 2) =
      (mkXIso X₀ X₁ X₂ d₀ d₁ s succ n).hom ≫ (succ
        (ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n))).2.1 := by
  have eq := mk_congr_succ_d₂ succ
    (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)
  rw [eqToHom_refl, comp_id] at eq
  refine Eq.trans ?_ eq
  dsimp only [mk, of]
  rw [dif_pos (by rfl), eqToHom_refl, id_comp]
  rfl

/-- A simpler inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₁ ⟶ X₀)
    (succ' : ∀ {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0) :
    ChainComplex V ℕ :=
  mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.f)

variable (succ' : ∀ {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0)

@[simp]
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ :=
  rfl

@[simp]
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ :=
  rfl


@[simp]
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl, Category.id_comp]

/-- The isomorphism from `(mk' X₀ X₁ d₀ succ').X (n + 2)` that is given by
the inductive construction. -/
def mk'XIso (n : ℕ) :
    (mk' X₀ X₁ d₀ succ').X (n + 2) ≅ (succ' ((mk' X₀ X₁ d₀ succ').d (n + 1) n)).1 := by
  obtain _ | n := n
  · apply eqToIso
    dsimp [mk', mk, of, mkAux]
    rw [id_comp]
  · exact mkXIso _ _ _ _ _ (succ' d₀).2.2 (fun S => succ' S.f) n

lemma mk'_congr_succ'_d {X Y : V} (f g : X ⟶ Y) (h : f = g) :
    (succ' f).2.1 = eqToHom (by rw [h]) ≫ (succ' g).2.1 := by
  subst h
  simp

lemma mk'_d (n : ℕ) :
    (mk' X₀ X₁ d₀ succ').d (n + 2) (n + 1) = (mk'XIso X₀ X₁ d₀ succ' n).hom ≫
      (succ' ((mk' X₀ X₁ d₀ succ').d (n + 1) n)).2.1 := by
  obtain _ | n := n
  · dsimp [mk'XIso, mk']
    rw [mk_d_2_1]
    apply mk'_congr_succ'_d
    rw [mk_d_1_0]
  · apply mk_d

end Mk

section MkHom

variable {V}
variable (P Q : ChainComplex V ℕ) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), f'' ≫ Q.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1)

/-- An auxiliary construction for `mkHom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mkHom`.
-/
def mkHomAux :
    ∀ n,
      Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
        f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mkHomAux n).2.1, (succ n (mkHomAux n)).1, (succ n (mkHomAux n)).2⟩

/-- A constructor for chain maps between `ℕ`-indexed chain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : m + 1 = n)
    exact (mkHomAux P Q zero one one_zero_comm succ m).2.2

@[simp]
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
theorem mkHom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n,
            (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm (n + 1) n⟩).1 := by
  dsimp [mkHom, mkHomAux]

end MkHom

end ChainComplex

namespace CochainComplex

section Of

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/-- Construct an `α`-indexed cochain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0) :
    CochainComplex V α :=
  { X := X
    d := fun i j => if h : i + 1 = j then d _ ≫ eqToHom (by rw [h]) else 0
    shape := fun i j w => by
      rw [dif_neg]
      exact w
    d_comp_d' := fun i j k => by
      dsimp
      split_ifs with h h' h'
      · substs h h'
        simp [sq]
      all_goals simp }

variable (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0)

@[simp]
theorem of_x (n : α) : (of X d sq).X n = X n :=
  rfl

@[simp]
theorem of_d (j : α) : (of X d sq).d j (j + 1) = d j := by
  dsimp [of]
  rw [if_pos rfl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem of_d_ne {i j : α} (h : i + 1 ≠ j) : (of X d sq).d i j = 0 := by
  dsimp [of]
  rw [dif_neg h]

end Of

section OfHom

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
variable (X : α → V) (d_X : ∀ n, X n ⟶ X (n + 1)) (sq_X : ∀ n, d_X n ≫ d_X (n + 1) = 0) (Y : α → V)
  (d_Y : ∀ n, Y n ⟶ Y (n + 1)) (sq_Y : ∀ n, d_Y n ≫ d_Y (n + 1) = 0)

set_option backward.isDefEq.respectTransparency false in
/--
A constructor for chain maps between `α`-indexed cochain complexes built using `CochainComplex.of`,
from a dependently typed collection of morphisms.
-/
@[simps]
def ofHom (f : ∀ i : α, X i ⟶ Y i) (comm : ∀ i : α, f i ≫ d_Y i = d_X i ≫ f (i + 1)) :
    of X d_X sq_X ⟶ of Y d_Y sq_Y :=
  { f
    comm' := fun n m => by
      by_cases h : n + 1 = m
      · subst h
        simpa using comm n
      · rw [of_d_ne X _ _ h, of_d_ne Y _ _ h]
        simp }

end OfHom

section Mk

variable {V}
variable (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₄ : V) (d₂ : S.X₃ ⟶ X₄), S.g ≫ d₂ = 0)

/-- Auxiliary definition for `mk`. -/
def mkAux : ℕ → ShortComplex V
  | 0 => ShortComplex.mk _ _ s
  | n + 1 => ShortComplex.mk _ _ (succ (mkAux n)).2.2

/-- An inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropriately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : CochainComplex V ℕ :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₁) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).f)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ :=
  rfl

@[simp]
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ :=
  rfl

@[simp]
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ :=
  rfl

@[simp]
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl, Category.comp_id]

@[simp]
theorem mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁ := by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁
  rw [if_pos rfl, Category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
/-- A simpler inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₀ ⟶ X₁)
    -- (succ' : ∀ : Σ X₀ X₁ : V, X₀ ⟶ X₁, Σ' (X₂ : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0) :
    (succ' : ∀ {X₀ X₁ : V} (f : X₀ ⟶ X₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0) :
    CochainComplex V ℕ :=
  mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.g)

variable (succ' : ∀ {X₀ X₁ : V} (f : X₀ ⟶ X₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0)

@[simp]
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ :=
  rfl

@[simp]
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ :=
  rfl

@[simp]
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl, Category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
end Mk

section MkHom

variable {V}
variable (P Q : CochainComplex V ℕ) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : zero ≫ Q.d 0 1 = P.d 0 1 ≫ one)
  (succ : ∀ (n : ℕ) (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), p.2.1 ≫ Q.d (n + 1) (n + 2) = P.d (n + 1) (n + 2) ≫ f'')

/-- An auxiliary construction for `mkHom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mkHom`.
-/
def mkHomAux :
    ∀ n,
      Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
        f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mkHomAux n).2.1, (succ n (mkHomAux n)).1, (succ n (mkHomAux n)).2⟩

/-- A constructor for chain maps between `ℕ`-indexed cochain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : n + 1 = m)
    exact (mkHomAux P Q zero one one_zero_comm succ n).2.2

@[simp]
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
theorem mkHom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n,
            (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm n (n + 1)⟩).1 := by
  dsimp [mkHom, mkHomAux]

end MkHom

end CochainComplex
