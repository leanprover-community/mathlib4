/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
<<<<<<< HEAD
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Tactic.Linarith
=======
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Tactic.Linarith

>>>>>>> origin/homology-sequence-computation
/-!
# The short complexes attached to homological complexes

In this file, we define a functor
`shortComplexFunctor C c i : HomologicalComplex C c ⥤ ShortComplex C`.
By definition, the image of a homological complex `K` by this functor
is the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`.

The homology `K.homology i` of a homological complex `K` in degree `i` is defined as
the homology of the short complex `(shortComplexFunctor C c i).obj K`, which can be
abbreviated as `K.sc i`.

-/

open CategoryTheory Category Limits ZeroObject

namespace HomologicalComplex

variable (C : Type*) [Category C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
@[simps]
def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where
  obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
@[simps!]
noncomputable def shortComplexFunctor (i : ι) :=
  shortComplexFunctor' C c (c.prev i) i (c.next i)

variable {C c}

section

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (ψ : L ⟶ M) (i j k : ι)

/-- The short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
abbrev sc' := (shortComplexFunctor' C c i j k).obj K

/-- The short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
noncomputable abbrev sc := (shortComplexFunctor C c i).obj K

abbrev HasHomology (i : ι) := (K.sc i).HasHomology

variable (i : ι) [K.HasHomology i] [L.HasHomology i] [M.HasHomology i]

noncomputable def homology := (K.sc i).homology
noncomputable def cycles := (K.sc i).cycles
noncomputable def homologyπ : K.cycles i ⟶ K.homology i := (K.sc i).homologyπ
noncomputable def iCycles : K.cycles i ⟶ K.X i := (K.sc i).iCycles

variable {i}

noncomputable def liftCycles {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  (K.sc i).liftCycles k (by subst hj ; exact hk)

@[reducible]
noncomputable def liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  K.liftCycles k j (c.next_eq' hj) hk

@[reassoc (attr := simp)]
lemma liftCycles_i {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iCycles i = k := by
  dsimp [liftCycles, iCycles]
  simp

noncomputable def toCycles (i j : ι) [K.HasHomology j] :
  K.X i ⟶ K.cycles j :=
  K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

variable (i)

@[reassoc (attr := simp)]
lemma iCycles_d (j : ι) : K.iCycles i ≫ K.d i j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  · rw [K.shape _ _ hij, comp_zero]

noncomputable def cyclesIsKernel (i j : ι) (hij : c.Rel i j) [K.HasHomology i]:
    IsLimit (KernelFork.ofι (K.iCycles i) (K.iCycles_d i j)) := by
  obtain rfl := c.next_eq' hij
  exact (K.sc i).cyclesIsKernel

@[reassoc (attr := simp)]
lemma toCycles_i (i j : ι) [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j :=
  liftCycles_i _ _ _ _ _

instance [K.HasHomology i] : Mono (K.iCycles i) := by
  dsimp only [iCycles]
  infer_instance

instance [K.HasHomology i] : Epi (K.homologyπ i) := by
  dsimp only [homologyπ]
  infer_instance

variable {i}

@[reassoc]
lemma comp_liftCycles {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (α : A' ⟶ A) :
    α ≫ K.liftCycles k j hj hk = K.liftCycles (α ≫ k) j hj (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono (K.iCycles i), assoc, liftCycles_i]

@[reassoc]
lemma liftCycles_homologyπ_eq_zero_of_boundary {A : C} (k : A ⟶ K.X i) (j : ι)
    (hj : c.next i = j) {i' : ι} (x : A ⟶ K.X i') (hx : k = x ≫ K.d i' i) :
    K.liftCycles k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) ≫ K.homologyπ i = 0 := by
  by_cases c.Rel i' i
  · obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  · have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h, comp_zero] at hx
      rw [← cancel_mono (K.iCycles i), zero_comp, liftCycles_i, hx]
    rw [this, zero_comp]

@[reassoc (attr := simp)]
lemma toCycles_comp_homologyπ (i j : ι) [K.HasHomology j] :
    K.toCycles i j ≫ K.homologyπ j = 0 :=
  K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

noncomputable def homologyIsCokernel (i j : ι) (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ i j)) := by
  subst hi
  exact ((K.sc j).homologyIsCokernel)

variable (i)

noncomputable def opcycles := (K.sc i).opcycles
noncomputable def homologyι : K.homology i ⟶ K.opcycles i := (K.sc i).homologyι
noncomputable def pOpcycles : K.X i ⟶ K.opcycles i := (K.sc i).pOpcycles

variable {i}

noncomputable def descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  (K.sc i).descOpcycles k (by subst hj; exact hk)

@[reducible]
noncomputable def descOpcycles' {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  K.descOpcycles k j (c.prev_eq' hj) hk

@[reassoc (attr := simp)]
lemma p_descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpcycles k j hj hk = k := by
  dsimp [descOpcycles, pOpcycles]
  simp

noncomputable def fromOpcycles (i j : ι) [K.HasHomology i] :
  K.opcycles i ⟶ K.X j  :=
  K.descOpcycles (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

variable (i)

@[reassoc (attr := simp)]
lemma d_pOpcycles (X : HomologicalComplex C c) (i j : ι) [X.HasHomology j] : X.d i j ≫ X.pOpcycles j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    exact (X.sc j).f_pOpcycles
  · rw [X.shape _ _ hij, zero_comp]

noncomputable def opcyclesIsCokernel (i j : ι) (hij : c.Rel i j) [K.HasHomology j]:
    IsColimit (CokernelCofork.ofπ (K.pOpcycles j) (K.d_pOpcycles i j)) := by
  obtain rfl := c.prev_eq' hij
  exact (K.sc j).opcyclesIsCokernel

@[reassoc (attr := simp)]
lemma p_fromOpcycles (i j : ι) [K.HasHomology i] :
    K.pOpcycles i ≫ K.fromOpcycles i j = K.d i j :=
  p_descOpcycles _ _ _ _ _

instance [K.HasHomology i] : Epi (K.pOpcycles i) := by
  dsimp only [pOpcycles]
  infer_instance

instance [K.HasHomology i] : Mono (K.homologyι i) := by
  dsimp only [homologyι]
  infer_instance

@[reassoc (attr := simp)]
lemma fromOpcycles_d (i j k : ι) [K.HasHomology i] :
    K.fromOpcycles i j ≫ K.d j k = 0 := by
  simp only [← cancel_epi (K.pOpcycles i),
   p_fromOpcycles_assoc, d_comp_d, comp_zero]

variable {i}

@[reassoc]
lemma descOpcycles_comp {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) (α : A ⟶ A') :
    K.descOpcycles k j hj hk ≫ α = K.descOpcycles (k ≫ α) j hj
      (by rw [reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_descOpcycles_assoc, p_descOpcycles]

lemma homologyι_descOpcycles_eq_zero_of_boundary {A : C} (k : K.X i ⟶ A) (j : ι)
    (hj : c.prev i = j) {i' : ι} (x : K.X i' ⟶ A) (hx : k = K.d i i' ≫ x) :
    K.homologyι i ≫ K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
  by_cases c.Rel i i'
  · obtain rfl := c.next_eq' h
    exact (K.sc i).homologyι_descOpcycles_eq_zero_of_boundary _ x hx
  · have : K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
      rw [K.shape _ _ h, zero_comp] at hx
      rw [← cancel_epi (K.pOpcycles i), comp_zero, p_descOpcycles, hx]
    rw [this, comp_zero]

@[reassoc (attr := simp)]
lemma homologyι_comp_fromOpcycles (i j : ι) [K.HasHomology i] :
    K.homologyι i ≫ K.fromOpcycles i j = 0 :=
  K.homologyι_descOpcycles_eq_zero_of_boundary (K.d i j) _ rfl (𝟙 _) (by simp)

noncomputable def homologyIsKernel (i j : ι) (hi : c.next i = j) [K.HasHomology i] :
    IsLimit (KernelFork.ofι (K.homologyι i) (K.homologyι_comp_fromOpcycles i j)) := by
  subst hi
  exact (K.sc i).homologyIsKernel

variable (i)
variable {K L M}

noncomputable def homologyMap : K.homology i ⟶ L.homology i :=
  ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

noncomputable def cyclesMap : K.cycles i ⟶ L.cycles i :=
  ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)

noncomputable def opcyclesMap : K.opcycles i ⟶ L.opcycles i :=
  ShortComplex.opcyclesMap ((shortComplexFunctor C c i).map φ)

@[reassoc (attr := simp)]
lemma cyclesMap_i : cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i :=
  ShortComplex.cyclesMap_i _

@[reassoc (attr := simp)]
lemma p_opcyclesMap : K.pOpcycles i ≫ opcyclesMap φ i = φ.f i ≫ L.pOpcycles i :=
  ShortComplex.p_opcyclesMap _

variable (K)

@[simp]
lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.homologyMap_id _

@[simp]
lemma cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.cyclesMap_id _

@[simp]
lemma opcyclesMap_id : opcyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.opcyclesMap_id _

variable {K}

@[reassoc]
lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i := by
  dsimp [homologyMap]
  rw [Functor.map_comp, ShortComplex.homologyMap_comp]

@[reassoc]
lemma cyclesMap_comp : cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i := by
  dsimp [cyclesMap]
  rw [Functor.map_comp, ShortComplex.cyclesMap_comp]

@[reassoc]
lemma opcyclesMap_comp : opcyclesMap (φ ≫ ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ i := by
  dsimp [opcyclesMap]
  rw [Functor.map_comp, ShortComplex.opcyclesMap_comp]

variable (K L)

@[simp]
lemma homologyMap_zero : homologyMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.homologyMap_zero _ _

@[simp]
lemma cyclesMap_zero : cyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.cyclesMap_zero _ _

@[simp]
lemma opcyclesMap_zero : opcyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.opcyclesMap_zero _ _

variable {K L}

@[reassoc (attr := simp)]
lemma homologyπ_naturality :
    K.homologyπ i ≫ homologyMap φ i = cyclesMap φ i ≫ L.homologyπ i :=
  ShortComplex.homologyπ_naturality _

@[reassoc (attr := simp)]
lemma liftCycles_comp_cyclesMap {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (φ : K ⟶ L) :
    K.liftCycles k j hj hk ≫ cyclesMap φ i = L.liftCycles (k ≫ φ.f i) j hj
      (by rw [assoc, φ.comm, reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_mono (L.iCycles i), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

@[reassoc (attr := simp)]
lemma homologyι_naturality :
    homologyMap φ i ≫ L.homologyι i = K.homologyι i ≫ opcyclesMap φ i :=
  ShortComplex.homologyι_naturality _

@[reassoc (attr := simp)]
lemma opcyclesMap_comp_descOpcycles {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : L.d j i ≫ k = 0) (φ : K ⟶ L) :
    opcyclesMap φ i ≫ L.descOpcycles k j hj hk = K.descOpcycles (φ.f i ≫ k) j hj
      (by rw [← φ.comm_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]
lemma homology_π_ι (i : ι) [K.HasHomology i]:
    K.homologyπ i ≫ K.homologyι i = K.iCycles i ≫ K.pOpcycles i :=
  (K.sc i).homology_π_ι

variable (C c)

section

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

@[simps]
noncomputable def homologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.homology i
  map f := homologyMap f i

@[simps]
noncomputable def gradedHomologyFunctor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ GradedObject ι C where
  obj K i := K.homology i
  map f i := homologyMap f i

@[simps]
noncomputable def cyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.cycles i
  map f := cyclesMap f i

@[simps]
noncomputable def opcyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.opcycles i
  map f := opcyclesMap f i

@[simps]
noncomputable def natTransHomologyι [CategoryWithHomology C] :
    homologyFunctor C c i ⟶ opcyclesFunctor C c i where
  app K := K.homologyι i

@[simps]
noncomputable def natTransHomologyπ [CategoryWithHomology C] :
    cyclesFunctor C c i ⟶ homologyFunctor C c i where
  app K := K.homologyπ i

end

@[simps!]
noncomputable def homologyFunctorIso [CategoryWithHomology C] :
    homologyFunctor C c i ≅ shortComplexFunctor C c i ⋙ ShortComplex.homologyFunctor C :=
  NatIso.ofComponents (fun T => Iso.refl _) (by aesop_cat)

/- TODO : adapt more of the homology of ShortComplex API to this situation, including the
dual versions opcycles, etc... -/


@[simps!]
noncomputable def natIsoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by aesop_cat) (by aesop_cat)) (by aesop_cat)

variable {C c} (K L)

/-- The canonical isomorphism `K.sc j ≅ K.sc' i j k` when `c.prev j = i` and `c.next j = k`. -/
noncomputable abbrev isoSc' (hi : c.prev j = i) (hk : c.next j = k) :
    K.sc j ≅ K.sc' i j k := (natIsoSc' C c i j k hi hk).app K

<<<<<<< HEAD
abbrev ExactAt (i : ι) := (K.sc i).Exact

lemma exactAt_iff (i : ι) :
    K.ExactAt i ↔ (K.sc i).Exact := by rfl

lemma exactAt_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k):
    K.ExactAt j ↔ (K.sc' i j k).Exact :=
  ShortComplex.exact_iff_of_iso (K.isoSc' i j k hi hk)

lemma isZero_homology_iff (i : ι) [K.HasHomology i] :
    IsZero (K.homology i) ↔ K.ExactAt i := by
  dsimp only [homology]
  rw [← ShortComplex.exact_iff_isZero_homology]

lemma isIso_iCycles (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    IsIso (K.iCycles i) := by
  subst hj
  exact ShortComplex.isIso_iCycles _ h

lemma isIso_pOpcycles (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    IsIso (K.pOpcycles j) := by
  subst hi
  exact ShortComplex.isIso_pOpcycles _ h

lemma isIso_liftCycles (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    IsIso (K.liftCycles (𝟙 (K.X i)) j hj (by rw [h, comp_zero])) := by
  have := K.isIso_iCycles i j hj h
  exact IsIso.of_isIso_fac_right (K.liftCycles_i _ _ _ _)

lemma isIso_descOpcycles (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    IsIso (K.descOpcycles (𝟙 (K.X j)) i hi (by rw [h, zero_comp])) := by
  have := K.isIso_pOpcycles i j hi h
  exact IsIso.of_isIso_fac_left (K.p_descOpcycles _ _ _ _)

lemma isIso_homologyπ (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    IsIso (K.homologyπ j) :=
  ShortComplex.isIso_homologyπ _ (by aesop_cat)

@[simps! hom]
noncomputable def isoHomologyπ (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    K.cycles j ≅ K.homology j :=
  have := K.isIso_homologyπ i j hi h
  asIso (K.homologyπ j)

@[reassoc (attr := simp)]
lemma isoHomologyπ_hom_inv_id (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    K.homologyπ j ≫ (K.isoHomologyπ i j hi h).inv = 𝟙 _ := (K.isoHomologyπ i j hi h).hom_inv_id

@[reassoc (attr := simp)]
lemma isoHomologyπ_inv_hom_id (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    (K.isoHomologyπ i j hi h).inv ≫ K.homologyπ j = 𝟙 _ := (K.isoHomologyπ i j hi h).inv_hom_id

lemma isIso_homologyι (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    IsIso (K.homologyι i) :=
  ShortComplex.isIso_homologyι _ (by aesop_cat)

@[simps! hom]
noncomputable def isoHomologyι (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    K.homology i ≅ K.opcycles i :=
=======
/-- A homological complex `K` has homology in degree `i` if the associated
short complex `K.sc i` has. -/
abbrev HasHomology := (K.sc i).HasHomology

variable [K.HasHomology i]

/-- The homology in degree `i` of a homological complex. -/
noncomputable def homology := (K.sc i).homology

/-- Comparison isomorphism between the homology for the two homology API. -/
noncomputable def homology'IsoHomology {A : Type*} [Category A] [Abelian A]
    (K : HomologicalComplex A c) (i : ι) :
    K.homology' i ≅ K.homology i :=
  (K.sc i).homology'IsoHomology

/-- The cycles in degree `i` of a homological complex. -/
noncomputable def cycles := (K.sc i).cycles

/-- The inclusion of the cycles of a homological complex. -/
noncomputable def iCycles : K.cycles i ⟶ K.X i := (K.sc i).iCycles

/-- The homology class map from cycles to the homology of a homological complex. -/
noncomputable def homologyπ : K.cycles i ⟶ K.homology i := (K.sc i).homologyπ

variable {i}

/-- The morphism to `K.cycles i` that is induced by a "cycle", i.e. a morphism
to `K.X i` whose postcomposition with the differential is zero. -/
noncomputable def liftCycles {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  (K.sc i).liftCycles k (by subst hj; exact hk)

/-- The morphism to `K.cycles i` that is induced by a "cycle", i.e. a morphism
to `K.X i` whose postcomposition with the differential is zero. -/
@[reducible]
noncomputable def liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  K.liftCycles k j (c.next_eq' hj) hk

@[reassoc (attr := simp)]
lemma liftCycles_i {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iCycles i = k := by
  dsimp [liftCycles, iCycles]
  simp

variable (i)

/-- The map `K.X i ⟶ K.cycles j` induced by the differential `K.d i j`. -/
noncomputable def toCycles [K.HasHomology j] :
    K.X i ⟶ K.cycles j :=
  K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

@[reassoc (attr := simp)]
lemma iCycles_d : K.iCycles i ≫ K.d i j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  · rw [K.shape _ _ hij, comp_zero]

/-- `K.cycles i` is the kernel of `K.d i j` when `c.next i = j`. -/
noncomputable def cyclesIsKernel (hj : c.next i = j) :
    IsLimit (KernelFork.ofι (K.iCycles i) (K.iCycles_d i j)) := by
  obtain rfl := hj
  exact (K.sc i).cyclesIsKernel

@[reassoc (attr := simp)]
lemma toCycles_i [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j :=
  liftCycles_i _ _ _ _ _

instance : Mono (K.iCycles i) := by
  dsimp only [iCycles]
  infer_instance

instance : Epi (K.homologyπ i) := by
  dsimp only [homologyπ]
  infer_instance

@[reassoc (attr := simp)]
lemma d_toCycles [K.HasHomology k] :
    K.d i j ≫ K.toCycles j k = 0 := by
  simp only [← cancel_mono (K.iCycles k), assoc, toCycles_i, d_comp_d, zero_comp]

variable {i}

@[reassoc]
lemma comp_liftCycles {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (α : A' ⟶ A) :
    α ≫ K.liftCycles k j hj hk = K.liftCycles (α ≫ k) j hj (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono (K.iCycles i), assoc, liftCycles_i]

@[reassoc]
lemma liftCycles_homologyπ_eq_zero_of_boundary {A : C} (k : A ⟶ K.X i) (j : ι)
    (hj : c.next i = j) {i' : ι} (x : A ⟶ K.X i') (hx : k = x ≫ K.d i' i) :
    K.liftCycles k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) ≫ K.homologyπ i = 0 := by
  by_cases h : c.Rel i' i
  · obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  · have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h, comp_zero] at hx
      rw [← cancel_mono (K.iCycles i), zero_comp, liftCycles_i, hx]
    rw [this, zero_comp]

variable (i)

@[reassoc (attr := simp)]
lemma toCycles_comp_homologyπ [K.HasHomology j] :
    K.toCycles i j ≫ K.homologyπ j = 0 :=
  K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

/-- `K.homology j` is the cokernel of `K.toCycles i j : K.X i ⟶ K.cycles j`
when `c.prev j = i`. -/
noncomputable def homologyIsCokernel (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ i j)) := by
  subst hi
  exact ((K.sc j).homologyIsCokernel)

/-- The opcycles in degree `i` of a homological complex. -/
noncomputable def opcycles := (K.sc i).opcycles

/-- The projection to the opcycles of a homological complex. -/
noncomputable def pOpcycles : K.X i ⟶ K.opcycles i := (K.sc i).pOpcycles

/-- The inclusion map of the homology of a homological complex into its opcycles. -/
noncomputable def homologyι : K.homology i ⟶ K.opcycles i := (K.sc i).homologyι

variable {i}

/-- The morphism from `K.opcycles i` that is induced by an "opcycle", i.e. a morphism
from `K.X i` whose precomposition with the differential is zero. -/
noncomputable def descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  (K.sc i).descOpcycles k (by subst hj; exact hk)

/-- The morphism from `K.opcycles i` that is induced by an "opcycle", i.e. a morphism
from `K.X i` whose precomposition with the differential is zero. -/
@[reducible]
noncomputable def descOpcycles' {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  K.descOpcycles k j (c.prev_eq' hj) hk

@[reassoc (attr := simp)]
lemma p_descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpcycles k j hj hk = k := by
  dsimp [descOpcycles, pOpcycles]
  simp

variable (i)

/-- The map `K.opcycles i ⟶ K.X j` induced by the differential `K.d i j`. -/
noncomputable def fromOpcycles :
  K.opcycles i ⟶ K.X j  :=
  K.descOpcycles (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

@[reassoc (attr := simp)]
lemma d_pOpcycles [K.HasHomology j] : K.d i j ≫ K.pOpcycles j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    exact (K.sc j).f_pOpcycles
  · rw [K.shape _ _ hij, zero_comp]

/-- `K.opcycles j` is the cokernel of `K.d i j` when `c.prev j = i`. -/
noncomputable def opcyclesIsCokernel (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.pOpcycles j) (K.d_pOpcycles i j)) := by
  obtain rfl := hi
  exact (K.sc j).opcyclesIsCokernel

@[reassoc (attr := simp)]
lemma p_fromOpcycles :
    K.pOpcycles i ≫ K.fromOpcycles i j = K.d i j :=
  p_descOpcycles _ _ _ _ _

instance : Epi (K.pOpcycles i) := by
  dsimp only [pOpcycles]
  infer_instance

instance : Mono (K.homologyι i) := by
  dsimp only [homologyι]
  infer_instance

@[reassoc (attr := simp)]
lemma fromOpcycles_d :
    K.fromOpcycles i j ≫ K.d j k = 0 := by
  simp only [← cancel_epi (K.pOpcycles i), p_fromOpcycles_assoc, d_comp_d, comp_zero]

variable {i}

@[reassoc]
lemma descOpcycles_comp {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) (α : A ⟶ A') :
    K.descOpcycles k j hj hk ≫ α = K.descOpcycles (k ≫ α) j hj
      (by rw [reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_descOpcycles_assoc, p_descOpcycles]

@[reassoc]
lemma homologyι_descOpcycles_eq_zero_of_boundary {A : C} (k : K.X i ⟶ A) (j : ι)
    (hj : c.prev i = j) {i' : ι} (x : K.X i' ⟶ A) (hx : k = K.d i i' ≫ x) :
    K.homologyι i ≫ K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
  by_cases h : c.Rel i i'
  · obtain rfl := c.next_eq' h
    exact (K.sc i).homologyι_descOpcycles_eq_zero_of_boundary _ x hx
  · have : K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
      rw [K.shape _ _ h, zero_comp] at hx
      rw [← cancel_epi (K.pOpcycles i), comp_zero, p_descOpcycles, hx]
    rw [this, comp_zero]

variable (i)

@[reassoc (attr := simp)]
lemma homologyι_comp_fromOpcycles :
    K.homologyι i ≫ K.fromOpcycles i j = 0 :=
  K.homologyι_descOpcycles_eq_zero_of_boundary (K.d i j) _ rfl (𝟙 _) (by simp)

/-- `K.homology i` is the kernel of `K.fromOpcycles i j : K.opcycles i ⟶ K.X j`
when `c.next i = j`. -/
noncomputable def homologyIsKernel (hi : c.next i = j) :
    IsLimit (KernelFork.ofι (K.homologyι i) (K.homologyι_comp_fromOpcycles i j)) := by
  subst hi
  exact (K.sc i).homologyIsKernel

variable {K L M}
variable [L.HasHomology i] [M.HasHomology i]

/-- The map `K.homology i ⟶ L.homology i` induced by a morphism in `HomologicalComplex`. -/
noncomputable def homologyMap : K.homology i ⟶ L.homology i :=
  ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

/-- The map `K.cycles i ⟶ L.cycles i` induced by a morphism in `HomologicalComplex`. -/
noncomputable def cyclesMap : K.cycles i ⟶ L.cycles i :=
  ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)

/-- The map `K.opcycles i ⟶ L.opcycles i` induced by a morphism in `HomologicalComplex`. -/
noncomputable def opcyclesMap : K.opcycles i ⟶ L.opcycles i :=
  ShortComplex.opcyclesMap ((shortComplexFunctor C c i).map φ)

@[reassoc (attr := simp)]
lemma cyclesMap_i : cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i :=
  ShortComplex.cyclesMap_i _

@[reassoc (attr := simp)]
lemma p_opcyclesMap : K.pOpcycles i ≫ opcyclesMap φ i = φ.f i ≫ L.pOpcycles i :=
  ShortComplex.p_opcyclesMap _

instance [Mono (φ.f i)] : Mono (cyclesMap φ i) := mono_of_mono_fac (cyclesMap_i φ i)

attribute [local instance] epi_comp

instance [Epi (φ.f i)] : Epi (opcyclesMap φ i) := epi_of_epi_fac (p_opcyclesMap φ i)

variable (K)

@[simp]
lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.homologyMap_id _

@[simp]
lemma cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.cyclesMap_id _

@[simp]
lemma opcyclesMap_id : opcyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.opcyclesMap_id _

variable {K}

@[reassoc]
lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i := by
  dsimp [homologyMap]
  rw [Functor.map_comp, ShortComplex.homologyMap_comp]

@[reassoc]
lemma cyclesMap_comp : cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i := by
  dsimp [cyclesMap]
  rw [Functor.map_comp, ShortComplex.cyclesMap_comp]

@[reassoc]
lemma opcyclesMap_comp : opcyclesMap (φ ≫ ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ i := by
  dsimp [opcyclesMap]
  rw [Functor.map_comp, ShortComplex.opcyclesMap_comp]

variable (K L)

@[simp]
lemma homologyMap_zero : homologyMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.homologyMap_zero _ _

@[simp]
lemma cyclesMap_zero : cyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.cyclesMap_zero _ _

@[simp]
lemma opcyclesMap_zero : opcyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.opcyclesMap_zero _ _

variable {K L}

@[reassoc (attr := simp)]
lemma homologyπ_naturality :
    K.homologyπ i ≫ homologyMap φ i = cyclesMap φ i ≫ L.homologyπ i :=
  ShortComplex.homologyπ_naturality _

@[reassoc (attr := simp)]
lemma homologyι_naturality :
    homologyMap φ i ≫ L.homologyι i = K.homologyι i ≫ opcyclesMap φ i :=
  ShortComplex.homologyι_naturality _

@[reassoc (attr := simp)]
lemma homology_π_ι :
    K.homologyπ i ≫ K.homologyι i = K.iCycles i ≫ K.pOpcycles i :=
  (K.sc i).homology_π_ι

variable {i}

@[reassoc (attr := simp)]
lemma opcyclesMap_comp_descOpcycles {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : L.d j i ≫ k = 0) (φ : K ⟶ L) :
    opcyclesMap φ i ≫ L.descOpcycles k j hj hk = K.descOpcycles (φ.f i ≫ k) j hj
      (by rw [← φ.comm_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]
lemma liftCycles_comp_cyclesMap {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (φ : K ⟶ L) :
    K.liftCycles k j hj hk ≫ cyclesMap φ i = L.liftCycles (k ≫ φ.f i) j hj
      (by rw [assoc, φ.comm, reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_mono (L.iCycles i), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

section

variable (C c i)

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

/-- The `i`th homology functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
noncomputable def homologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.homology i
  map f := homologyMap f i

/-- The homology functor to graded objects. -/
@[simps]
noncomputable def gradedHomologyFunctor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ GradedObject ι C where
  obj K i := K.homology i
  map f i := homologyMap f i

/-- The `i`th cycles functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
noncomputable def cyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.cycles i
  map f := cyclesMap f i

/-- The `i`th opcycles functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
noncomputable def opcyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.opcycles i
  map f := opcyclesMap f i

/-- The natural transformation `K.homologyπ i : K.cycles i ⟶ K.homology i`
for all `K : HomologicalComplex C c`. -/
@[simps]
noncomputable def natTransHomologyπ [CategoryWithHomology C] :
    cyclesFunctor C c i ⟶ homologyFunctor C c i where
  app K := K.homologyπ i

/-- The natural transformation `K.homologyι i : K.homology i ⟶ K.opcycles i`
for all `K : HomologicalComplex C c`. -/
@[simps]
noncomputable def natTransHomologyι [CategoryWithHomology C] :
    homologyFunctor C c i ⟶ opcyclesFunctor C c i where
  app K := K.homologyι i

/-- The natural isomorphism `K.homology i ≅ (K.sc i).homology`
for all homological complexes `K`. -/
@[simps!]
noncomputable def homologyFunctorIso [CategoryWithHomology C] :
    homologyFunctor C c i ≅
      shortComplexFunctor C c i ⋙ ShortComplex.homologyFunctor C :=
  Iso.refl _

/-- The natural isomorphism `K.homology j ≅ (K.sc' i j k).homology`
for all homological complexes `K` when `c.prev j = i` and `c.next j = k`. -/
noncomputable def homologyFunctorIso' [CategoryWithHomology C]
    (hi : c.prev j = i) (hk : c.next j = k) :
    homologyFunctor C c j ≅
      shortComplexFunctor' C c i j k ⋙ ShortComplex.homologyFunctor C :=
  homologyFunctorIso C c j ≪≫ isoWhiskerRight (natIsoSc' C c i j k hi hk) _

instance [CategoryWithHomology C] : (homologyFunctor C c i).PreservesZeroMorphisms where
instance [CategoryWithHomology C] : (opcyclesFunctor C c i).PreservesZeroMorphisms where
instance [CategoryWithHomology C] : (cyclesFunctor C c i).PreservesZeroMorphisms where

end

end

variable (K : HomologicalComplex C c) (i j k : ι)

section

variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]

lemma isIso_iCycles : IsIso (K.iCycles i) := by
  subst hj
  exact ShortComplex.isIso_iCycles _ h

/-- The canonical isomorphism `K.cycles i ≅ K.X i` when the differential from `i` is zero. -/
@[simps! hom]
noncomputable def iCyclesIso : K.cycles i ≅ K.X i :=
  have := K.isIso_iCycles i j hj h
  asIso (K.iCycles i)

@[reassoc (attr := simp)]
lemma iCyclesIso_hom_inv_id :
    K.iCycles i ≫ (K.iCyclesIso i j hj h).inv = 𝟙 _ :=
  (K.iCyclesIso i j hj h).hom_inv_id

@[reassoc (attr := simp)]
lemma iCyclesIso_inv_hom_id :
    (K.iCyclesIso i j hj h).inv ≫ K.iCycles i = 𝟙 _ :=
  (K.iCyclesIso i j hj h).inv_hom_id

lemma isIso_homologyι : IsIso (K.homologyι i) :=
  ShortComplex.isIso_homologyι _ (by aesop_cat)

/-- The canonical isomorphism `K.homology i ≅ K.opcycles i`
when the differential from `i` is zero. -/
@[simps! hom]
noncomputable def isoHomologyι : K.homology i ≅ K.opcycles i :=
>>>>>>> origin/homology-sequence-computation
  have := K.isIso_homologyι i j hj h
  asIso (K.homologyι i)

@[reassoc (attr := simp)]
<<<<<<< HEAD
lemma isoHomologyι_hom_inv_id (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    K.homologyι i ≫ (K.isoHomologyι i j hj h).inv = 𝟙 _ := (K.isoHomologyι i j hj h).hom_inv_id

@[reassoc (attr := simp)]
lemma isoHomologyι_inv_hom_id (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    (K.isoHomologyι i j hj h).inv ≫ K.homologyι i = 𝟙 _ := (K.isoHomologyι i j hj h).inv_hom_id

variable {K L}

noncomputable def homologyMapArrowIso (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
    Arrow.mk (homologyMap φ j) ≅
      Arrow.mk (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  refine' Arrow.isoMk
    (ShortComplex.homologyMapIso ((natIsoSc' C c i j k hi hk).app K))
    (ShortComplex.homologyMapIso ((natIsoSc' C c i j k hi hk).app L)) _
  dsimp [homologyMap]
  simp only [← ShortComplex.homologyMap_comp]
  congr 1
  exact ((natIsoSc' C c i j k hi hk).hom.naturality φ).symm

lemma isIso_homologyMap_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
  IsIso (homologyMap φ j) ↔
    IsIso (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  exact MorphismProperty.RespectsIso.arrow_mk_iso_iff
    (MorphismProperty.RespectsIso.isomorphisms C) (homologyMapArrowIso φ i j k hi hk)

lemma mono_homologyMap_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
  Mono (homologyMap φ j) ↔
    Mono (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  exact MorphismProperty.RespectsIso.arrow_mk_iso_iff
    (MorphismProperty.RespectsIso.monomorphisms C) (homologyMapArrowIso φ i j k hi hk)

lemma epi_homologyMap_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
  Epi (homologyMap φ j) ↔
    Epi (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  exact MorphismProperty.RespectsIso.arrow_mk_iso_iff
    (MorphismProperty.RespectsIso.epimorphisms C) (homologyMapArrowIso φ i j k hi hk)

lemma isIso_homologyMap_of_isIso_cyclesMap_of_epi (i j : ι) (hi : c.prev j = i)
    [K.HasHomology j] [L.HasHomology j]
    (h₁ : IsIso (cyclesMap φ j)) (h₂ : Epi (φ.f i)) :
    IsIso (homologyMap φ j) := by
  subst hi
  exact ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi h₁ h₂

lemma isIso_homologyMap_of_isIso_opcyclesMap_of_mono (i j : ι) (hj : c.next i = j)
    [K.HasHomology i] [L.HasHomology i]
    (h₁ : IsIso (opcyclesMap φ i)) (h₂ : Mono (φ.f j)) :
    IsIso (homologyMap φ i) := by
  subst hj
  exact ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono h₁ h₂

lemma isZero_homology_of_isZero (i : ι) (hi : IsZero (K.X i)) [K.HasHomology i]:
    IsZero (K.homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (by exact hi)

variable (C c)

def qis [CategoryWithHomology C] : MorphismProperty (HomologicalComplex C c) :=
  fun _ _ f => ∀ (i : ι), IsIso (homologyMap f i)

end HomologicalComplex

section

open HomologicalComplex CategoryTheory

variable {C : Type _} [Category C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}
  [DecidableRel c.Rel] {K L : HomologicalComplex C c} {f g : K ⟶ L}

noncomputable def Homotopy.toShortComplex (ho : Homotopy f g) (i : ι) :
    ShortComplex.Homotopy ((shortComplexFunctor C c i).map f)
      ((shortComplexFunctor C c i).map g) where
  h₀ :=
    if c.Rel (c.prev i) i
    then ho.hom _ (c.prev (c.prev i)) ≫ L.d _ _
    else f.f _ - g.f _ - K.d _ i ≫ ho.hom i _
  h₁ := ho.hom _ _
  h₂ := ho.hom _ _
  h₃ :=
    if c.Rel i (c.next i)
    then K.d _ _ ≫ ho.hom (c.next (c.next i)) _
    else f.f _ - g.f _ - ho.hom _ i ≫ L.d _ _
  h₀_f := by
    split_ifs with h
    · dsimp
      simp only [assoc, d_comp_d, comp_zero]
    · dsimp
      rw [L.shape _ _ h, comp_zero]
  g_h₃ := by
    split_ifs with h
    · dsimp
      simp
    · dsimp
      rw [K.shape _ _ h, zero_comp]
  comm₁ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.prev i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => d K (c.prev i) j ≫ ho.hom j (c.prev i)) (c.next_eq' h)]
    · abel
  comm₂ := ho.comm i
  comm₃ := by
    dsimp
    split_ifs with h
    · rw [ho.comm (c.next i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => ho.hom (c.next i) j ≫ L.d j (c.next i)) (c.prev_eq' h)]
    · abel

lemma Homotopy.homologyMap_eq (ho : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    homologyMap f i = homologyMap g i :=
  ShortComplex.Homotopy.congr_homologyMap (ho.toShortComplex i)

noncomputable def HomotopyEquiv.toHomologyIso (h : HomotopyEquiv K L) (i : ι)
  [K.HasHomology i] [L.HasHomology i] : K.homology i ≅ L.homology i where
  hom := homologyMap h.hom i
  inv := homologyMap h.inv i
  hom_inv_id := by rw [← homologyMap_comp, h.homotopyHomInvId.homologyMap_eq, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, h.homotopyInvHomId.homologyMap_eq, homologyMap_id]

namespace HomologicalComplex

variable (φ ψ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]

@[simp]
lemma homologyMap_neg : homologyMap (-φ) i = -homologyMap φ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_neg]
  rfl

@[simp]
lemma homologyMap_add : homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_add]
  rfl

@[simp]
lemma homologyMap_sub : homologyMap (φ - ψ) i = homologyMap φ i - homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_sub]
  rfl

instance [CategoryWithHomology C] : (homologyFunctor C c i).Additive where

variable (C c)

lemma homotopyEquivalences_subset_qis [CategoryWithHomology C] :
    homotopyEquivalences C c ⊆ qis C c := by
  rintro X Y _ ⟨e, rfl⟩ i
  exact IsIso.of_iso (e.toHomologyIso i)

end HomologicalComplex
=======
lemma isoHomologyι_hom_inv_id :
    K.homologyι i ≫ (K.isoHomologyι i j hj h).inv = 𝟙 _ :=
  (K.isoHomologyι i j hj h).hom_inv_id

@[reassoc (attr := simp)]
lemma isoHomologyι_inv_hom_id :
    (K.isoHomologyι i j hj h).inv ≫ K.homologyι i = 𝟙 _ :=
  (K.isoHomologyι i j hj h).inv_hom_id
>>>>>>> origin/homology-sequence-computation

end

section

<<<<<<< HEAD
variable {C : Type _} [Category C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable {ι : Type _} {c : ComplexShape ι}
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

section single

variable [HasZeroObject C] [DecidableEq ι] (c i)

instance (A : C) (j : ι): ((single C c i).obj A).HasHomology j :=
  ⟨⟨ShortComplex.HomologyData.ofZeros _ rfl rfl⟩⟩

instance (A : C) (j : ι) : ((single C c i).obj A).HasHomology j :=
  inferInstance

noncomputable def singleHomologyIso (A : C) : ((single C c i).obj A).homology i ≅ A :=
  (ShortComplex.HomologyData.ofZeros (sc ((single C c i).obj A) i) rfl rfl).left.homologyIso ≪≫
    singleObjXSelf C c i A

@[reassoc (attr := simp)]
lemma singleHomologyIso_hom_naturality {A B : C} (f : A ⟶ B) :
    homologyMap ((single C c i).map f) i ≫ (singleHomologyIso c i B).hom =
      (singleHomologyIso c i A).hom ≫ f := by
  dsimp only [singleHomologyIso, Iso.trans, homologyMap]
  simp [(ShortComplex.HomologyMapData.ofZeros
    ((shortComplexFunctor C c i).map ((single C c i).map f)) rfl rfl rfl rfl).left.homologyMap_eq]

variable (C)

@[simps!]
noncomputable def singleCompHomologyFunctorIso [CategoryWithHomology C] :
    single C c i ⋙ homologyFunctor C c i ≅ 𝟭 C :=
  NatIso.ofComponents (singleHomologyIso c i) (by aesop_cat)

lemma single_exactAt (A : C) (i j : ι) (hij : j ≠ i) :
    ((single C c i).obj A).ExactAt j := by
  rw [exactAt_iff, (ShortComplex.LeftHomologyData.ofZeros
    (sc ((single C c i).obj A) j) rfl rfl).exact_iff]
  dsimp
  rw [if_neg hij]
  exact Limits.isZero_zero C

end single

end HomologicalComplex

namespace ChainComplex

section

variable [HasZeroObject C]

instance single₀_obj_hasHomology (X : C) (j : ℕ) :
    ((single₀ C).obj X).HasHomology j :=
  ShortComplex.hasHomology_of_zeros _ _ _

lemma single₀_exactAt (X : C) (j : ℕ) :
    ((single₀ C).obj X).ExactAt j.succ := by
  rw [HomologicalComplex.exactAt_iff, (ShortComplex.LeftHomologyData.ofZeros
    (((single₀ C).obj X).sc j.succ) rfl rfl).exact_iff]
  dsimp
  exact Limits.isZero_zero C

@[simps!]
noncomputable def homologyDataSingle₀Obj (X : C) : (((single₀ C).obj X).sc 0).HomologyData :=
  ShortComplex.HomologyData.ofZeros _ rfl rfl

noncomputable def single₀Homology₀Iso (X : C) : ((single₀ C).obj X).homology 0 ≅ X :=
  (homologyDataSingle₀Obj X).left.homologyIso

lemma single₀HomologyIso_eq' (X : C) :
    single₀Homology₀Iso X = (homologyDataSingle₀Obj X).right.homologyIso := by
  ext
  simp [single₀Homology₀Iso,
    (homologyDataSingle₀Obj X).right_homologyIso_eq_left_homologyIso_trans_iso]

noncomputable def single₀Cycles₀Iso (X : C) : ((single₀ C).obj X).cycles 0 ≅ X :=
  (homologyDataSingle₀Obj X).left.cyclesIso

noncomputable def single₀Opcycles₀Iso (X : C) : ((single₀ C).obj X).opcycles 0 ≅ X :=
  (homologyDataSingle₀Obj X).right.opcyclesIso

@[reassoc (attr := simp)]
lemma single₀Cycles₀Iso_inv_comp_iCycles (X : C) :
  (single₀Cycles₀Iso X).inv ≫ ((single₀ C).obj X).iCycles 0 = 𝟙 _ :=
  (homologyDataSingle₀Obj X).left.cyclesIso_inv_comp_iCycles

@[reassoc (attr := simp)]
lemma single₀_homologyπ_comp_single₀Homology₀Iso_hom (X : C) :
    ((single₀ C).obj X).homologyπ 0 ≫ (single₀Homology₀Iso X).hom =
      (single₀Cycles₀Iso X).hom :=
    ((homologyDataSingle₀Obj X).left.homologyπ_comp_homologyIso_hom).trans (comp_id _)

@[reassoc (attr := simp)]
lemma pOpcycles_comp_single₀OpcyclesIso_hom (X : C) :
    ((ChainComplex.single₀ C).obj X).pOpcycles 0 ≫ (single₀Opcycles₀Iso X).hom = 𝟙 _ :=
  (homologyDataSingle₀Obj X).right.pOpcycles_comp_opcyclesIso_hom

@[reassoc (attr := simp)]
lemma single₀Homology₀Iso_inv_comp_single₀_homologyι (X : C) :
  (single₀Homology₀Iso X).inv ≫ ((single₀ C).obj X).homologyι 0 =
    (single₀Opcycles₀Iso X).inv := by
  rw [single₀HomologyIso_eq']
  refine' ((homologyDataSingle₀Obj X).right.homologyIso_inv_comp_homologyι).trans _
  simp
  rfl

@[reassoc (attr := simp)]
lemma single₀Cycles₀Iso_hom_naturality {A B : C} (f : A ⟶ B) :
    HomologicalComplex.cyclesMap ((single₀ C).map f) 0 ≫ (single₀Cycles₀Iso B).hom =
      (single₀Cycles₀Iso A).hom ≫ f := by
  simp only [← cancel_mono (single₀Cycles₀Iso B).inv, assoc, Iso.hom_inv_id,
    comp_id, ← cancel_mono (HomologicalComplex.iCycles _ _),
    HomologicalComplex.cyclesMap_i, single₀_map_f_0,
    single₀Cycles₀Iso_inv_comp_iCycles, comp_id,
    ← cancel_epi (single₀Cycles₀Iso A).inv, Iso.inv_hom_id_assoc,
    single₀Cycles₀Iso_inv_comp_iCycles_assoc]

@[reassoc (attr := simp)]
lemma single₀Homology₀Iso_hom_naturality {A B : C} (f : A ⟶ B) :
    HomologicalComplex.homologyMap ((single₀ C).map f) 0 ≫ (single₀Homology₀Iso B).hom =
      (single₀Homology₀Iso A).hom ≫ f := by
  simp only [← cancel_epi (HomologicalComplex.homologyπ _ _),
    HomologicalComplex.homologyπ_naturality_assoc,
    single₀_homologyπ_comp_single₀Homology₀Iso_hom, single₀Cycles₀Iso_hom_naturality,
    single₀_homologyπ_comp_single₀Homology₀Iso_hom_assoc]

variable (C)

noncomputable def single₀CompCyclesFunctor₀Iso [CategoryWithHomology C] :
    single₀ C ⋙ HomologicalComplex.cyclesFunctor _ _ 0 ≅ 𝟭 C :=
  NatIso.ofComponents single₀Cycles₀Iso (by aesop_cat)

noncomputable def single₀CompHomologyFunctor₀Iso [CategoryWithHomology C] :
    single₀ C ⋙ HomologicalComplex.homologyFunctor _ _ 0 ≅ 𝟭 C :=
  NatIso.ofComponents single₀Homology₀Iso (by aesop_cat)

end

@[simp]
lemma d_zero_eq_zero (K : ChainComplex C ℕ) (i : ℕ) : K.d 0 i = 0 :=
  K.shape _ _ (by dsimp; linarith)

instance isIso_homologyι₀ (K : ChainComplex C ℕ) [K.HasHomology 0] :
    IsIso (K.homologyι 0) :=
  ShortComplex.isIso_homologyι _ (by aesop_cat)

@[simps! hom]
noncomputable def isoHomologyι₀ (K : ChainComplex C ℕ) [K.HasHomology 0] :
    K.homology 0 ≅ K.opcycles 0 :=
  asIso (K.homologyι 0)

@[reassoc (attr := simp)]
lemma isoHomologyι₀_hom_inv_id (K : ChainComplex C ℕ) [K.HasHomology 0] :
    K.homologyι 0 ≫ K.isoHomologyι₀.inv = 𝟙 _ := K.isoHomologyι₀.hom_inv_id

@[reassoc (attr := simp)]
lemma isoHomologyι₀_inv_hom_id (K : ChainComplex C ℕ) [K.HasHomology 0] :
    K.isoHomologyι₀.inv ≫ K.homologyι 0 = 𝟙 _ := K.isoHomologyι₀.inv_hom_id

@[reassoc (attr := simp)]
lemma isoHomologyι₀_inv_naturality {K L : ChainComplex C ℕ} (φ : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] :
    K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.opcyclesMap φ 0 ≫ L.isoHomologyι₀.inv := by
  simp only [assoc, ← cancel_mono (L.homologyι 0), ← cancel_epi (K.homologyι 0),
    HomologicalComplex.homologyι_naturality, isoHomologyι₀_inv_hom_id_assoc,
    isoHomologyι₀_inv_hom_id, comp_id]

section Abelian

variable {A : Type _} [Category A] [Abelian A]

lemma isIso_descOpcycles_iff (K : ChainComplex A ℕ) {X : A} (φ : K.X 0 ⟶ X)
    [K.HasHomology 0] (hφ : K.d 1 0 ≫ φ = 0) :
    IsIso (K.descOpcycles φ 1 (by simp) hφ) ↔
      Epi φ ∧ (ShortComplex.mk _ _ hφ).Exact := by
  suffices ∀ (i : ℕ) (hx : (ComplexShape.down ℕ).prev 0 = i)
    (hφ : K.d i 0 ≫ φ = 0), IsIso (K.descOpcycles φ i hx hφ) ↔
      Epi φ ∧ (ShortComplex.mk _ _ hφ).Exact from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : K.sc 0 ⟶ ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) :=
      { τ₁ := 0
        τ₂ := φ
        τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_descOpcycles α (by simp) rfl rfl).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros' α (by simp) rfl rfl)

end Abelian


end ChainComplex

namespace CochainComplex

section

variable [HasZeroObject C]

instance single₀_obj_hasHomology (X : C) (j : ℕ) :
    ((single₀ C).obj X).HasHomology j :=
  ShortComplex.hasHomology_of_zeros _ _ _

lemma single₀_exactAt (X : C) (j : ℕ) :
    ((single₀ C).obj X).ExactAt j.succ := by
  rw [HomologicalComplex.exactAt_iff, (ShortComplex.LeftHomologyData.ofZeros
    (((single₀ C).obj X).sc j.succ) rfl rfl).exact_iff]
  dsimp
  exact Limits.isZero_zero C

noncomputable def homologyDataSingle₀Obj (X : C) : (((single₀ C).obj X).sc 0).HomologyData :=
  ShortComplex.HomologyData.ofZeros _ rfl rfl

noncomputable def single₀Homology₀Iso (X : C) : ((single₀ C).obj X).homology 0 ≅ X :=
  (homologyDataSingle₀Obj X).left.homologyIso

noncomputable def single₀Cycles₀Iso (X : C) : ((single₀ C).obj X).cycles 0 ≅ X :=
  (homologyDataSingle₀Obj X).left.cyclesIso

@[reassoc (attr := simp)]
lemma single₀Cycles₀Iso_inv_comp_iCycles (X : C) :
  (single₀Cycles₀Iso X).inv ≫ ((single₀ C).obj X).iCycles 0 = 𝟙 _ :=
  (homologyDataSingle₀Obj X).left.cyclesIso_inv_comp_iCycles

@[reassoc (attr := simp)]
lemma single₀_homologyπ_comp_single₀Homology₀Iso_hom (X : C) :
    ((single₀ C).obj X).homologyπ 0 ≫ (single₀Homology₀Iso X).hom =
      (single₀Cycles₀Iso X).hom :=
    ((homologyDataSingle₀Obj X).left.homologyπ_comp_homologyIso_hom).trans (comp_id _)

@[reassoc (attr := simp)]
lemma single₀Cycles₀Iso_hom_naturality {A B : C} (f : A ⟶ B) :
    HomologicalComplex.cyclesMap ((single₀ C).map f) 0 ≫ (single₀Cycles₀Iso B).hom =
      (single₀Cycles₀Iso A).hom ≫ f := by
  simp only [← cancel_mono (single₀Cycles₀Iso B).inv, assoc, Iso.hom_inv_id,
    comp_id, ← cancel_mono (HomologicalComplex.iCycles _ _),
    HomologicalComplex.cyclesMap_i, single₀_map_f_0,
    single₀Cycles₀Iso_inv_comp_iCycles, comp_id,
    ← cancel_epi (single₀Cycles₀Iso A).inv, Iso.inv_hom_id_assoc,
    single₀Cycles₀Iso_inv_comp_iCycles_assoc]

@[reassoc (attr := simp)]
lemma single₀Homology₀Iso_hom_naturality {A B : C} (f : A ⟶ B) :
    HomologicalComplex.homologyMap ((single₀ C).map f) 0 ≫ (single₀Homology₀Iso B).hom =
      (single₀Homology₀Iso A).hom ≫ f := by
  simp only [← cancel_epi (HomologicalComplex.homologyπ _ _),
    HomologicalComplex.homologyπ_naturality_assoc,
    single₀_homologyπ_comp_single₀Homology₀Iso_hom, single₀Cycles₀Iso_hom_naturality,
    single₀_homologyπ_comp_single₀Homology₀Iso_hom_assoc]

variable (C)

noncomputable def single₀CompCyclesFunctor₀Iso [CategoryWithHomology C] :
    single₀ C ⋙ HomologicalComplex.cyclesFunctor _ _ 0 ≅ 𝟭 C :=
  NatIso.ofComponents single₀Cycles₀Iso (by aesop_cat)

noncomputable def single₀CompHomologyFunctor₀Iso [CategoryWithHomology C] :
    single₀ C ⋙ HomologicalComplex.homologyFunctor _ _ 0 ≅ 𝟭 C :=
  NatIso.ofComponents single₀Homology₀Iso (by aesop_cat)

end

@[simp]
lemma d_zero_eq_zero (K : CochainComplex C ℕ) (i : ℕ) : K.d i 0 = 0 :=
  K.shape _ _ (by dsimp; linarith)

instance isIso_homologyπ₀ (K : CochainComplex C ℕ) [K.HasHomology 0] :
    IsIso (K.homologyπ 0) :=
  ShortComplex.isIso_homologyπ _ (by aesop_cat)

@[simps! hom]
noncomputable def isoHomologyπ₀ (K : CochainComplex C ℕ) [K.HasHomology 0] :
    K.cycles 0 ≅ K.homology 0 :=
  asIso (K.homologyπ 0)

@[reassoc (attr := simp)]
lemma isoHomologyπ₀_hom_inv_id (K : CochainComplex C ℕ) [K.HasHomology 0] :
    K.homologyπ 0 ≫ K.isoHomologyπ₀.inv = 𝟙 _ := K.isoHomologyπ₀.hom_inv_id

@[reassoc (attr := simp)]
lemma isoHomologyπ₀_inv_hom_id (K : CochainComplex C ℕ) [K.HasHomology 0] :
    K.isoHomologyπ₀.inv ≫ K.homologyπ 0 = 𝟙 _ := K.isoHomologyπ₀.inv_hom_id

@[reassoc (attr := simp)]
lemma isoHomologyπ₀_inv_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] :
    HomologicalComplex.homologyMap φ 0 ≫ L.isoHomologyπ₀.inv =
      K.isoHomologyπ₀.inv ≫ HomologicalComplex.cyclesMap φ 0 := by
  simp only [← cancel_mono (L.homologyπ 0), ← cancel_epi (K.homologyπ 0),
    assoc, isoHomologyπ₀_inv_hom_id, comp_id, HomologicalComplex.homologyπ_naturality,
    isoHomologyπ₀_hom_inv_id_assoc]

section Abelian

variable {A : Type _} [Category A] [Abelian A]

lemma isIso_liftCycles_iff (K : CochainComplex A ℕ) {X : A} (φ : X ⟶ K.X 0)
    [K.HasHomology 0] (hφ : φ ≫ K.d 0 1 = 0) :
    IsIso (K.liftCycles φ 1 (by simp) hφ) ↔
      Mono φ ∧ (ShortComplex.mk _ _ hφ).Exact := by
  suffices ∀ (i : ℕ) (hx : (ComplexShape.up ℕ).next 0 = i)
    (hφ : φ ≫ K.d 0 i = 0), IsIso (K.liftCycles φ i hx hφ) ↔
      Mono φ ∧ (ShortComplex.mk _ _ hφ).Exact from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) ⟶
    K.sc 0 :=
      { τ₁ := 0
        τ₂ := φ
        τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_liftCycles α rfl rfl (by simp)).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros α rfl rfl (by simp))

end Abelian

end CochainComplex

end

namespace HomologicalComplex

variable {C : Type _} [Category C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

def sc'OpIso (i j k : ι) : K.op.sc' i j k ≅ (K.sc' k j i).op :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by aesop_cat) (by aesop_cat)

noncomputable def scOpIso (i : ι) : K.op.sc i ≅ (K.sc i).op := K.sc'OpIso  _ _ _

noncomputable def homologyOpIso (i : ι) [K.HasHomology i]
  [K.HasHomology i] [K.op.HasHomology i] :
  K.op.homology i ≅ Opposite.op (K.homology i) :=
  (K.sc i).homologyOpIso

noncomputable def homologyUnopIso (K : HomologicalComplex Cᵒᵖ c) (i : ι)
    [K.HasHomology i] [K.unop.HasHomology i] :
    Opposite.unop (K.homology i) ≅ K.unop.homology i := by
  have : K.unop.op.HasHomology i := (inferInstance : K.HasHomology i)
  exact (K.unop.homologyOpIso i).unop.symm

end HomologicalComplex

namespace HomotopyCategory

variable (C : Type _) [Category C] [Preadditive C] {ι : Type _} (c : ComplexShape ι)
  [DecidableRel c.Rel] [CategoryWithHomology C]

noncomputable def homologyFunctor (i : ι) : HomotopyCategory C c ⥤ C :=
  CategoryTheory.Quotient.lift _ (HomologicalComplex.homologyFunctor C c i) (by
    rintro K L f g ⟨h⟩
    exact h.homologyMap_eq i)

noncomputable def homologyFunctorFactors (i : ι) :
    quotient C c ⋙ homologyFunctor C c i ≅
      HomologicalComplex.homologyFunctor C c i :=
  Quotient.lift.isLift _ _ _

-- this is to prevent any abuse of defeq
attribute [irreducible] homologyFunctor homologyFunctorFactors

instance (i : ι) : (homologyFunctor C c i).Additive := by
  have := Functor.additive_of_iso (homologyFunctorFactors C c i).symm
  exact Functor.additive_of_full_essSurj_comp (quotient C c) _

end HomotopyCategory

namespace HomologicalComplex

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  (K : HomologicalComplex C c)

lemma comp_homologyπ_eq_zero_iff_up_to_refinements {A : C} {i : ι} (z : A ⟶ K.cycles i) (j : ι) (hj : c.prev i = j) :
    z ≫ K.homologyπ i = 0 ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ K.X j), π ≫ z = x ≫ K.toCycles j i := by
  subst hj
  apply ShortComplex.comp_homologyπ_eq_zero_iff_up_to_refinements

lemma comp_pOpcycles_eq_zero_iff_up_to_refinements {A : C} {i : ι} (z : A ⟶ K.X i) (j : ι) (hj : c.prev i = j) :
      z ≫ K.pOpcycles i = 0 ↔
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ K.X j), π ≫ z = x ≫ K.d j i := by
  subst hj
  apply (K.sc i).comp_pOpcycles_eq_zero_iff_up_to_refinements
=======
variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]

lemma isIso_pOpcycles : IsIso (K.pOpcycles j) := by
  obtain rfl := hi
  exact ShortComplex.isIso_pOpcycles _ h

/-- The canonical isomorphism `K.X j ≅ K.opCycles j` when the differential to `j` is zero. -/
@[simps! hom]
noncomputable def pOpcyclesIso : K.X j ≅ K.opcycles j :=
  have := K.isIso_pOpcycles i j hi h
  asIso (K.pOpcycles j)

@[reassoc (attr := simp)]
lemma pOpcyclesIso_hom_inv_id :
    K.pOpcycles j ≫ (K.pOpcyclesIso i j hi h).inv = 𝟙 _ :=
  (K.pOpcyclesIso i j hi h).hom_inv_id

@[reassoc (attr := simp)]
lemma pOpcyclesIso_inv_hom_id :
    (K.pOpcyclesIso i j hi h).inv ≫ K.pOpcycles j = 𝟙 _ :=
  (K.pOpcyclesIso i j hi h).inv_hom_id

lemma isIso_homologyπ : IsIso (K.homologyπ j) :=
  ShortComplex.isIso_homologyπ _ (by aesop_cat)

/-- The canonical isomorphism `K.cycles j ≅ K.homology j`
when the differential to `j` is zero. -/
@[simps! hom]
noncomputable def isoHomologyπ : K.cycles j ≅ K.homology j :=
  have := K.isIso_homologyπ i j hi h
  asIso (K.homologyπ j)

@[reassoc (attr := simp)]
lemma isoHomologyπ_hom_inv_id :
    K.homologyπ j ≫ (K.isoHomologyπ i j hi h).inv = 𝟙 _ :=
  (K.isoHomologyπ i j hi h).hom_inv_id

@[reassoc (attr := simp)]
lemma isoHomologyπ_inv_hom_id :
    (K.isoHomologyπ i j hi h).inv ≫ K.homologyπ j = 𝟙 _ :=
  (K.isoHomologyπ i j hi h).inv_hom_id

end

/-- A homological complex `K` is exact at `i` if the short complex `K.sc i` is exact. -/
def ExactAt := (K.sc i).Exact

lemma exactAt_iff :
    K.ExactAt i ↔ (K.sc i).Exact := by rfl

lemma exactAt_iff' (hi : c.prev j = i) (hk : c.next j = k) :
    K.ExactAt j ↔ (K.sc' i j k).Exact :=
  ShortComplex.exact_iff_of_iso (K.isoSc' i j k hi hk)

lemma exactAt_iff_isZero_homology [K.HasHomology i] :
    K.ExactAt i ↔ IsZero (K.homology i) := by
  dsimp [homology]
  rw [exactAt_iff, ShortComplex.exact_iff_isZero_homology]
>>>>>>> origin/homology-sequence-computation

end HomologicalComplex

namespace ChainComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : ChainComplex C ℕ) (φ : K ⟶ L) [K.HasHomology 0]

instance isIso_homologyι₀ :
    IsIso (K.homologyι 0) :=
  K.isIso_homologyι 0 _ rfl (by simp)

/-- The canonical isomorphism `K.homology 0 ≅ K.opcycles 0` for a chain complex `K`
indexed by `ℕ`. -/
noncomputable abbrev isoHomologyι₀ :
  K.homology 0 ≅ K.opcycles 0 := K.isoHomologyι 0 _ rfl (by simp)

variable {K L}

@[reassoc (attr := simp)]
lemma isoHomologyι₀_inv_naturality [L.HasHomology 0] :
    K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.opcyclesMap φ 0 ≫ L.isoHomologyι₀.inv := by
  simp only [assoc, ← cancel_mono (L.homologyι 0),
    HomologicalComplex.homologyι_naturality, HomologicalComplex.isoHomologyι_inv_hom_id_assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id, comp_id]

end ChainComplex

namespace CochainComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : CochainComplex C ℕ) (φ : K ⟶ L) [K.HasHomology 0]

instance isIso_homologyπ₀ :
    IsIso (K.homologyπ 0) :=
  K.isIso_homologyπ _ 0 rfl (by simp)

/-- The canonical isomorphism `K.cycles 0 ≅ K.homology 0` for a cochain complex `K`
indexed by `ℕ`. -/
noncomputable abbrev isoHomologyπ₀ :
  K.cycles 0 ≅ K.homology 0 := K.isoHomologyπ _ 0 rfl (by simp)

variable {K L}

@[reassoc (attr := simp)]
lemma isoHomologyπ₀_inv_naturality [L.HasHomology 0] :
    HomologicalComplex.homologyMap φ 0 ≫ L.isoHomologyπ₀.inv =
      K.isoHomologyπ₀.inv ≫ HomologicalComplex.cyclesMap φ 0 := by
  simp only [← cancel_epi (K.homologyπ 0), HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id, comp_id,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]

end CochainComplex

namespace HomologicalComplex

variable {C ι : Type*} [Category C] [Preadditive C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

variable (φ ψ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]

@[simp]
lemma homologyMap_neg : homologyMap (-φ) i = -homologyMap φ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_neg]
  rfl

@[simp]
lemma homologyMap_add : homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_add]
  rfl

@[simp]
lemma homologyMap_sub : homologyMap (φ - ψ) i = homologyMap φ i - homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_sub]
  rfl

instance [CategoryWithHomology C] : (homologyFunctor C c i).Additive where

end HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]

lemma isIso_liftCycles_iff (K : CochainComplex C ℕ) {X : C} (φ : X ⟶ K.X 0)
    [K.HasHomology 0] (hφ : φ ≫ K.d 0 1 = 0) :
    IsIso (K.liftCycles φ 1 (by simp) hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ := by
  suffices ∀ (i : ℕ) (hx : (ComplexShape.up ℕ).next 0 = i)
    (hφ : φ ≫ K.d 0 i = 0), IsIso (K.liftCycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) ⟶ K.sc 0 :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_liftCycles α rfl rfl (by simp)).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros α rfl rfl (by simp))

end CochainComplex

namespace ChainComplex

variable {C : Type*} [Category C] [Abelian C]

lemma isIso_descOpcycles_iff (K : ChainComplex C ℕ) {X : C} (φ : K.X 0 ⟶ X)
    [K.HasHomology 0] (hφ : K.d 1 0 ≫ φ = 0) :
    IsIso (K.descOpcycles φ 1 (by simp) hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ := by
  suffices ∀ (i : ℕ) (hx : (ComplexShape.down ℕ).prev 0 = i)
    (hφ : K.d i 0 ≫ φ = 0), IsIso (K.descOpcycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : K.sc 0 ⟶ ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_descOpcycles α (by simp) rfl rfl).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros' α (by simp) rfl rfl)

end ChainComplex
