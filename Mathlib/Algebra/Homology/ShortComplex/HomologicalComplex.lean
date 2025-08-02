/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Tactic.Linarith

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

open CategoryTheory Category Limits

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

/-- The natural isomorphism `shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k`
when `c.prev j = i` and `c.next j = k`. -/
@[simps!]
noncomputable def natIsoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by simp) (by simp)) (by aesop_cat)

variable {C c}

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

/-- The short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
abbrev sc' := (shortComplexFunctor' C c i j k).obj K

/-- The short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
noncomputable abbrev sc := (shortComplexFunctor C c i).obj K

/-- The canonical isomorphism `K.sc j ≅ K.sc' i j k` when `c.prev j = i` and `c.next j = k`. -/
noncomputable abbrev isoSc' (hi : c.prev j = i) (hk : c.next j = k) :
    K.sc j ≅ K.sc' i j k := (natIsoSc' C c i j k hi hk).app K

/-- A homological complex `K` has homology in degree `i` if the associated
short complex `K.sc i` has. -/
abbrev HasHomology := (K.sc i).HasHomology

variable {K L} in
include iso in
lemma hasHomology_of_iso [K.HasHomology i] : L.HasHomology i :=
  ShortComplex.hasHomology_of_iso
    ((shortComplexFunctor _ _ i).mapIso iso : K.sc i ≅ L.sc i)

section

variable [K.HasHomology i]

/-- The homology in degree `i` of a homological complex. -/
noncomputable def homology := (K.sc i).homology

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
noncomputable abbrev liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
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

end

@[reassoc (attr := simp)]
lemma toCycles_i [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j :=
  liftCycles_i _ _ _ _ _

section
variable [K.HasHomology i]

instance : Mono (K.iCycles i) := by
  dsimp only [iCycles]
  infer_instance

instance : Epi (K.homologyπ i) := by
  dsimp only [homologyπ]
  infer_instance

end

@[reassoc (attr := simp)]
lemma d_toCycles [K.HasHomology k] :
    K.d i j ≫ K.toCycles j k = 0 := by
  simp only [← cancel_mono (K.iCycles k), assoc, toCycles_i, d_comp_d, zero_comp]

variable {i j} in
lemma toCycles_eq_zero [K.HasHomology j] (hij : ¬ c.Rel i j) :
    K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), toCycles_i, zero_comp, K.shape _ _ hij]

variable {i}

section
variable [K.HasHomology i]

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

end

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
  exact (K.sc j).homologyIsCokernel

section
variable [K.HasHomology i]

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
noncomputable abbrev descOpcycles' {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  K.descOpcycles k j (c.prev_eq' hj) hk

@[reassoc (attr := simp)]
lemma p_descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpcycles k j hj hk = k := by
  dsimp [descOpcycles, pOpcycles]
  simp

variable (i)

/-- The map `K.opcycles i ⟶ K.X j` induced by the differential `K.d i j`. -/
noncomputable def fromOpcycles : K.opcycles i ⟶ K.X j  :=
  K.descOpcycles (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

omit [K.HasHomology i] in
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

variable {i j} in
lemma fromOpcycles_eq_zero (hij : ¬ c.Rel i j) :
    K.fromOpcycles i j = 0 := by
  rw [← cancel_epi (K.pOpcycles i), p_fromOpcycles, comp_zero, K.shape _ _ hij]

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

/-- The isomorphism `K.homology i ≅ L.homology i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
noncomputable def homologyMapIso : K.homology i ≅ L.homology i where
  hom := homologyMap iso.hom i
  inv := homologyMap iso.inv i
  hom_inv_id := by simp [← homologyMap_comp]
  inv_hom_id := by simp [← homologyMap_comp]

/-- The isomorphism `K.cycles i ≅ L.cycles i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
noncomputable def cyclesMapIso : K.cycles i ≅ L.cycles i where
  hom := cyclesMap iso.hom i
  inv := cyclesMap iso.inv i
  hom_inv_id := by simp [← cyclesMap_comp]
  inv_hom_id := by simp [← cyclesMap_comp]

/-- The isomorphism `K.opcycles i ≅ L.opcycles i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
noncomputable def opcyclesMapIso : K.opcycles i ≅ L.opcycles i where
  hom := opcyclesMap iso.hom i
  inv := opcyclesMap iso.inv i
  hom_inv_id := by simp [← opcyclesMap_comp]
  inv_hom_id := by simp [← opcyclesMap_comp]

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
  homologyFunctorIso C c j ≪≫ Functor.isoWhiskerRight (natIsoSc' C c i j k hi hk) _

instance [CategoryWithHomology C] : (homologyFunctor C c i).PreservesZeroMorphisms where
instance [CategoryWithHomology C] : (opcyclesFunctor C c i).PreservesZeroMorphisms where
instance [CategoryWithHomology C] : (cyclesFunctor C c i).PreservesZeroMorphisms where

end

end

section

variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]
include hj h

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
  have := K.isIso_homologyι i j hj h
  asIso (K.homologyι i)

@[reassoc (attr := simp)]
lemma isoHomologyι_hom_inv_id :
    K.homologyι i ≫ (K.isoHomologyι i j hj h).inv = 𝟙 _ :=
  (K.isoHomologyι i j hj h).hom_inv_id

@[reassoc (attr := simp)]
lemma isoHomologyι_inv_hom_id :
    (K.isoHomologyι i j hj h).inv ≫ K.homologyι i = 𝟙 _ :=
  (K.isoHomologyι i j hj h).inv_hom_id

end

section

variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]
include hi h

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

section

variable {K L}

lemma epi_homologyMap_of_epi_of_not_rel (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [Epi (φ.f i)] (hi : ∀ j, ¬ c.Rel i j) :
    Epi (homologyMap φ i) :=
  ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyι i _ rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyι i _ rfl (shape _ _ _ (by tauto))))).2
      (MorphismProperty.epimorphisms.infer_property (opcyclesMap φ i))

lemma mono_homologyMap_of_mono_of_not_rel (φ : K ⟶ L) (j : ι)
    [K.HasHomology j] [L.HasHomology j] [Mono (φ.f j)] (hj : ∀ i, ¬ c.Rel i j) :
    Mono (homologyMap φ j) :=
  ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyπ _ j rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyπ _ j rfl (shape _ _ _ (by tauto))))).1
      (MorphismProperty.monomorphisms.infer_property (cyclesMap φ j))

end

/-- A homological complex `K` is exact at `i` if the short complex `K.sc i` is exact. -/
def ExactAt := (K.sc i).Exact

lemma exactAt_iff :
    K.ExactAt i ↔ (K.sc i).Exact := by rfl

variable {K i} in
lemma ExactAt.of_iso (hK : K.ExactAt i) {L : HomologicalComplex C c} (e : K ≅ L) :
    L.ExactAt i := by
  rw [exactAt_iff] at hK ⊢
  exact ShortComplex.exact_of_iso ((shortComplexFunctor C c i).mapIso e) hK

lemma exactAt_iff' (hi : c.prev j = i) (hk : c.next j = k) :
    K.ExactAt j ↔ (K.sc' i j k).Exact :=
  ShortComplex.exact_iff_of_iso (K.isoSc' i j k hi hk)

lemma exactAt_iff_isZero_homology [K.HasHomology i] :
    K.ExactAt i ↔ IsZero (K.homology i) := by
  dsimp [homology]
  rw [exactAt_iff, ShortComplex.exact_iff_isZero_homology]

variable {K i} in
lemma ExactAt.isZero_homology [K.HasHomology i] (h : K.ExactAt i) :
    IsZero (K.homology i) := by
  rwa [← exactAt_iff_isZero_homology]

/-- A homological complex `K` is acyclic if it is exact at `i` for any `i`. -/
def Acyclic := ∀ i, K.ExactAt i

lemma acyclic_iff :
    K.Acyclic ↔ ∀ i, K.ExactAt i := by rfl

lemma acyclic_of_isZero (hK : IsZero K) :
    K.Acyclic := by
  rw [acyclic_iff]
  intro i
  apply ShortComplex.exact_of_isZero_X₂
  exact (eval _ _ i).map_isZero hK

end HomologicalComplex

namespace ChainComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : ChainComplex C ℕ) (φ : K ⟶ L) [K.HasHomology 0]

instance isIso_homologyι₀ :
    IsIso (K.homologyι 0) :=
  K.isIso_homologyι 0 _ rfl (by simp)

/-- The canonical isomorphism `K.homology 0 ≅ K.opcycles 0` for a chain complex `K`
indexed by `ℕ`. -/
noncomputable abbrev isoHomologyι₀ : K.homology 0 ≅ K.opcycles 0 :=
  K.isoHomologyι 0 _ rfl (by simp)

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
noncomputable abbrev isoHomologyπ₀ : K.cycles 0 ≅ K.homology 0 :=
  K.isoHomologyπ _ 0 rfl (by simp)

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

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

/-- The cycles of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`. -/
noncomputable def cyclesIsoSc' : K.cycles j ≅ (K.sc' i j k).cycles :=
  ShortComplex.cyclesMapIso (K.isoSc' i j k hi hk)

@[reassoc (attr := simp)]
lemma cyclesIsoSc'_hom_iCycles :
    (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).iCycles = K.iCycles j := by
  dsimp [cyclesIsoSc']
  simp only [ShortComplex.cyclesMap_i, shortComplexFunctor_obj_X₂, shortComplexFunctor'_obj_X₂,
    natIsoSc'_hom_app_τ₂, comp_id]
  rfl

@[reassoc (attr := simp)]
lemma cyclesIsoSc'_inv_iCycles :
    (K.cyclesIsoSc' i j k hi hk).inv ≫ K.iCycles j = (K.sc' i j k).iCycles := by
  dsimp [cyclesIsoSc']
  erw [ShortComplex.cyclesMap_i]
  apply comp_id

@[reassoc (attr := simp)]
lemma toCycles_cyclesIsoSc'_hom :
    K.toCycles i j ≫ (K.cyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).toCycles := by
  simp only [← cancel_mono (K.sc' i j k).iCycles, assoc, cyclesIsoSc'_hom_iCycles,
    toCycles_i, ShortComplex.toCycles_i, shortComplexFunctor'_obj_f]

/-- The homology of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`. -/
noncomputable def opcyclesIsoSc' : K.opcycles j ≅ (K.sc' i j k).opcycles :=
  ShortComplex.opcyclesMapIso (K.isoSc' i j k hi hk)

@[reassoc (attr := simp)]
lemma pOpcycles_opcyclesIsoSc'_inv :
    (K.sc' i j k).pOpcycles ≫ (K.opcyclesIsoSc' i j k hi hk).inv = K.pOpcycles j := by
  dsimp [opcyclesIsoSc']
  simp only [ShortComplex.p_opcyclesMap, shortComplexFunctor'_obj_X₂, shortComplexFunctor_obj_X₂,
    natIsoSc'_inv_app_τ₂, id_comp]
  rfl

@[reassoc (attr := simp)]
lemma pOpcycles_opcyclesIsoSc'_hom :
    K.pOpcycles j ≫ (K.opcyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).pOpcycles := by
  dsimp [opcyclesIsoSc']
  erw [ShortComplex.p_opcyclesMap]
  apply id_comp

@[reassoc (attr := simp)]
lemma opcyclesIsoSc'_inv_fromOpcycles :
    (K.opcyclesIsoSc' i j k hi hk).inv ≫ K.fromOpcycles j k =
      (K.sc' i j k).fromOpcycles := by
  simp only [← cancel_epi (K.sc' i j k).pOpcycles, pOpcycles_opcyclesIsoSc'_inv_assoc,
    p_fromOpcycles, ShortComplex.p_fromOpcycles, shortComplexFunctor'_obj_g]

/-- The opcycles of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`. -/
noncomputable def homologyIsoSc' : K.homology j ≅ (K.sc' i j k).homology :=
  ShortComplex.homologyMapIso (K.isoSc' i j k hi hk)

@[reassoc (attr := simp)]
lemma π_homologyIsoSc'_hom :
    K.homologyπ j ≫ (K.homologyIsoSc' i j k hi hk).hom =
      (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyπ := by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]
lemma π_homologyIsoSc'_inv :
    (K.sc' i j k).homologyπ ≫ (K.homologyIsoSc' i j k hi hk).inv =
      (K.cyclesIsoSc' i j k hi hk).inv ≫ K.homologyπ j := by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]
lemma homologyIsoSc'_hom_ι :
    (K.homologyIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyι =
      K.homologyι j ≫ (K.opcyclesIsoSc' i j k hi hk).hom := by
  apply ShortComplex.homologyι_naturality

@[reassoc (attr := simp)]
lemma homologyIsoSc'_inv_ι :
    (K.homologyIsoSc' i j k hi hk).inv ≫ K.homologyι j =
      (K.sc' i j k).homologyι ≫ (K.opcyclesIsoSc' i j k hi hk).inv := by
  apply ShortComplex.homologyι_naturality

end HomologicalComplex
