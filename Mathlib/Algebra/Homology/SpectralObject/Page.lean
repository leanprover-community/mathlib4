/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ExactSequenceFour
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Spectral objects in abelian categories

Let `X` be a spectral object index by the category `ι`
in the abelian category `C`. The purpose of this file
is two introduce the homology `X.E` of the short complex `X.shortComplexE`
`(X.H n₀).obj (mk₁ f₃) ⟶ (X.H n₁).obj (mk₁ f₂) ⟶ (X.H n₂).obj (mk₁ f₁)`
when `f₁`, `f₂` and `f₃` are composable morphisms in `ι` and the
equalities `n₀ + 1 = n₁` and `n₁ + 1 = n₂` hold (both maps in the
short complex are given by `X.δ`). All the relevant objects in the
spectral sequence attached to spectral objects can be defined
in terms of this homology `X.E`: the objects in all pages, including
the page at infinity.

In order to study this homology, we introduce objects `X.cycles`
for the kernel of `δ` and `X.opcycles` for its cokernel. We record
the obvious exact sequences that are part of this definition
as the lemmas `kernelSequenceCycles_exact`
and `cokernelSequenceOpcycles_exact`, and constructor for morphisms
`X.liftCycles` to cycles and `X.descOpcycles` from opcycles.
The definitions `cyclesMap` and `opcyclesMap` give the functoriality
with respect to `ComposableArrows ι 2`.

The fact that the morphisms `δ` are part of a long exact sequence allow
to show that `X.cycles` also identify to a cokernel (`cokernelIsoCycles`)
and `X.opcycles` to a kernel (`opcyclesIsoKernel`). In particular, we also
get constructors `descCycles` and `liftOpcycles` for morphisms from cycles
and to opcycles.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

namespace SpectralObject
variable (X : SpectralObject C ι)

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

/-- The kernel of `δ`. In the documentation, this may be shortened
as `Z^n₀(f, g)` -/
noncomputable def cycles : C := kernel (X.δ n₀ n₁ hn₁ f g)

/-- The cokernel of `δ`. In the documentation, this may be shortened
as `opZ^n₁(f, g)`. -/
noncomputable def opcycles : C := cokernel (X.δ n₀ n₁ hn₁ f g)

/-- The inclusion `Z^n₀(f, g) ⟶ H^n₀(g)` of the kernel of `δ`. -/
noncomputable def iCycles :
    X.cycles n₀ n₁ hn₁ f g ⟶ (X.H n₀).obj (mk₁ g) :=
  kernel.ι _

/-- The projection `H^n₁(f) ⟶ opZ^n₁(f, g)` to the cokernel of `δ`. -/
noncomputable def pOpcycles :
    (X.H n₁).obj (mk₁ f) ⟶ X.opcycles n₀ n₁ hn₁ f g :=
  cokernel.π _

instance : Mono (X.iCycles n₀ n₁ hn₁ f g) := by
  dsimp [iCycles]
  infer_instance

instance : Epi (X.pOpcycles n₀ n₁ hn₁ f g) := by
  dsimp [pOpcycles]
  infer_instance

@[reassoc (attr := simp)]
lemma iCycles_δ : X.iCycles n₀ n₁ hn₁ f g ≫ X.δ n₀ n₁ hn₁ f g = 0 := by
  simp [iCycles]

@[reassoc (attr := simp)]
lemma δ_pOpcycles : X.δ n₀ n₁ hn₁ f g ≫ X.pOpcycles n₀ n₁ hn₁ f g = 0 := by
  simp [pOpcycles]

/-- The short complex which expresses `X.cycles` as the kernel of `X.δ`. -/
@[simps]
noncomputable def kernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ n₀ n₁ hn₁ f g)

/-- The short complex which expresses `X.opcycles` as the cokernel of `X.δ`. -/
@[simps]
noncomputable def cokernelSequenceOpcycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles n₀ n₁ hn₁ f g)

instance : Mono (X.kernelSequenceCycles n₀ n₁ hn₁ f g).f := by
  dsimp
  infer_instance

instance : Epi (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).g := by
  dsimp
  infer_instance

lemma kernelSequenceCycles_exact :
    (X.kernelSequenceCycles n₀ n₁ hn₁ f g).Exact :=
  ShortComplex.kernelSequence_exact _

lemma cokernelSequenceOpcycles_exact :
    (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).Exact :=
  ShortComplex.cokernelSequence_exact _

section

variable {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g)) (hx : x ≫ X.δ n₀ n₁ hn₁ f g = 0)

/-- Constructor for morphisms to `X.cycles`. -/
noncomputable def liftCycles :
    A ⟶ X.cycles n₀ n₁ hn₁ f g :=
  kernel.lift _ x hx

@[reassoc (attr := simp)]
lemma liftCycles_i : X.liftCycles n₀ n₁ hn₁ f g x hx ≫ X.iCycles n₀ n₁ hn₁ f g = x := by
  apply kernel.lift_ι

end

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A) (hx : X.δ n₀ n₁ hn₁ f g ≫ x = 0)

/-- Constructor for morphisms from `X.opcycles`. -/
noncomputable def descOpcycles :
    X.opcycles n₀ n₁ hn₁ f g ⟶ A :=
  cokernel.desc _ x hx

@[reassoc (attr := simp)]
lemma p_descOpcycles : X.pOpcycles n₀ n₁ hn₁ f g ≫ X.descOpcycles n₀ n₁ hn₁ f g x hx = x := by
  apply cokernel.π_desc

end

/-- The functoriality of `X.cycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
noncomputable def cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.cycles n₀ n₁ hn₁ f g ⟶ X.cycles n₀ n₁ hn₁ f' g' :=
  kernel.lift _ (X.iCycles n₀ n₁ hn₁ f g ≫
      (X.H n₀).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))) (by
      rw [Category.assoc, X.δ_naturality n₀ n₁ hn₁ f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl, iCycles_δ_assoc, zero_comp])

@[reassoc]
lemma cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g')
    (hβ : β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) :
    X.cyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.iCycles n₀ n₁ hn₁ f' g' =
      X.iCycles n₀ n₁ hn₁ f g ≫ (X.H n₀).map β := by
  subst hβ
  apply kernel.lift_ι

@[simp]
lemma cyclesMap_id :
    X.cyclesMap n₀ n₁ hn₁ f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f g),
    X.cyclesMap_i n₀ n₁ hn₁ f g f g (𝟙 _) (𝟙 _) (by cat_disch),
    Functor.map_id, Category.comp_id, Category.id_comp]

lemma cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.cyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.cyclesMap n₀ n₁ hn₁ f' g' f'' g'' α' =
      X.cyclesMap n₀ n₁ hn₁ f g f'' g'' α'' := by
  subst h
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f'' g''), Category.assoc,
    X.cyclesMap_i n₀ n₁ hn₁ f' g' f'' g'' α' _ rfl,
    X.cyclesMap_i_assoc n₀ n₁ hn₁ f g f' g' α _ rfl,
    ← Functor.map_comp]
  symm
  apply X.cyclesMap_i
  cat_disch

/-- The functoriality of `X.opcycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
noncomputable def opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.opcycles n₀ n₁ hn₁ f g ⟶ X.opcycles n₀ n₁ hn₁ f' g' :=
  cokernel.desc _
    ((X.H n₁).map (homMk₁ (by exact α.app 0) (by exact α.app 1) (by exact naturality' α 0 1)) ≫
      X.pOpcycles n₀ n₁ hn₁ f' g') (by
        rw [← X.δ_naturality_assoc n₀ n₁ hn₁ f g f' g'
          (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl, δ_pOpcycles, comp_zero])

@[reassoc]
lemma p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f')
    (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)) :
    X.pOpcycles n₀ n₁ hn₁ f g ≫ X.opcyclesMap n₀ n₁ hn₁ f g f' g' α =
      (X.H n₁).map β ≫ X.pOpcycles n₀ n₁ hn₁ f' g' := by
  subst hβ
  apply cokernel.π_desc

@[simp]
lemma opcyclesMap_id :
    X.opcyclesMap n₀ n₁ hn₁ f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g),
    X.p_opcyclesMap n₀ n₁ hn₁ f g f g (𝟙 _) (𝟙 _) (by cat_disch),
    Functor.map_id, Category.comp_id, Category.id_comp]

lemma opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.opcyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.opcyclesMap n₀ n₁ hn₁ f' g' f'' g'' α' =
      X.opcyclesMap n₀ n₁ hn₁ f g f'' g'' α'' := by
  subst h
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g),
    X.p_opcyclesMap_assoc n₀ n₁ hn₁ f g f' g' α _ rfl,
    X.p_opcyclesMap n₀ n₁ hn₁ f' g' f'' g'' α' _ rfl,
    ← Functor.map_comp_assoc]
  symm
  apply X.p_opcyclesMap
  aesop_cat

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

/-- `X.cycles` also identifies to a cokernel. -/
noncomputable def cokernelIsoCycles :
    cokernel ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ≅ X.cycles n₀ n₁ hn₁ f g :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer 0

@[reassoc (attr := simp)]
lemma cokernelIsoCycles_hom_fac :
    cokernel.π _ ≫ (X.cokernelIsoCycles n₀ n₁ hn₁ f g fg h).hom ≫
      X.iCycles n₀ n₁ hn₁ f g = (X.H n₀).map (twoδ₁Toδ₀ f g fg h) :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer_hom_fac 0

/-- `X.opcycles` also identifies to a kernel. -/
noncomputable def opcyclesIsoKernel :
    X.opcycles n₀ n₁ hn₁ f g ≅ kernel ((X.H n₁).map (twoδ₁Toδ₀ f g fg h)) :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer 2

@[reassoc (attr := simp)]
lemma opcyclesIsoKernel_hom_fac :
    X.pOpcycles n₀ n₁ hn₁ f g ≫ (X.opcyclesIsoKernel n₀ n₁ hn₁ f g fg h).hom ≫
      kernel.ι _ = (X.H n₁).map (twoδ₂Toδ₁ f g fg h) :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer_hom_fac 2

/-- The map `H^n₀(fg) ⟶ H^n₀(g)` factors through `Z^n₀(f, g)`. -/
noncomputable def toCycles : (X.H n₀).obj (mk₁ fg) ⟶ X.cycles n₀ n₁ hn₁ f g :=
  kernel.lift _ ((X.H n₀).map (twoδ₁Toδ₀ f g fg h)) (by simp)

instance : Epi (X.toCycles n₀ n₁ hn₁ f g fg h) :=
  (ShortComplex.exact_iff_epi_kernel_lift _).1 (X.exact₃ n₀ n₁ hn₁ f g fg h)

@[reassoc (attr := simp)]
lemma toCycles_i :
    X.toCycles n₀ n₁ hn₁ f g fg h ≫ X.iCycles n₀ n₁ hn₁ f g =
      (X.H n₀).map (twoδ₁Toδ₀ f g fg h) :=
  kernel.lift_ι ..

@[reassoc]
lemma toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg')
    (hβ₀ : β.app 0 = α.app 0) (hβ₁ : β.app 1 = α.app 2) :
    X.toCycles n₀ n₁ hn₁ f g fg h ≫ X.cyclesMap n₀ n₁ hn₁ f g f' g' α =
      (X.H n₀).map β ≫ X.toCycles n₀ n₁ hn₁ f' g' fg' h' := by
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f' g'), Category.assoc, Category.assoc, toCycles_i,
    X.cyclesMap_i n₀ n₁ hn₁ f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl,
    toCycles_i_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀]
    exact naturality' α 0 1
  · dsimp
    rw [hβ₁, Category.comp_id, Category.id_comp]

/-- The map `H^n₁(f) ⟶ H^n₁(f ≫ g)` factors through `opZ^n₁(f, g)`. -/
noncomputable def fromOpcycles :
    X.opcycles n₀ n₁ hn₁ f g ⟶ (X.H n₁).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n₁).map (twoδ₂Toδ₁ f g fg h)) (by simp)

instance : Mono (X.fromOpcycles n₀ n₁ hn₁ f g fg h) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1 (X.exact₁ n₀ n₁ hn₁ f g fg h)

@[reassoc (attr := simp)]
lemma p_fromOpcycles :
    X.pOpcycles n₀ n₁ hn₁ f g ≫ X.fromOpcycles n₀ n₁ hn₁ f g fg h =
      (X.H n₁).map (twoδ₂Toδ₁ f g fg h) :=
  cokernel.π_desc ..

@[reassoc]
lemma opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg')
    (hβ₀ : β.app 0 = α.app 0) (hβ₁ : β.app 1 = α.app 2) :
    X.opcyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.fromOpcycles n₀ n₁ hn₁ f' g' fg' h' =
      X.fromOpcycles n₀ n₁ hn₁ f g fg h ≫ (X.H n₁).map β := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g), p_fromOpcycles_assoc,
    X.p_opcyclesMap_assoc n₀ n₁ hn₁ f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) rfl,
    p_fromOpcycles, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    exact (naturality' α 1 2).symm

@[reassoc (attr := simp)]
lemma H_map_twoδ₂Toδ₁_toCycles :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles n₀ n₁ hn₁ f g fg h = 0 := by
  simp [← cancel_mono (X.iCycles n₀ n₁ hn₁ f g)]

@[reassoc (attr := simp)]
lemma fromOpcycles_H_map_twoδ₁Toδ₀ :
    X.fromOpcycles n₀ n₁ hn₁ f g fg h ≫ (X.H n₁).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  simp [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g)]

/-- The short complex expressing `Z^n₀(f, g)` as a cokernel of
the map `H^n₀(f) ⟶ H^n₀(f ≫ g)`. -/
@[simps]
noncomputable def cokernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles n₀ n₁ hn₁ f g fg h)

/-- The short complex expressing `opZ^n₁(f, g)` as a kernel of
the map `H^n₁(f ≫ g) ⟶ H^n₁(g)`. -/
@[simps]
noncomputable def kernelSequenceOpcycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ n₀ n₁ hn₁ f g fg h)

instance : Epi (X.cokernelSequenceCycles n₀ n₁ hn₁ f g fg h).g := by
  dsimp
  infer_instance

instance : Mono (X.kernelSequenceOpcycles n₀ n₁ hn₁ f g fg h).f := by
  dsimp
  infer_instance

lemma cokernelSequenceCycles_exact :
    (X.cokernelSequenceCycles n₀ n₁ hn₁ f g fg h).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles n₀ n₁ hn₁ f g fg h) (by
      simp [← cancel_mono (X.iCycles n₀ n₁ hn₁ f g)]))

lemma kernelSequenceOpcycles_exact :
    (X.kernelSequenceOpcycles n₀ n₁ hn₁ f g fg h).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel n₀ n₁ hn₁ f g fg h) (by
      simp [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g)])))

section

variable {A : C} (x : (X.H n₀).obj (mk₁ fg) ⟶ A)
  (hx : (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ x = 0)

/-- Constructor for morphisms from `X.cycles`. -/
noncomputable def descCycles :
    X.cycles n₀ n₁ hn₁ f g ⟶ A :=
  (X.cokernelSequenceCycles_exact n₀ n₁ hn₁ f g fg h).desc x hx

@[reassoc (attr := simp)]
lemma toCycles_descCycles :
    X.toCycles n₀ n₁ hn₁ f g fg h ≫ X.descCycles n₀ n₁ hn₁ f g fg h x hx = x :=
  (X.cokernelSequenceCycles_exact n₀ n₁ hn₁ f g fg h).g_desc x hx

end

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ fg))
  (hx : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f g fg h) = 0)

/-- Constructor for morphisms to `X.descCycles`. -/
noncomputable def liftOpcycles :
    A ⟶ X.opcycles n₀ n₁ hn₁ f g :=
  (X.kernelSequenceOpcycles_exact n₀ n₁ hn₁ f g fg h).lift x hx

@[reassoc (attr := simp)]
lemma liftOpcycles_fromOpcycles :
    X.liftOpcycles n₀ n₁ hn₁ f g fg h x hx ≫ X.fromOpcycles n₀ n₁ hn₁ f g fg h = x :=
  (X.kernelSequenceOpcycles_exact n₀ n₁ hn₁ f g fg h).lift_f x hx

end

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)

/-- The short complex consisting of the composition of
two morphisms `X.δ`, given three composable morphisms `f₁`, `f₂`
and `f₃` in `ι`, and three consecutive integers. -/
@[simps]
def shortComplexE : ShortComplex C where
  X₁ := (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ n₀ n₁ hn₁ f₂ f₃
  g := X.δ n₁ n₂ hn₂ f₁ f₂
  zero := by simp

/-- The homology of the short complex `shortComplexE` consisting of
two morphisms `X.δ`. In the documentation, we shorten it as `E^n₁(f₁, f₂, f₃)` -/
noncomputable def E : C := (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homology

lemma isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂))) :
    IsZero (X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) :=
  (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι}
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')

/-- The functoriality of `shortComplexE` with respect to morphisms
in `ComposableArrows ι 3`. -/
@[simps]
def shortComplexEMap :
    X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶
      X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' where
  τ₁ := (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

@[simp]
lemma shortComplexEMap_id :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  ext
  all_goals dsimp; convert (X.H _).map_id _; cat_disch

@[reassoc, simp]
lemma shortComplexEMap_comp :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

/-- The functoriality of `E` with respect to morphisms
in `ComposableArrows ι 3`. -/
noncomputable def EMap :
    X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' :=
  ShortComplex.homologyMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α)

@[simp]
lemma EMap_id :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  dsimp only [EMap]
  rw [shortComplexEMap_id, ShortComplex.homologyMap_id]
  rfl

/-- Variant of `EMap_id`. -/
lemma EMap_id' (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃) (hα : α = 𝟙 _) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ α = 𝟙 _ := by
  subst hα
  simp only [EMap_id]

@[reassoc, simp]
lemma EMap_comp :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  dsimp only [EMap]
  rw [shortComplexEMap_comp, ShortComplex.homologyMap_comp]

lemma isIso_EMap
    (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α)))
    (h₁ : IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α)))
    (h₂ : IsIso ((X.H n₂).map ((functorArrows ι 0 1 3).map α))) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) := by
  have : IsIso (shortComplexEMap X n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) := by
    apply (config := { allowSynthFailures := true})
      ShortComplex.isIso_of_isIso <;> assumption
  dsimp [EMap]
  infer_instance

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

lemma δ_eq_zero_of_isIso₁ (hf : IsIso f) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ n₀ n₁ hn₁ f g _ rfl

lemma δ_eq_zero_of_isIso₂ (hg : IsIso g) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ n₀ n₁ hn₁ f g _ rfl

end

lemma isZero_H_obj_of_isIso (n : ℤ) {i j : ι} (f : i ⟶ j) (hf : IsIso f) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ n (𝟙 i) (𝟙 i) (𝟙 i) (by simp)
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← h]
  congr 1
  cat_disch

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j : ι} (f : i ⟶ j) {i' j' : ι} (f' : i' ⟶ j')

/-- An homology data for `X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)`,
expressing `H^n₁(f)` as the homology of this short complex,
see `EIsoH`. -/
@[simps!]
noncomputable def homologyDataEIdId :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).HomologyData :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j))
    (X.δ_eq_zero_of_isIso₂ n₀ n₁ hn₁ f (𝟙 j) inferInstance)
    (X.δ_eq_zero_of_isIso₁ n₁ n₂ hn₂ (𝟙 i) f inferInstance))

/-- For any morphism `f : i ⟶ j`, this is the isomorphism from
`E^n₁(𝟙 i, f, 𝟙 j)` to `H^n₁(f)`. -/
noncomputable def EIsoH :
    X.E n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j) ≅ (X.H n₁).obj (mk₁ f) :=
  (X.homologyDataEIdId ..).left.homologyIso

lemma EIsoH_hom_naturality
    (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _))
    (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.app 1)
      (by simp) (naturality' α 0 1) (by simp [Precomp.obj, Precomp.map])) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ (𝟙 _) f (𝟙 _) (𝟙 _) f' (𝟙 _) β ≫
      (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f').hom =
    (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom ≫ (X.H n₁).map α := by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ β) _ _ _ _).homologyMap_comm

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)

noncomputable def δToCycles : (X.H n₀).obj (mk₁ f₃) ⟶ X.cycles n₁ n₂ hn₂ f₁ f₂ :=
  X.liftCycles n₁ n₂ hn₂ f₁ f₂ (X.δ n₀ n₁ hn₁ f₂ f₃) (by simp)

@[reassoc (attr := simp)]
lemma δToCycles_iCycles :
    X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.iCycles n₁ n₂ hn₂ f₁ f₂ =
      X.δ n₀ n₁ hn₁ f₂ f₃ := by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]
lemma δ_toCycles :
    X.δ n₀ n₁ hn₁ f₁₂ f₃ ≫ X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ =
      X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := by
  rw [← cancel_mono (X.iCycles n₁ n₂ hn₂ f₁ f₂), Category.assoc,
    toCycles_i, δToCycles_iCycles,
    ← X.δ_naturality n₀ n₁ hn₁ f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) rfl,
    Functor.map_id, Category.id_comp]

noncomputable def δFromOpcycles : X.opcycles n₀ n₁ hn₁ f₂ f₃ ⟶ (X.H n₂).obj (mk₁ f₁) :=
  X.descOpcycles n₀ n₁ hn₁ f₂ f₃ (X.δ n₁ n₂ hn₂ f₁ f₂) (by simp)

@[reassoc (attr := simp)]
lemma pOpcycles_δFromOpcycles :
    X.pOpcycles n₀ n₁ hn₁ f₂ f₃ ≫ X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      X.δ n₁ n₂ hn₂ f₁ f₂ := by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]
lemma fromOpcyles_δ :
    X.fromOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃ ≫ X.δ n₁ n₂ hn₂ f₁ f₂₃ =
      X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f₂ f₃),
    p_fromOpcycles_assoc, pOpcycles_δFromOpcycles,
    X.δ_naturality n₁ n₂ hn₂ f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) rfl,
    Functor.map_id, Category.comp_id]

@[simps]
noncomputable def leftHomologyDataShortComplexE :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).LeftHomologyData where
  K := X.cycles n₁ n₂ hn₂ f₁ f₂
  H := cokernel (X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)
  i := X.iCycles n₁ n₂ hn₂ f₁ f₂
  π := cokernel.π _
  wi := by simp
  hi := kernelIsKernel _
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

@[simp]
lemma leftHomologyDataShortComplexE_f' :
    (X.leftHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).f' =
      X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := rfl

noncomputable def cyclesIso :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).cycles ≅ X.cycles n₁ n₂ hn₂ f₁ f₂ :=
  (X.leftHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).cyclesIso

@[reassoc (attr := simp)]
lemma cyclesIso_inv_i :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles = X.iCycles n₁ n₂ hn₂ f₁ f₂ :=
  ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]
lemma cyclesIso_hom_i :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.iCycles n₁ n₂ hn₂ f₁ f₂ =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

noncomputable def πE : X.cycles n₁ n₂ hn₂ f₁ f₂ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyπ

instance : Epi (X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) := by
  dsimp [πE]
  apply epi_comp

@[reassoc (attr := simp)]
lemma δToCycles_cyclesIso_inv :
    X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).toCycles := by
  -- this could be a general lemma for LeftHomologyData
  rw [← cancel_mono (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles, Category.assoc,
    cyclesIso_inv_i, δToCycles_iCycles, ShortComplex.toCycles_i, shortComplexE_f]

@[reassoc (attr := simp)]
lemma δToCycles_πE :
    X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ = 0 := by
  simp only [πE, δToCycles_cyclesIso_inv_assoc, ShortComplex.toCycles_comp_homologyπ]

/-- cokernelSequenceE' -/
@[simps]
noncomputable def cokernelSequenceE' : ShortComplex C :=
    ShortComplex.mk _ _ (X.δToCycles_πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)

@[simps!]
noncomputable def cokernelSequenceE'Iso :
    X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≅ ShortComplex.mk _ _
        (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).toCycles_comp_homologyπ :=
  ShortComplex.isoMk (Iso.refl _) (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (Iso.refl _) (by simp) (by simp [πE])

lemma cokernelSequenceE'_exact :
    (X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).Exact :=
  ShortComplex.exact_of_iso (X.cokernelSequenceE'Iso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

instance : Epi (X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).g := by
  dsimp
  infer_instance

@[simps]
noncomputable def rightHomologyDataShortComplexE :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).RightHomologyData where
  Q := X.opcycles n₀ n₁ hn₁ f₂ f₃
  H := kernel (X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)
  p := X.pOpcycles n₀ n₁ hn₁ f₂ f₃
  ι := kernel.ι _
  wp := by simp
  hp := cokernelIsCokernel _
  wι := kernel.condition _
  hι := kernelIsKernel _

/-- rightHomologyDataShortComplexE_g' -/
@[simp]
lemma rightHomologyDataShortComplexE_g' :
    (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).g' =
      X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := rfl

noncomputable def opcyclesIso :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).opcycles ≅ X.opcycles n₀ n₁ hn₁ f₂ f₃ :=
  (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).opcyclesIso

@[reassoc (attr := simp)]
lemma p_opcyclesIso_hom :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom =
      X.pOpcycles n₀ n₁ hn₁ f₂ f₃ :=
  ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]
lemma p_opcyclesIso_inv :
    X.pOpcycles n₀ n₁ hn₁ f₂ f₃ ≫ (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles :=
  (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).p_comp_opcyclesIso_inv

noncomputable def ιE : X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ X.opcycles n₀ n₁ hn₁ f₂ f₃ :=
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyι ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom

instance : Mono (X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) := by
  dsimp [ιE]
  infer_instance

@[reassoc (attr := simp)]
lemma opcyclesIso_hom_δFromOpcycles :
    (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).fromOpcycles := by
  -- this could be a general lemma for RightHomologyData
  rw [← cancel_epi (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles,
    p_opcyclesIso_hom_assoc, ShortComplex.p_fromOpcycles, shortComplexE_g,
    pOpcycles_δFromOpcycles]

@[reassoc (attr := simp)]
lemma ιE_δFromOpcycles :
    X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ = 0 := by
  simp only [ιE, Category.assoc, opcyclesIso_hom_δFromOpcycles,
    ShortComplex.homologyι_comp_fromOpcycles]

@[reassoc (attr := simp)]
lemma πE_ιE :
    X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      X.iCycles n₁ n₂ hn₂ f₁ f₂ ≫ X.pOpcycles n₀ n₁ hn₁ f₂ f₃ := by
  simp [πE, ιE]

/-- kernelSequenceE' -/
@[simps]
noncomputable def kernelSequenceE' : ShortComplex C :=
    ShortComplex.mk _ _ (X.ιE_δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)

@[simps!]
noncomputable def kernelSequenceE'Iso :
    X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≅ ShortComplex.mk _ _
        (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyι_comp_fromOpcycles :=
  Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)
    (Iso.refl _) (by simp [ιE]) (by simp))

lemma kernelSequenceE'_exact :
    (X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).Exact :=
  ShortComplex.exact_of_iso (X.kernelSequenceE'Iso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

instance : Mono (X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).f := by
  dsimp
  infer_instance

@[simps]
noncomputable def cokernelSequenceE : ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ n₀ n₁ hn₁ f₁₂ f₃)
  g := X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  zero := by ext <;> simp

instance : Epi (X.cokernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g := by
  dsimp
  apply epi_comp

lemma cokernelSequenceE_exact :
    (X.cokernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE'_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_up_to_refinements
      (x₂ ≫ X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂) (by simpa using hx₂)
  dsimp at y₁ hy₁
  let z := π₁ ≫ x₂ - y₁ ≫ X.δ n₀ n₁ hn₁ f₁₂ f₃
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (X.exact₂ n₁ f₁ f₂ f₁₂ h₁₂).exact_up_to_refinements z (by
      have : z ≫ X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ = 0 := by simp [z, hy₁]
      simpa only [zero_comp, Category.assoc, toCycles_i] using this =≫ X.iCycles n₁ n₂ hn₂ f₁ f₂)
  dsimp at x₁ hx₁
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift x₁ (π₂ ≫ y₁), by simp [z, ← hx₁]⟩

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
  (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0)
  (h' : X.δ n₀ n₁ hn₁ f₁₂ f₃ ≫ x = 0)

noncomputable def descE :
    X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ A :=
  (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).desc x (by
    dsimp
    ext
    · simp [h]
    · simp [h'])

@[reassoc (attr := simp)]
lemma toCycles_πE_descE :
    X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫
      X.descE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ x h h' = x := by
  dsimp only [descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g_desc

end

@[simps]
noncomputable def kernelSequenceE : ShortComplex C where
  X₁ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.fromOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ n₁ n₂ hn₂ f₁ f₂₃)
  zero := by ext <;> simp

instance : Mono (X.kernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).f := by
  dsimp
  infer_instance

lemma kernelSequenceE_exact :
    (X.kernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE'_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_up_to_refinements
      (X.liftOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        dsimp
        rw [← X.fromOpcyles_δ n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃,
          X.liftOpcycles_fromOpcycles_assoc ]
        simpa using hx₂ =≫ biprod.snd)
  dsimp at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁, ?_⟩
  dsimp
  rw [← reassoc_of% hx₁, liftOpcycles_fromOpcycles]

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
  (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0)
  (h' : x ≫ X.δ n₁ n₂ hn₂ f₁ f₂₃ = 0)

noncomputable def liftE :
    A ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
  (X.kernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).lift x (by
    dsimp
    ext
    · simp [h]
    · simp [h'])

@[reassoc (attr := simp)]
lemma liftE_ιE_fromOpcycles :
    X.liftE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃ x h h' ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫
      X.fromOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃ = x := by
  apply (X.kernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).lift_f

end

end

section

variable (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ : ι} (f : i₀ ⟶ i₁)

-- TODO: remove the dependency on `n₀`
noncomputable def cyclesIsoH :
    X.cycles n₁ n₂ hn₂ (𝟙 i₀) f ≅ (X.H n₁).obj (mk₁ f) :=
  (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ (𝟙 i₀) f (𝟙 i₁)).symm ≪≫
    (X.homologyDataEIdId ..).left.cyclesIso

@[simp]
lemma cyclesIsoH_inv :
    (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).inv = X.toCycles n₁ n₂ hn₂ (𝟙 _) f f (by simp) := by
  rw [← cancel_mono (X.iCycles n₁ n₂ hn₂ (𝟙 _) f ), toCycles_i]
  dsimp [cyclesIsoH]
  rw [Category.assoc, cyclesIso_hom_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles,
    homologyDataEIdId_left_i, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
lemma cyclesIsoH_hom_inv_id :
    (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom ≫
      X.toCycles n₁ n₂ hn₂ (𝟙 _) f f (by simp) = 𝟙 _ := by
  simpa using (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom_inv_id

@[reassoc (attr := simp)]
lemma cyclesIsoH_inv_hom_id :
    X.toCycles n₁ n₂ hn₂ (𝟙 _) f f (by simp) ≫
      (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom = 𝟙 _ := by
  simpa using (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')

@[reassoc]
lemma cyclesIso_inv_cyclesMap
    (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia))) :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      ShortComplex.cyclesMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) =
      X.cyclesMap n₁ n₂ hn₂ f₁ f₂ f₁' f₂' β ≫
        (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃').inv := by
  subst hβ
  rw [← cancel_mono (ShortComplex.iCycles _), Category.assoc, Category.assoc,
    ShortComplex.cyclesMap_i, cyclesIso_inv_i_assoc, cyclesIso_inv_i,
    shortComplexEMap_τ₂, cyclesMap_i]
  dsimp

@[reassoc]
lemma opcyclesMap_opcyclesIso_hom
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2) (naturality' α 2 3)) :
    ShortComplex.opcyclesMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃').hom =
    (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.opcyclesMap n₀ n₁ hn₁ f₂ f₃ f₂' f₃' γ := by
  subst hγ
  rw [← cancel_epi (ShortComplex.pOpcycles _), ShortComplex.p_opcyclesMap_assoc,
    p_opcyclesIso_hom, p_opcyclesIso_hom_assoc, shortComplexEMap_τ₂, p_opcyclesMap]
  dsimp

@[reassoc]
lemma πE_EMap (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
    (naturality' α 1 2 (by lia) (by lia))) :
    X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α =
      X.cyclesMap n₁ n₂ hn₂ f₁ f₂ f₁' f₂' β ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' := by
  dsimp [πE, EMap]
  simp only [Category.assoc, ShortComplex.homologyπ_naturality,
    X.cyclesIso_inv_cyclesMap_assoc n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α β hβ]

@[reassoc]
lemma EMap_ιE
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2) (naturality' α 2 3)) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' =
      X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.opcyclesMap n₀ n₁ hn₁ f₂ f₃ f₂' f₃' γ := by
  dsimp [ιE, EMap]
  simp only [ShortComplex.homologyι_naturality_assoc, Category.assoc,
    X.opcyclesMap_opcyclesIso_hom n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ]

end

end SpectralObject

end Abelian

end CategoryTheory
