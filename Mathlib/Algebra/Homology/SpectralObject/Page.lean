/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ExactSequenceFour

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

/-- The kernel of `δ`. -/
noncomputable def cycles : C := kernel (X.δ n₀ n₁ hn₁ f g)

/-- The cokernel of `δ`. -/
noncomputable def opcycles : C := cokernel (X.δ n₀ n₁ hn₁ f g)

/-- The inclusion `X.cycles n₀ n₁ hn₁ f g ⟶ (X.H n₀).obj (mk₁ g)`
of the kernel of `δ`. -/
noncomputable def iCycles :
    X.cycles n₀ n₁ hn₁ f g ⟶ (X.H n₀).obj (mk₁ g) :=
  kernel.ι _

/-- The projection `(X.H n₁).obj (mk₁ f) ⟶ X.opcycles n₀ n₁ hn₁ f g`
to the cokernel of `δ`. -/
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
    X.cyclesMap_i n₀ n₁ hn₁ f g f g (𝟙 _) (𝟙 _) (by aesop_cat),
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
  aesop_cat

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
    X.p_opcyclesMap n₀ n₁ hn₁ f g f g (𝟙 _) (𝟙 _) (by aesop_cat),
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

/-- The map `(X.H n₀).obj (mk₁ fg) ⟶ (X.H n₀).obj (mk₁ g)` factors through
`X.cycles n₀ n₁ hn₁ f g`. -/
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

/-- The map `(X.H n₁).obj (mk₁ f) ⟶ (X.H n₁).obj (mk₁ fg)` factors through
`X.opcycles n₀ n₁ hn₁ f g`. -/
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

/-- The short complex expressing `X.cycles n₀ n₁ hn₁ f g` as a cokernel of
the map `(X.H n₀).obj (mk₁ f) ⟶ (X.H n₀).obj (mk₁ fg)`. -/
@[simps]
noncomputable def cokernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles n₀ n₁ hn₁ f g fg h)

/-- The short complex expressing `X.opcycles n₀ n₁ hn₁ f g` as a kernel of
the map `(X.H n₁).obj (mk₁ fg) ⟶ (X.H n₁).obj (mk₁ g)`. -/
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
two morphisms `X.δ`. -/
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
expressing `(X.H n₁).obj (mk₁ f)` as the homology of this short complex,
see `EIsoH`. -/
@[simps!]
noncomputable def homologyDataEIdId :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).HomologyData :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j))
    (X.δ_eq_zero_of_isIso₂ n₀ n₁ hn₁ f (𝟙 j) inferInstance)
    (X.δ_eq_zero_of_isIso₁ n₁ n₂ hn₂ (𝟙 i) f inferInstance))

/-- `(X.H n₁).obj (mk₁ f)` identifies to `X.E` applied to the composable
morphisms `𝟙 _, f, 𝟙 _`. -/
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

end SpectralObject

end Abelian

end CategoryTheory
