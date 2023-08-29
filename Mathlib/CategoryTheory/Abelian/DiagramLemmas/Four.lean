/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Abelian.Pseudoelements

#align_import category_theory.abelian.diagram_lemmas.four from "leanprover-community/mathlib"@"d34cbcf6c94953e965448c933cd9cc485115ebbd"

/-!
# The four and five lemmas

Consider the following commutative diagram with exact rows in an abelian category:

```
A ---f--> B ---g--> C ---h--> D ---i--> E
|         |         |         |         |
α         β         γ         δ         ε
|         |         |         |         |
v         v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D' --i'-> E'
```

We show:
- the "mono" version of the four lemma: if `α` is an epimorphism and `β` and `δ` are monomorphisms,
  then `γ` is a monomorphism,
- the "epi" version of the four lemma: if `β` and `δ` are epimorphisms and `ε` is a monomorphism,
  then `γ` is an epimorphism,
- the five lemma: if `α`, `β`, `δ` and `ε` are isomorphisms, then `γ` is an isomorphism.

## Implementation details

To show the mono version, we use pseudoelements. For the epi version, we use a completely different
arrow-theoretic proof. In theory, it should be sufficient to have one version and the other should
follow automatically by duality. In practice, mathlib's knowledge about duality isn't quite at the
point where this is doable easily.

However, one key duality statement about exactness is needed in the proof of the epi version of the
four lemma: we need to know that exactness of a pair `(f, g)`, which we defined via the map from
the image of `f` to the kernel of `g`, is the same as "co-exactness", defined via the map from the
cokernel of `f` to the coimage of `g` (more precisely, we only need the consequence that if `(f, g)`
is exact, then the factorization of `g` through the cokernel of `f` is monomorphic). Luckily, in the
case of abelian categories, we have the characterization that `(f, g)` is exact if and only if
`f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`, and the latter condition is self dual, so the
equivalence of exactness and co-exactness follows easily.

## Tags

four lemma, five lemma, diagram lemma, diagram chase
-/


open CategoryTheory hiding comp_apply

open CategoryTheory.Abelian.Pseudoelement

open CategoryTheory.Limits

universe v u

variable {V : Type u} [Category.{v} V] [Abelian V]

attribute [local instance] Preadditive.hasEqualizers_of_hasKernels

open Pseudoelement

namespace CategoryTheory.Abelian

variable {A B C D A' B' C' D' : V}

variable {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}

variable {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'}

variable {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'}

variable (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)

section

variable (hfg : Exact f g) (hgh : Exact g h) (hf'g' : Exact f' g')

/-- The four lemma, mono version. For names of objects and morphisms, refer to the following
    diagram:

```
A ---f--> B ---g--> C ---h--> D
|         |         |         |
α         β         γ         δ
|         |         |         |
v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D'
```
-/
theorem mono_of_epi_of_mono_of_mono (hα : Epi α) (hβ : Mono β) (hδ : Mono δ) : Mono γ :=
  mono_of_zero_of_map_zero _ fun c hc =>
    have : h c = 0 :=
      suffices δ (h c) = 0 from zero_of_map_zero _ (pseudo_injective_of_mono _) _ this
      calc
        δ (h c) = h' (γ c) := by rw [← Pseudoelement.comp_apply, ← comm₃, Pseudoelement.comp_apply]
                                 -- 🎉 no goals
        _ = h' 0 := by rw [hc]
                       -- 🎉 no goals
        _ = 0 := apply_zero _
    Exists.elim ((pseudo_exact_of_exact hgh).2 _ this) fun b hb =>
      have : g' (β b) = 0 :=
        calc
          g' (β b) = γ (g b) := by rw [← Pseudoelement.comp_apply, comm₂, Pseudoelement.comp_apply]
                                   -- 🎉 no goals
          _ = γ c := by rw [hb]
                        -- 🎉 no goals
          _ = 0 := hc
      Exists.elim ((pseudo_exact_of_exact hf'g').2 _ this) fun a' ha' =>
        Exists.elim (pseudo_surjective_of_epi α a') fun a ha =>
          have : f a = b :=
            suffices β (f a) = β b from pseudo_injective_of_mono _ this
            calc
              β (f a) = f' (α a) := by
                rw [← Pseudoelement.comp_apply, ← comm₁, Pseudoelement.comp_apply]
                -- 🎉 no goals
              _ = f' a' := by rw [ha]
                              -- 🎉 no goals
              _ = β b := ha'
          calc
            c = g b := hb.symm
            _ = g (f a) := by rw [this]
                              -- 🎉 no goals
            _ = 0 := (pseudo_exact_of_exact hfg).1 _
#align category_theory.abelian.mono_of_epi_of_mono_of_mono CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono

end

section

variable (hgh : Exact g h) (hf'g' : Exact f' g') (hg'h' : Exact g' h')

/-- The four lemma, epi version. For names of objects and morphisms, refer to the following
    diagram:

```
A ---f--> B ---g--> C ---h--> D
|         |         |         |
α         β         γ         δ
|         |         |         |
v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D'
```
-/
theorem epi_of_epi_of_epi_of_mono (hα : Epi α) (hγ : Epi γ) (hδ : Mono δ) : Epi β :=
  Preadditive.epi_of_cancel_zero _ fun {R} r hβr => by
    have hf'r : f' ≫ r = 0 :=
      Limits.zero_of_epi_comp α <|
        calc
          α ≫ f' ≫ r = f ≫ β ≫ r := by rw [reassoc_of% comm₁]
          _ = f ≫ 0 := by rw [hβr]
          _ = 0 := HasZeroMorphisms.comp_zero _ _
    let y : R ⟶ pushout r g' := pushout.inl
    -- ⊢ r = 0
    let z : C' ⟶ pushout r g' := pushout.inr
    -- ⊢ r = 0
    -- Porting note: Added instance for `Mono (cokernel.desc f' g' hf'g'.w)`
    have : Mono (cokernel.desc f' g' hf'g'.w) := mono_cokernel_desc_of_exact _ _ hf'g'
    -- ⊢ r = 0
    have : Mono y :=
      mono_inl_of_factor_thru_epi_mono_factorization r g' (cokernel.π f')
        (cokernel.desc f' g' hf'g'.w) (by simp) (cokernel.desc f' r hf'r) (by simp) _
        (colimit.isColimit _)
    have hz : g ≫ γ ≫ z = 0 :=
      calc
        g ≫ γ ≫ z = β ≫ g' ≫ z := by rw [← reassoc_of% comm₂]
        _ = β ≫ r ≫ y := by rw [← pushout.condition]
        _ = 0 ≫ y := by rw [reassoc_of% hβr]
        _ = 0 := HasZeroMorphisms.zero_comp _ _
    let v : pushout r g' ⟶ pushout (γ ≫ z) (h ≫ δ) := pushout.inl
    -- ⊢ r = 0
    let w : D' ⟶ pushout (γ ≫ z) (h ≫ δ) := pushout.inr
    -- ⊢ r = 0
    -- Porting note: Added instance for `Mono (cokernel.desc g h hgh.w)`
    have : Mono (cokernel.desc g h hgh.w) := mono_cokernel_desc_of_exact _ _ hgh
    -- ⊢ r = 0
    have : Mono v :=
      mono_inl_of_factor_thru_epi_mono_factorization _ _ (cokernel.π g)
        (cokernel.desc g h hgh.w ≫ δ) (by simp) (cokernel.desc _ _ hz) (by simp) _
        (colimit.isColimit _)
    have hzv : z ≫ v = h' ≫ w :=
      (cancel_epi γ).1 <|
        calc
          γ ≫ z ≫ v = h ≫ δ ≫ w := by rw [← Category.assoc, pushout.condition, Category.assoc]
          _ = γ ≫ h' ≫ w := by rw [reassoc_of% comm₃]
    suffices (r ≫ y) ≫ v = 0 from zero_of_comp_mono _ (zero_of_comp_mono _ this)
    -- ⊢ (r ≫ y) ≫ v = 0
    calc
      (r ≫ y) ≫ v = g' ≫ z ≫ v := by rw [pushout.condition, Category.assoc]
      _ = g' ≫ h' ≫ w := by rw [hzv]
      _ = 0 ≫ w := (hg'h'.w_assoc _)
      _ = 0 := HasZeroMorphisms.zero_comp _ _
#align category_theory.abelian.epi_of_epi_of_epi_of_mono CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono

end

section Five

variable {E E' : V} {i : D ⟶ E} {i' : D' ⟶ E'} {ε : E ⟶ E'} (comm₄ : δ ≫ i' = i ≫ ε)

variable (hfg : Exact f g) (hgh : Exact g h) (hhi : Exact h i)

variable (hf'g' : Exact f' g') (hg'h' : Exact g' h') (hh'i' : Exact h' i')

variable [Epi α] [IsIso β] [IsIso δ] [Mono ε]

/-- The five lemma. For names of objects and morphisms, refer to the following diagram:

```
A ---f--> B ---g--> C ---h--> D ---i--> E
|         |         |         |         |
α         β         γ         δ         ε
|         |         |         |         |
v         v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D' --i'-> E'
```
-/
theorem isIso_of_epi_of_isIso_of_isIso_of_mono : IsIso γ :=
  have : Mono γ := by
    apply mono_of_epi_of_mono_of_mono comm₁ comm₂ comm₃ hfg hgh hf'g' <;> infer_instance
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
  have : Epi γ := by
    apply epi_of_epi_of_epi_of_mono comm₂ comm₃ comm₄ hhi hg'h' hh'i' <;> infer_instance
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
                                                                          -- 🎉 no goals
  isIso_of_mono_of_epi _
#align category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono

end Five

end CategoryTheory.Abelian
