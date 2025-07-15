/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Michail Karatarakis
-/
import Mathlib.CategoryTheory.Category.Factorisation
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Combinatorics.Quiver.ReflQuiver

/- This code is based on a Unimath implementation of regular categories
 by Niels van der Weide. Original source:
https://github.com/UniMath/UniMath/blob/master/UniMath/CategoryTheory/RegularAndExact/RegularCategory.v#L319 -/

set_option linter.unusedSimpArgs false
set_option linter.style.multiGoal false
set_option linter.unusedSectionVars false
set_option linter.style.docString false
set_option linter.style.commandStart false

universe u v

noncomputable section

namespace CategoryTheory

open Functor Opposite Limits MonoidalCategory
  CartesianMonoidalCategory Category

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local instance]
  _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory

class Regular extends HasFiniteLimits C where
  equiv_rel_coeq : ∀ {W X Y : C} (f : X ⟶ Y) (a b : W ⟶ X),
    IsKernelPair f a b → HasCoequalizer a b
  pullback_stability : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    RegularEpi f → RegularEpi (pullback.snd f g)

variable {C}

/--
A `RegularEpiFactorisation` of a morphism `f : X ⟶ Y` in a category
`C` is a factorisation of `f` into a regular epimorphism `ι`
followed by a monomorphism `π`.
-/
structure RegularEpiFactorisation {X Y : C} (f : X ⟶ Y)
    extends Factorisation f where
  regular_epi : RegularEpi ι
  mono : Mono π

variable [HasPullbacks C] {A B C' : C} (f : A ⟶ B) (g : B ⟶ C')

/-- The pullback of `(f ≫ g)` with itself. -/
def Khh := pullback (f ≫ g) (f ≫ g)

/-- The pullback of `g` with itself. -/
def Kgg := pullback g g

/--
The canonical map between the pullbacks of two morphisms `f` and `h`.
-/
def kernel_pair_map : Khh f g ⟶ Kgg g := by
    let h := (pullback.fst (f ≫ g) (f ≫ g) ≫ f)
    let k := (pullback.snd (f ≫ g) (f ≫ g) ≫ f)
    have : IsPullback (pullback.fst g g) (pullback.snd g g) g g :=
      IsPullback.of_hasPullback g g
    apply CategoryTheory.IsPullback.lift this h k
    change (pullback.fst (f ≫ g) (f ≫ g) ≫ f) ≫ g =
      (pullback.snd (f ≫ g) (f ≫ g) ≫ f) ≫ g
    simp only [assoc]
    exact pullback.condition

-- def Kgg_new := pullback g g

-- def Khh_new (h : A ⟶ C') := pullback h h

-- def kernel_pair_map'' (h : A ⟶ C')
--   (p : f ≫ g = h) : Khh_new h ⟶ Kgg_new g := by
--   let PullbackPr1Khh := (pullback.fst h h ≫ f)
--   let PullbackPr2Khh := (pullback.snd h h ≫ f)
--   have w : PullbackPr1Khh ≫ g = PullbackPr2Khh ≫ g := by {
--     unfold PullbackPr1Khh  PullbackPr2Khh
--     simp only [assoc]
--     rw [p]
--     exact pullback.condition}
--   apply CategoryTheory.IsPullback.lift ?_
--   · exact w
--   · exact pullback.fst g g
--   · exact pullback.snd g g
--   · exact IsPullback.of_hasPullback g g

/-- The pullback of a morphism `f` along the first projection from
 the pullback of another morphism `g` with itself. -/
def Kl := pullback f (pullback.fst g g)

/-- The pullback of a morphism `f` along the
  second projection from the pullback of `g` with itself. -/
def Kr := pullback f (pullback.snd g g)

/-- The projection morphism from the pullback of `f` and
 the first projection of the pullback of `g` with itself. -/
def PullbackPr2Kl := pullback.snd f (pullback.fst g g)

/-- The second projection from
the pullback of `f` and the second projection from the pullback of `g` with itself.
-/
def PullbackPr2Kr := pullback.snd f (pullback.snd g g)

variable [RegularEpi f]

/--
  In a regular category, the second projection from the pullback of
   morphisms `f` and `g`
  is a regular epimorphism, by stability of regular epis under pullback.
-/
def is_regular_epi_left [Regular C] :
  RegularEpi (PullbackPr2Kl f g) := by
  apply Regular.pullback_stability
  infer_instance

/--
Given a regular epimorphism `f`, the pullback of `f` along itself
 yields another regular epimorphism.
-/
def is_regular_epi_right [Regular C] :
  RegularEpi (pullback.snd f (pullback.snd g g)) := by
  apply Regular.pullback_stability
  infer_instance

/--
Given morphisms `f` and `g`, constructs a morphism from `Khh` to
 `Kl` using the universal property of the pullback, relating kernel
 pairs and pullbacks.
-/
def map_to_pullback_left :
  Khh f g ⟶ Kl f g := by {
  apply CategoryTheory.IsPullback.lift ?_
    (pullback.fst (f ≫ g) (f ≫ g)) (kernel_pair_map f g)
  have : (kernel_pair_map f g) ≫ (pullback.fst g g) =
    (pullback.fst (f ≫ g) (f ≫ g)) ≫ f := by {
    unfold kernel_pair_map
    simp only [IsPullback.lift_fst]}
  apply this.symm
  · exact pullback.fst f (pullback.fst g g)
  · exact PullbackPr2Kl f g
  exact IsPullback.of_hasPullback f (pullback.fst g g)}

/--
Constructs a morphism from `Khh h` to `Kr f g` using the universal
 property of the pullback.
-/
def map_to_pullback_right :
  Khh f g ⟶ Kr f g := by {
  apply CategoryTheory.IsPullback.lift ?_
    (pullback.snd (f ≫ g) (f ≫ g)) (kernel_pair_map f g)
  have : (kernel_pair_map f g) ≫ (pullback.snd g g) =
    (pullback.snd (f ≫ g) (f ≫ g)) ≫ f := by {
    unfold kernel_pair_map
    simp only [IsPullback.lift_snd]}
  apply this.symm
  · unfold Kr
    exact pullback.fst f (pullback.snd g g)
  · exact pullback.snd f (pullback.snd g g)
  exact IsPullback.of_hasPullback f (pullback.snd g g)}

/--
Establishes the equality between two compositions involving the morphisms
`map_to_pullback_left` and `map_to_pullback_right` with pullback projections,
using properties of pullbacks.
-/
lemma map_to_pullback_sqr : map_to_pullback_left f g ≫ (PullbackPr2Kl f g) =
   map_to_pullback_right f g ≫ pullback.snd f (pullback.snd g g) := by {
    unfold map_to_pullback_left map_to_pullback_right
    simp only [IsPullback.lift_snd, id_eq]}

variable {w : C} (k₁ : w ⟶ Kl f g) (k₂ : w ⟶ Kr f g)
 (IsPullbacketc : k₁ ≫ (PullbackPr2Kl f g) = k₂ ≫
    pullback.snd f (pullback.snd g g))

include IsPullbacketc in
omit [CartesianMonoidalCategory C] [RegularEpi f] in
lemma is_pullback_sqr_mor_eq :
  (k₁ ≫ pullback.fst f (pullback.fst g g)) ≫ (f ≫ g) =
  (k₂ ≫ pullback.fst f (pullback.snd g g)) ≫ (f ≫ g) := by {
    unfold Kl at *
    unfold Kr at *
    rw [assoc]
    rw [assoc]
    have PullbackSqrCommutesKl : pullback.fst f (pullback.fst g g) ≫ f =
      (PullbackPr2Kl f g) ≫ (pullback.fst g g) :=
      pullback.condition
    have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
     = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g)  :=
      pullback.condition
    have h1 : k₂ ≫ pullback.fst f (pullback.snd g g) ≫ f ≫ g =
     k₂ ≫ (pullback.fst f (pullback.snd g g) ≫ f) ≫ g :=
       by {simp only [assoc]}
    rw [h1]
    have h11 : k₁ ≫ pullback.fst f (pullback.fst g g) ≫ f ≫ g =
      k₁ ≫ (pullback.fst f (pullback.fst g g) ≫ f) ≫ g := by {
        simp only [assoc]
      }
    rw [h11]
    rw [PullbackSqrCommutesKl]
    rw [PullbackSqrCommutesKr]
    have : k₁ ≫ (PullbackPr2Kl f g ≫ pullback.fst g g) ≫ g =
      (k₁ ≫ (PullbackPr2Kl f g)) ≫ pullback.fst g g ≫ g := by {
        simp only [assoc]
      }
    rw [this]
    have :  k₂ ≫ (pullback.snd f (pullback.snd g g)
      ≫ pullback.snd g g) ≫ g =
      (k₂ ≫ (pullback.snd f (pullback.snd g g)
      ≫ pullback.snd g g)) ≫ g := by {simp only [assoc]}
    rw [this]
    rw [IsPullbacketc]
    have PullbackSqrCommutes : pullback.fst g g ≫ g =
      pullback.snd g g ≫ g := pullback.condition
    rw [PullbackSqrCommutes]
    simp only [assoc]
  }

/--
Constructs a morphism `w ⟶ Khh f g` using the universal property of pullbacks,
given morphisms `k₁` and `k₂` and appropriate pullback data.
-/
def is_pullback_sqr_mor : w ⟶ Khh f g:= by {
  unfold Khh
  apply CategoryTheory.IsPullback.lift ?_
    (k₁ ≫ pullback.fst f (pullback.fst g g))
    (k₂ ≫ pullback.fst f (pullback.snd g g))
  apply is_pullback_sqr_mor_eq f g k₁ k₂ (IsPullbacketc)
  · exact pullback.fst (f ≫ g) (f ≫ g)
  · exact pullback.snd (f ≫ g) (f ≫ g)
  · exact IsPullback.of_hasPullback (f ≫ g) (f ≫ g)}

omit [CartesianMonoidalCategory C] [RegularEpi f] in
lemma is_pullback_sqr_mor_pr1 :
  is_pullback_sqr_mor f g k₁ k₂ (IsPullbacketc) ≫
  map_to_pullback_left f g = k₁ := by {
  unfold is_pullback_sqr_mor map_to_pullback_left
  unfold kernel_pair_map
  simp only
  have PullbackSqrCommutesKl : pullback.fst f (pullback.fst g g) ≫ f =
    (PullbackPr2Kl f g) ≫ (pullback.fst g g) :=
    pullback.condition
  have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
    = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g)  :=
    pullback.condition
  unfold PullbackPr2Kl at *
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [id_eq, assoc, IsPullback.lift_fst]
  · simp only [id_eq]
    apply CategoryTheory.Limits.pullback.hom_ext
    · have : (k₁ ≫ pullback.snd f (pullback.fst g g)) ≫ pullback.fst g g=
        k₁ ≫ (pullback.snd f (pullback.fst g g)) ≫ pullback.fst g g := by {
          simp only [assoc]
        }
      rw [this]
      rw [← PullbackSqrCommutesKl]
      simp only [assoc, IsPullback.lift_snd,
        IsPullback.lift_fst, IsPullback.lift_fst_assoc]
    · simp only [assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc]
      have : k₂ ≫ pullback.fst f (pullback.snd g g) ≫ f =
        k₂ ≫ (pullback.fst f (pullback.snd g g) ≫ f) := by {
          simp only [assoc]
        }
      rw [this]
      rw [PullbackSqrCommutesKr]
      have : k₂ ≫ pullback.snd f (pullback.snd g g) ≫ pullback.snd g g=
       (k₂ ≫ pullback.snd f (pullback.snd g g)) ≫ pullback.snd g g := by {
        simp only [assoc]
       }
      rw [this, ← (IsPullbacketc)]
      simp only [assoc]
}

omit [CartesianMonoidalCategory C] [RegularEpi f] in
lemma is_pullback_sqr_mor_pr2 :
  is_pullback_sqr_mor f g k₁ k₂ (IsPullbacketc) ≫
  map_to_pullback_right f g = k₂ := by {
  unfold is_pullback_sqr_mor map_to_pullback_right
  have PullbackSqrCommutesKl : pullback.fst f (pullback.fst g g) ≫ f =
    (PullbackPr2Kl f g) ≫ (pullback.fst g g) :=
    pullback.condition
  have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
      = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g)  :=
     pullback.condition
  unfold PullbackPr2Kl kernel_pair_map at *
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [id_eq, assoc, IsPullback.lift_fst, IsPullback.lift_snd]
  · simp only [id_eq]
    apply CategoryTheory.Limits.pullback.hom_ext
    · simp only [assoc, IsPullback.lift_snd, IsPullback.lift_fst,
        IsPullback.lift_fst_assoc]
      have :  k₁ ≫ pullback.fst f (pullback.fst g g) ≫ f =
         k₁ ≫ (pullback.fst f (pullback.fst g g) ≫ f) := by {
          simp only [assoc]
         }
      rw [this]
      rw [PullbackSqrCommutesKl]
      have : k₁ ≫ pullback.snd f (pullback.fst g g) ≫ pullback.fst g g =
        (k₁ ≫ pullback.snd f (pullback.fst g g)) ≫ pullback.fst g g := by {
          simp only [assoc]
        }
      rw [this, (IsPullbacketc)]
      simp only [assoc]
    · simp only [assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc]
      rw [PullbackSqrCommutesKr]}

lemma is_pullback_sqr_unique :
  ∃! hk, (hk ≫ (map_to_pullback_left f g ) = k₁ ∧
    hk ≫ map_to_pullback_right f g = k₂) := by {
    constructor
    simp only [and_imp]
    unfold Khh
    · constructor
      · sorry
      · intros y hy1 hy2
        apply CategoryTheory.Limits.pullback.hom_ext ?_ ?_
        · sorry
        · sorry
        · sorry
    }

lemma is_pullback_sqr : IsPullback (map_to_pullback_left f g)
 (map_to_pullback_right f g)
 (PullbackPr2Kl f g) (pullback.snd f (pullback.snd g g)) := by {
  constructor
  · let cone := PullbackCone.mk (map_to_pullback_left f g)
      (map_to_pullback_right f g) (map_to_pullback_sqr f g)
    have : IsLimit cone := by {
      apply PullbackCone.IsLimit.mk
      intros s
      unfold PullbackPr2Kl at *
      · sorry
      · intros s
        sorry
      sorry
      sorry
    }
    sorry
    --apply PullbackCone.isLimit.mk
  · constructor
    exact map_to_pullback_sqr f g
 }

instance regularEpiOfIsoComp {X Y Z: C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [hg : RegularEpi g] :
    RegularEpi (f ≫ g) where
  W := _
  left := hg.left ≫ inv f
  right := hg.right ≫ inv f
  w := by simp [hg.w]
  isColimit := by
    fapply Cofork.IsColimit.mk
    · exact fun s ↦ Cofork.IsColimit.desc hg.isColimit (inv f ≫ s.π) (by simpa using s.condition)
    · intro s
      simp only [parallelPair_obj_one, Cofork.ofπ_pt, const_obj_obj, Cofork.π_ofπ, assoc]
      erw [← IsIso.eq_inv_comp, Cofork.IsColimit.π_desc' hg.isColimit]
    · intro s m hm
      simp [← IsIso.eq_inv_comp] at hm
      have := hg.isColimit.uniq (Cofork.ofπ (inv f ≫ s.π) (by simpa using s.condition)) m
        (by rintro (_ | _) <;> simp [hm])
      simp [this]
      congr!

/--
Borceux - Lemma 2.1.2:
Let `f : A ⟶ B` be a regular epimorphism and `g : B ⟶ C` any morphism in a category.
Then the induced morphism `f ×C f : A ×c A ⟶ B ×c B` (the product over `C`)
is also an epimorphism. -/
lemma isEpi_kernel_pair_map [Regular C] :
  Epi (kernel_pair_map f g) := by {
    have PullbackSqrCommutesKr : pullback.fst f (pullback.snd g g) ≫ f
      = pullback.snd f (pullback.snd g g) ≫ (pullback.snd g g) :=
     pullback.condition
    let q : Khh f g ⟶ Kr f g := map_to_pullback_right f g
    let t := PullbackPr2Kr f g
    have Hq : kernel_pair_map f g =  q ≫ t :=  by {
      unfold kernel_pair_map q t
      unfold map_to_pullback_right
      unfold PullbackPr2Kr
      unfold kernel_pair_map
      simp only [id_eq, IsPullback.lift_snd]
    }
    rw [Hq]
    haveI : Epi t := by {
      unfold t
      unfold PullbackPr2Kr
      have : RegularEpi (pullback.snd f (pullback.snd g g)) := by {
        apply is_regular_epi_right f g
      }
      apply RegularEpi.epi }
    haveI : Epi q := by {
      have : RegularEpi q := by {
        have h₁ := IsPullback.of_hasPullback g g
        have h₂ := IsPullback.of_hasPullback f (pullback.snd g g)
        have hR := h₂.paste_vert h₁.flip
        have h := IsPullback.of_hasPullback (f ≫ g) (f ≫ g)
        have hq : q ≫ pullback.fst f (pullback.snd g g) = pullback.snd (f ≫ g) (f ≫ g) := by
          simp [q, map_to_pullback_right, kernel_pair_map]
        rw [← hq] at h
        have hL := by
          refine IsPullback.paste_vert_iff hR.flip ?_ |>.mp h
          simp [q, map_to_pullback_right, kernel_pair_map]
        have : (IsPullback.isoPullback hL).hom ≫ pullback.snd _ _ = q := by simp
        rw [← this]
        unfold q
        unfold Kr at q
        unfold map_to_pullback_right
        have := is_regular_epi_left f g
        unfold PullbackPr2Kl at this
        simp only [kernel_pair_map]
        convert regularEpiOfIsoComp hL.isoPullback.hom _
        fapply Regular.pullback_stability
        assumption }
      apply RegularEpi.epi
    }
    apply epi_comp }

variable [Regular C]

/-- `K` is defined as the pullback of the morphism `f` with itself. -/
def K := pullback f f

instance regular_epi_mono_factorization_image
    : HasCoequalizer (pullback.fst f f) (pullback.snd f f)
    := by {
      apply Regular.equiv_rel_coeq f (pullback.fst f f) (pullback.snd f f)
      unfold IsKernelPair
      exact IsPullback.of_hasPullback f f}

/-- The image of a morphism `f`, defined as the coequalizer of the
 two projections from the pullback of `f` with itself. -/
def im := coequalizer (pullback.fst f f) (pullback.snd f f)

/-- The canonical morphism from `A` to the image of `f`, given
 by the coequalizer of the two projections from the pullback of `f` with itself. -/
def regular_epi_mono_factorization_epi : A ⟶ im f :=
  coequalizer.π (pullback.fst f f) (pullback.snd f f)

/-- The epimorphism part of the regular epi-mono factorization of `f`. -/
def e := regular_epi_mono_factorization_epi f

/-- The canonical morphism from the image of `f` to `B` in the
  regular epi-mono factorization. -/
def regular_epi_mono_factorization_mono : im f ⟶ B :=
  coequalizer.desc f (pullback.condition)

/-- The mono part of the regular epi-mono factorization of `f`. -/
def m := regular_epi_mono_factorization_mono f

/--
  Proves that the morphism obtained from the epi-mono
  factorization is a regular epimorphism,
  using the coequalizer of the pullback projections of `f`.
-/
def regular_epi_mono_factorization_is_regular_epi : RegularEpi (e f) :=
  coequalizerRegular (pullback.fst f f) (pullback.snd f f)

/-- `K'` is defined as the pullback of the morphism `m f` with itself. -/
def K' := pullback (m f) (m f)

lemma regular_epi_mono_factorization_is_regular_is_monic_eq : pullback.fst f f ≫
    (coequalizer.π (pullback.fst f f) (pullback.snd f f)) ≫  (m f) =
    pullback.snd f f ≫
    (coequalizer.π (pullback.fst f f) (pullback.snd f f)) ≫  (m f) := by {
      unfold m regular_epi_mono_factorization_mono
      simp only [colimit.ι_desc, Cofork.ofπ_pt, Cofork.ofπ_ι_app]
      exact pullback.condition
    }

lemma regular_epi_mono_factorization_comm : f = e f ≫ m f := by {
  unfold e m
  unfold regular_epi_mono_factorization_epi
    regular_epi_mono_factorization_mono
  simp only [colimit.ι_desc, Cofork.ofπ_pt, Cofork.ofπ_ι_app]}

omit IsPullbacketc in
/-- Constructs a morphism between the kernels `K f` and `K' f` in
 the context of the regular epi-mono factorization,
   using the universal property of pullbacks. -/
def regular_epi_mono_factorization_is_regular_is_monic_mor :
  K f ⟶ K' f := by {
    unfold K'
    let kernel_pair_map := kernel_pair_map f g
    unfold Khh Kgg at kernel_pair_map
    have hP : IsPullback (pullback.fst (m f) (m f))
     (pullback.snd (m f) (m f)) (m f) (m f) :=
     IsPullback.of_hasPullback (m f) (m f)
    apply CategoryTheory.IsPullback.lift hP
    · rfl_cat
    · exact (pullback.fst f f) ≫ (e f)
    }

/-- The morphism `φ` is the canonical map from `K f` to `K' f` arising from the
  regular epi-mono factorization of `f` and `g`. -/
def φ : K f ⟶ K' f := regular_epi_mono_factorization_is_regular_is_monic_mor f g

omit k₁ k₂ IsPullbacketc in
lemma is_epi_monic_mor : Epi (φ f g) := by {
  unfold φ
  unfold regular_epi_mono_factorization_is_regular_is_monic_mor
  simp only [id_eq]
  --simp only [id_eq]
  --sorry
  have : Epi (IsPullback.lift
    (IsPullback.of_hasPullback (m f) (m f))
    (pullback.fst f f ≫ e f)
    (pullback.fst f f ≫ e f)
    (by simp only [assoc])) := sorry
  have H {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    RegularEpi f → RegularEpi (pullback.snd f g) :=
    Regular.pullback_stability f g
  sorry
  -- unfold kernel_pair_map at this
  -- simp only at this
  -- unfold e
  -- unfold regular_epi_mono_factorization_epi
}

omit w k₁ k₂ IsPullbacketc [CartesianMonoidalCategory C] [RegularEpi f] in
lemma monic_mor_pr1 :
  φ f g ≫ pullback.fst (m f) (m f) = pullback.fst f f ≫
    coequalizer.π (pullback.fst f f) (pullback.snd f f) := by
  apply CategoryTheory.IsPullback.lift_fst

omit w k₁ k₂ IsPullbacketc in
lemma monic_mor_pr2 :
  φ f g ≫ pullback.snd (m f) (m f) = pullback.fst f f ≫
    coequalizer.π (pullback.fst f f) (pullback.snd f f) := by
  apply CategoryTheory.IsPullback.lift_snd

omit w k₁ k₂ IsPullbacketc in
include g in
lemma monic_mor_eq :
  pullback.fst (m f) (m f) =
  pullback.snd (m f) (m f) := by {
  let Hepi := (is_epi_monic_mor f g)
  have Hepi_prop :=
    Hepi.left_cancellation
     (pullback.fst (m f) (m f)) (pullback.snd (m f) (m f))
  simp only at Hepi_prop
  apply Hepi_prop
  rw [monic_mor_pr1 f g]
  rw [monic_mor_pr2 f g]}

include g in
omit w k₁ k₂ IsPullbacketc in
lemma regular_epi_mono_factorization_is_regular_is_monic :
  Mono (m f) := by {
  constructor
  intros w g' h p
  have hP : IsPullback (pullback.fst (m f) (m f))
    (pullback.snd (m f) (m f)) (m f) (m f) :=
    IsPullback.of_hasPullback (m f) (m f)
  have ζ := CategoryTheory.IsPullback.lift hP g' h p
  have h1 := IsPullback.lift_fst hP g' h p
  have h2 := IsPullback.lift_snd hP g' h p
  rw [← h1]
  let := monic_mor_eq f g
  simp_all only [IsPullback.lift_fst]}

/--
In a regular category, every morphism `f : X ⟶ Y` can be factored as `f = e ≫ m`,
where `e` is a regular epimorphism and `m` is a monomorphism.
This is a useful test for the definition of regular categories, and corresponds to
Proposition 8.3 in Barrs and Wells.
-/
def regularEpiFactorization [Regular C] (f : A ⟶ B) [RegularEpi f]:
  RegularEpiFactorisation f where
    mid := im f
    ι := e f
    π := m f
    ι_π := (regular_epi_mono_factorization_comm f).symm
    regular_epi := regular_epi_mono_factorization_is_regular_epi f
    mono := regular_epi_mono_factorization_is_regular_is_monic f g

-- def regularEpiFactorization' {A A' : C} [Regular C] (f : A ⟶ A') :
--   RegularEpiFactorisation f where
--     mid := by {
--       let K := pullback f f
--       let d0 : K ⟶ A := pullback.fst f f
--       let d1 : K ⟶ A := pullback.snd f f
--       haveI kernelPair : IsKernelPair f d0 d1 :=
--         IsPullback.of_hasPullback f f
--       haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
--       exact coequalizer d0 d1}
--     ι := by {
--       let K := pullback f f
--       let d0 : K ⟶ A := pullback.fst f f
--       let d1 : K ⟶ A := pullback.snd f f
--       haveI kernelPair : IsKernelPair f d0 d1 :=
--         IsPullback.of_hasPullback f f
--       haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
--       -- let g be the coequalizer of d0 and d1.
--       let g : A ⟶ coequalizer d0 d1 := coequalizer.π d0 d1
--       exact g
--     }
--     π := by {
--       let K := pullback f f
--       let d0 : K ⟶ A := pullback.fst f f
--       let d1 : K ⟶ A := pullback.snd f f
--       haveI kernelPair : IsKernelPair f d0 d1 :=
--         IsPullback.of_hasPullback f f
--       haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
--       apply CategoryTheory.Limits.coequalizer.desc f
--       exact pullback.condition}
--     ι_π := by {
--       simp only [colimit.ι_desc, Cofork.ofπ_pt, Cofork.ofπ_ι_app] }
--     regular_epi := by {
--       let K := pullback f f
--       let d0 : K ⟶ A := pullback.fst f f
--       let d1 : K ⟶ A := pullback.snd f f
--       haveI kernelPair : IsKernelPair f d0 d1 := IsPullback.of_hasPullback f f
--       haveI := Regular.equiv_rel_coeq f d0 d1 kernelPair
--       let g : A ⟶ coequalizer d0 d1 := coequalizer.π d0 d1
--       simp only
--       constructor
--       exact coequalizerIsCoequalizer (pullback.fst f f) (pullback.snd f f)}
