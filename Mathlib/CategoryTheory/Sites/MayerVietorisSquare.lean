/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Square
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X₄` is an open subset
of a topological space that is covered by two open subsets `X₂` and `X₃`,
it is known that there is a long exact sequence
`... ⟶ H^q(X₄) ⟶ H^q(X₂) ⊞ H^q(X₃) ⟶ H^q(X₁) ⟶ H^{q+1}(X₄) ⟶ ...`
where `X₁` is the intersection of `X₂` and `X₃`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which extends `Square C`,
and asserts properties which shall imply the existence of long
exact Mayer-Vietoris sequences in sheaf cohomology (TODO).
We require that the map `X₁ ⟶ X₃` is a monomorphism and
that the square in `C` becomes a pushout square in
the category of sheaves after the application of the
functor `yoneda ⋙ presheafToSheaf J _`. Note that in the
standard case of a covering by two open subsets, all
the morphisms in the square would be monomorphisms,
but this dissymmetry allows the example of Nisnevich distinguished
squares in the case of the Nisnevich topology on schemes (in which case
`f₂₄ : X₂ ⟶ X₄` shall be an open immersion and
`f₃₄ : X₃ ⟶ X₄` an étale map that is an isomorphism over
the closed (reduced) subscheme `X₄ - X₂`,
and `X₁` shall be the pullback of `f₂₄` and `f₃₄`.).

Given a Mayer-Vietoris square `S` and a presheaf `P` on `C`,
we introduce a sheaf condition `S.SheafCondition P` and show
that it is indeed satisfied by sheaves.

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}

lemma Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff
    [HasWeakSheafify J (Type v)]
    (F : Sheaf J (Type v)) (sq : Square C) :
    (sq.op.map ((yoneda ⋙ presheafToSheaf J _).op ⋙ yoneda.obj F)).IsPullback ↔
      (sq.op.map F.val).IsPullback := by
  refine Square.IsPullback.iff_of_equiv _ _
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv) ?_ ?_ ?_ ?_
  all_goals
    ext x
    dsimp
    rw [yonedaEquiv_naturality]
    erw [Adjunction.homEquiv_naturality_left]
    rfl

namespace GrothendieckTopology

variable (J)

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄` in `C`
such that `f₁₃` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare [HasWeakSheafify J (Type v)] extends Square C where
  mono_f₁₃ : Mono toSquare.f₁₃ := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout

namespace MayerVietorisSquare

attribute [instance] mono_f₁₃

variable {J}

section

variable [HasWeakSheafify J (Type v)]

/-- Constructor for Mayer-Vietoris squares taking as an input
a square `sq` such that `sq.f₁₃` is a mono and that for every
sheaf of types `F`, the square `sq.op.map F.val` is a pullback square. -/
@[simps toSquare]
noncomputable def mk' (sq : Square C) [Mono sq.f₁₃]
    (H : ∀ (F : Sheaf J (Type v)), (sq.op.map F.val).IsPullback) :
    J.MayerVietorisSquare where
  toSquare := sq
  isPushout := by
    rw [Square.isPushout_iff_op_map_yoneda_isPullback]
    intro F
    exact (F.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff sq).2 (H F)

/-- Constructor for Mayer-Vietoris squares taking as an input
a pullback square `sq` such that `sq.f₂₄` and `sq.f₃₄` are two monomorphisms
which form a covering of `S.X₄`. -/
@[simps! toSquare]
noncomputable def mk_of_isPullback (sq : Square C) [Mono sq.f₂₄] [Mono sq.f₃₄]
    (h₁ : sq.IsPullback) (h₂ : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄) :
    J.MayerVietorisSquare :=
  have : Mono sq.f₁₃ := h₁.mono_f₁₃
  mk' sq (fun F ↦ by
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun s ↦ F.2.amalgamateOfArrows _ h₂
        (fun j ↦ WalkingPair.casesOn j s.fst s.snd)
        (fun W ↦ by
          rintro (_ | _) (_ | _) a b fac
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₂₄] using fac
            rfl
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac
            simpa using s.condition =≫ F.val.map φ.op
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac.symm
            simpa using s.condition.symm =≫ F.val.map φ.op
          · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₃₄] using fac
            rfl)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_)
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
    · exact F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
    · apply F.2.hom_ext_ofArrows _ h₂
      rintro (_ | _)
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
        exact hm₁
      · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
        exact hm₂)

variable (S : J.MayerVietorisSquare)

lemma isPushoutAddCommGrpFreeSheaf [HasWeakSheafify J AddCommGrpCat.{v}] :
    (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf J _)).IsPushout :=
  (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrpCat.free)).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free)).app
        (S.map yoneda))

/-- The condition that a Mayer-Vietoris square becomes a pullback square
when we evaluate a presheaf on it. -/
def SheafCondition {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) : Prop :=
  (S.toSquare.op.map P).IsPullback

lemma sheafCondition_iff_comp_coyoneda {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) :
    S.SheafCondition P ↔ ∀ (X : Aᵒᵖ), S.SheafCondition (P ⋙ coyoneda.obj X) :=
  Square.isPullback_iff_map_coyoneda_isPullback (S.op.map P)

/-- Given a Mayer-Vietoris square `S` and a presheaf of types, this is the
map from `P.obj (op S.X₄)` to the explicit fibre product of
`P.map S.f₁₂.op` and `P.map S.f₁₃.op`. -/
abbrev toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    P.obj (op S.X₄) → Types.PullbackObj (P.map S.f₁₂.op) (P.map S.f₁₃.op) :=
  (S.toSquare.op.map P).pullbackCone.toPullbackObj

lemma sheafCondition_iff_bijective_toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    S.SheafCondition P ↔ Function.Bijective (S.toPullbackObj P) := by
  have := (S.toSquare.op.map P).pullbackCone.isLimitEquivBijective
  exact ⟨fun h ↦ this h.isLimit, fun h ↦ Square.IsPullback.mk _ (this.symm h)⟩

namespace SheafCondition

variable {S}
variable {P : Cᵒᵖ ⥤ Type v'} (h : S.SheafCondition P)
include h

lemma bijective_toPullbackObj : Function.Bijective (S.toPullbackObj P) := by
  rwa [← sheafCondition_iff_bijective_toPullbackObj]

lemma ext {x y : P.obj (op S.X₄)}
    (h₁ : P.map S.f₂₄.op x = P.map S.f₂₄.op y)
    (h₂ : P.map S.f₃₄.op x = P.map S.f₃₄.op y) : x = y :=
  h.bijective_toPullbackObj.injective (by ext <;> assumption)

variable (u : P.obj (op S.X₂)) (v : P.obj (op S.X₃))
  (huv : P.map S.f₁₂.op u = P.map S.f₁₃.op v)

/-- If `S` is a Mayer-Vietoris square, and `P` is a presheaf
which satisfies the sheaf condition with respect to `S`, then
elements of `P` over `S.X₂` and `S.X₃` can be glued if the
coincide over `S.X₁`. -/
noncomputable def glue : P.obj (op S.X₄) :=
  (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨u, v⟩, huv⟩

@[simp]
lemma map_f₂₄_op_glue : P.map S.f₂₄.op (h.glue u v huv) = u :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit _

@[simp]
lemma map_f₃₄_op_glue : P.map S.f₃₄.op (h.glue u v huv) = v :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit _

end SheafCondition

lemma sheafCondition_of_sheaf {A : Type u'} [Category.{v} A]
    (F : Sheaf J A) : S.SheafCondition F.val := by
  rw [sheafCondition_iff_comp_coyoneda]
  intro X
  exact (Sheaf.isPullback_square_op_map_yoneda_presheafToSheaf_yoneda_iff _ S.toSquare).1
    (S.isPushout.op.map
      (yoneda.obj ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.cond X.unop)⟩))

end

variable [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  (S : J.MayerVietorisSquare)

/-- The short complex of abelian sheaves
`ℤ[S.X₁] ⟶ ℤ[S.X₂] ⊞ ℤ[S.X₃] ⟶ ℤ[S.X₄]`
where the left map is a difference and the right map a sum. -/
@[simps]
noncomputable def shortComplex :
    ShortComplex (Sheaf J AddCommGrpCat.{v}) where
  X₁ := (presheafToSheaf J _).obj (yoneda.obj S.X₁ ⋙ AddCommGrpCat.free)
  X₂ := (presheafToSheaf J _).obj (yoneda.obj S.X₂ ⋙ AddCommGrpCat.free) ⊞
    (presheafToSheaf J _).obj (yoneda.obj S.X₃ ⋙ AddCommGrpCat.free)
  X₃ := (presheafToSheaf J _).obj (yoneda.obj S.X₄ ⋙ AddCommGrpCat.free)
  f :=
    biprod.lift
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₂) _))
      (-(presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₃) _))
  g :=
    biprod.desc
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₂₄) _))
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₃₄) _))
  zero := (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf J _)).cokernelCofork.condition

instance : Mono S.shortComplex.f := by
  have : Mono (S.shortComplex.f ≫ biprod.snd) := by
    dsimp
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

instance : Epi S.shortComplex.g :=
  (S.shortComplex.exact_and_epi_g_iff_g_is_cokernel.2
    ⟨S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork⟩).2

lemma shortComplex_exact : S.shortComplex.Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    S.isPushoutAddCommGrpFreeSheaf.isColimitCokernelCofork

lemma shortComplex_shortExact : S.shortComplex.ShortExact where
  exact := S.shortComplex_exact

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
