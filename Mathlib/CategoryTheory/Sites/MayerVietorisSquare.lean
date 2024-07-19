/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X` is an open subset
of a topological space that is covered by two open subsets `U` and `V`,
it is known that this is a long exact sequence
`... ⟶ H^q(X) ⟶ H^q(U) ⊞ H^q(V) ⟶ H^q(W) ⟶ H^{q+1}(X) ⟶ ...`
when `W` is the intersection of `U` and `V`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which contains the data
of a commutative square in a category `C` equipped with a Grothendieck
topology `J`, which share some properties with the square formed by
the open subsets `W`, `U`, `V`, `X` in the example above.
In particular, we require that the square become a pushout square
when it is understood as a square in the category of sheaves of sets.
We also require that `U ⟶ X` is a monomorphism. The morphism `V ⟶ X`
does not have to be a monomorphism, which shall allow the example
of Nisnevich distinguished squares in the case of the Nisnevich
topology on schemes (in which case `i : U ⟶ X` shall be an open
immersion and `j : V ⟶ X` an étale map that is an
isomorphism over the closed (reduced) subscheme `X - U`,
and `W` is the fibre product of `i` and `j`.).

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe w v u

namespace CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

open Limits Opposite

section

variable {C : Type u} [Category.{v} C]

abbrev Sieve.ofTwoArrows {U V X : C} (i : U ⟶ X) (j : V ⟶ X) : Sieve X :=
  Sieve.ofArrows (Y := pairFunction U V) (fun k ↦ WalkingPair.casesOn k i j)

variable {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : PullbackCone f g}
  (hc : IsLimit c)

open Concrete

namespace Limits.PullbackCone.IsLimit

noncomputable def equiv : c.pt ≃ { p : X × Y // f p.1 = g p.2 } :=
  have : HasPullback f g := ⟨_, hc⟩
  (IsLimit.conePointUniqueUpToIso hc
    (pullbackIsPullback f g)).toEquiv.trans (pullbackEquiv f g)

@[simp]
lemma equiv_apply_fst (x : c.pt) : (equiv hc x).1.1 = c.fst x := by
  erw [pullbackEquiv_fst]
  exact congr_fun ((IsLimit.conePointUniqueUpToIso_hom_comp hc _) .left) x

@[simp]
lemma equiv_apply_snd (x : c.pt) : (equiv hc x).1.2 = c.snd x := by
  erw [pullbackEquiv_snd]
  exact congr_fun ((IsLimit.conePointUniqueUpToIso_hom_comp hc _) .right) x

@[simp]
lemma equiv_symm_apply_fst (x : { p : X × Y // f p.1 = g p.2 }) :
    c.fst ((equiv hc).symm x) = x.1.1 := by
  obtain ⟨x, rfl⟩ := (equiv hc).surjective x
  simp

@[simp]
lemma equiv_symm_apply_snd (x : { p : X × Y // f p.1 = g p.2 }) :
    c.snd ((equiv hc).symm x) = x.1.2 := by
  obtain ⟨x, rfl⟩ := (equiv hc).surjective x
  simp

lemma type_ext {z₁ z₂ : c.pt}
    (h₁ : c.fst z₁ = c.fst z₂)
    (h₂ : c.snd z₁ = c.snd z₂): z₁ = z₂ := by
  apply (equiv hc).injective
  ext <;> simpa

end Limits.PullbackCone.IsLimit

end

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrp.{v}]

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `p ≫ i = q ≫ j` in `C`
such that `i` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare where
  /-- the object that is covered -/
  X : C
  /-- the first object of the covering -/
  U : C
  /-- the second object of the covering -/
  V : C
  /-- the top-left corner of the square -/
  W : C
  /-- the inclusion of `U` in `X` -/
  i : U ⟶ X
  /-- the morphism from `V` to `X` -/
  j : V ⟶ X
  /-- the morphism from `W` to `U` -/
  p : W ⟶ U
  /-- the morphism from `W` to `V` -/
  q : W ⟶ V
  fac : p ≫ i = q ≫ j
  hi : Mono i := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isColimit :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsColimit (PushoutCocone.mk
      (f := F.map p) (g := F.map q) (F.map i) (F.map j) (by
        simp only [← Functor.map_comp, fac]))

initialize_simps_projections MayerVietorisSquare (-isColimit)

namespace MayerVietorisSquare

variable {J}
section

variable {X U V W : C} (i : U ⟶ X) (j : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V) [Mono i]
  (H : ∀ (F : Sheaf J (Type v)),
    IsPullback (F.val.map i.op) (F.val.map j.op) (F.val.map p.op) (F.val.map q.op))

namespace mk'

variable {i j p q}
variable (s : PushoutCocone ((yoneda ⋙ presheafToSheaf J _).map p)
    ((yoneda ⋙ presheafToSheaf J _).map q))

noncomputable def aux₁ : s.pt.val.obj (op X) :=
  (PullbackCone.IsLimit.equiv (H s.pt).isLimit).symm
    ⟨⟨yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _ s.inl),
       yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _ s.inr)⟩, by
        simpa only [yonedaEquiv_naturality, ← Adjunction.homEquiv_naturality_left]
          using congr_arg yonedaEquiv
            (congr_arg ((sheafificationAdjunction _ _).homEquiv _ _) s.condition)⟩

lemma map_i_op_aux₁ : s.pt.val.map i.op (aux₁ H s) =
    yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _ s.inl) :=
  PullbackCone.IsLimit.equiv_symm_apply_fst (H s.pt).isLimit _

lemma map_j_op_aux₁ : s.pt.val.map j.op (aux₁ H s) =
    yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _ s.inr) :=
  PullbackCone.IsLimit.equiv_symm_apply_snd (H s.pt).isLimit _

noncomputable def aux₂ : (presheafToSheaf J (Type v)).obj (yoneda.obj X) ⟶ s.pt :=
  ((sheafificationAdjunction _ _).homEquiv _ _).symm (yonedaEquiv.symm (aux₁ H s))

lemma yonedaEquiv_sheafificationAdjunction_homEquiv_aux₂ :
    yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _ (aux₂ H s)) =
      aux₁ H s := by
  simp only [aux₂, Equiv.apply_symm_apply]

lemma map_i_comp_aux₂ :
    (yoneda ⋙ presheafToSheaf J (Type v)).map i ≫ mk'.aux₂ H s = s.inl := by
  apply ((sheafificationAdjunction _ _).homEquiv _ _).injective
  apply yonedaEquiv.injective
  dsimp only [aux₂, Functor.comp_map]
  rw [← map_i_op_aux₁ H s, ← Adjunction.homEquiv_naturality_left_symm,
    Equiv.apply_symm_apply, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  dsimp

lemma map_j_comp_aux₂ :
    (yoneda ⋙ presheafToSheaf J (Type v)).map j ≫ mk'.aux₂ H s = s.inr := by
  apply ((sheafificationAdjunction _ _).homEquiv _ _).injective
  apply yonedaEquiv.injective
  dsimp only [aux₂, Functor.comp_map]
  rw [← map_j_op_aux₁ H s, ← Adjunction.homEquiv_naturality_left_symm,
    Equiv.apply_symm_apply, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  dsimp

end mk'

@[simps]
noncomputable def mk' (fac : p ≫ i = q ≫ j) (H : ∀ (F : Sheaf J (Type v)),
    IsPullback (F.val.map i.op) (F.val.map j.op) (F.val.map p.op) (F.val.map q.op)) :
    J.MayerVietorisSquare where
  fac := fac
  isColimit := PushoutCocone.IsColimit.mk _ (fun s ↦ mk'.aux₂ H s)
    (fun s ↦ mk'.map_i_comp_aux₂ H s) (fun s ↦ mk'.map_j_comp_aux₂ H s)
    (fun s m hm₁ hm₂ ↦ by
      apply ((sheafificationAdjunction _ _).homEquiv _ _).injective
      apply yonedaEquiv.injective
      apply PullbackCone.IsLimit.type_ext (H s.pt).isLimit
      · rw [mk'.yonedaEquiv_sheafificationAdjunction_homEquiv_aux₂]
        dsimp
        rw [mk'.map_i_op_aux₁, ← hm₁]
        erw [Adjunction.homEquiv_naturality_left]
        rw [yonedaEquiv_naturality]
        rfl
      · rw [mk'.yonedaEquiv_sheafificationAdjunction_homEquiv_aux₂]
        dsimp
        rw [mk'.map_j_op_aux₁, ← hm₂]
        erw [Adjunction.homEquiv_naturality_left]
        rw [yonedaEquiv_naturality]
        rfl)

variable {i j p q}

@[simps!]
noncomputable def mk_of_isPullback
    [Mono j] (h₁ : IsPullback p q i j) (h₂ : Sieve.ofTwoArrows i j ∈ J X) :
    J.MayerVietorisSquare :=
  mk' _ _ _ _ h₁.w (fun F ↦
    { w := by simp only [← Functor.map_comp, ← op_comp, h₁.w]
      isLimit' :=
        ⟨PullbackCone.IsLimit.mk _
          (fun s ↦ F.2.amalgamateOfArrows _ h₂
            (fun j ↦ WalkingPair.casesOn j s.fst s.snd) (fun W ↦ by
              rintro (_|_) (_|_) a b fac
              · obtain rfl : a = b := by simpa only [← cancel_mono i] using fac
                rfl
              · dsimp at a b fac ⊢
                obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac
                simpa using s.condition =≫ F.val.map φ.op
              · dsimp at a b fac ⊢
                obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' h₁.isLimit _ _ fac.symm
                simpa using s.condition.symm =≫ F.val.map φ.op
              · obtain rfl : a = b := by simpa only [← cancel_mono j] using fac
                rfl))
          (fun _ ↦ F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left)
          (fun _ ↦ F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right)
          (fun s m hm₁ hm₂ ↦ F.2.hom_ext_ofArrows _ h₂ (by
            rintro (_|_)
            · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.left, hm₁]
            · rw [F.2.amalgamateOfArrows_map _ _ _ _ WalkingPair.right, hm₂]))⟩ } )

end

variable (S : J.MayerVietorisSquare)

lemma isPushout :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsPushout (F.map S.p) (F.map S.q) (F.map S.i) (F.map S.j) where
  w := by simp only [← Functor.map_comp, S.fac]
  isColimit' := ⟨S.isColimit⟩

section

variable (F : Sheaf J (Type v))

lemma ext {x y : F.val.obj (op S.X)} (h₁ : F.val.map S.i.op x = F.val.map S.i.op y)
    (h₂ : F.val.map S.j.op x = F.val.map S.j.op y) : x = y := by
  apply yonedaEquiv.symm.injective
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  apply PushoutCocone.IsColimit.hom_ext S.isColimit
  · erw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_left_symm,
      ← yonedaEquiv_symm_map S.i.op, ← yonedaEquiv_symm_map S.i.op]
    dsimp
    rw [h₁]
  · erw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_left_symm,
      ← yonedaEquiv_symm_map S.j.op, ← yonedaEquiv_symm_map S.j.op]
    dsimp
    rw [h₂]

variable (u : F.val.obj (op S.U)) (v : F.val.obj (op S.V))
  (h : F.val.map S.p.op u = F.val.map S.q.op v)

namespace glue

/-- Auxiliary definition for `MayerVietorisSquare.glue`. -/
noncomputable def hom : (presheafToSheaf J _).obj (yoneda.obj S.X) ⟶ F :=
  PushoutCocone.IsColimit.desc S.isColimit
      (((sheafificationAdjunction _ _).homEquiv _ _).symm (yonedaEquiv.symm u))
      (((sheafificationAdjunction _ _).homEquiv _ _).symm (yonedaEquiv.symm v)) (by
        dsimp
        erw [← Adjunction.homEquiv_naturality_left_symm,
          ← Adjunction.homEquiv_naturality_left_symm]
        congr 1
        apply yonedaEquiv.injective
        simpa [yonedaEquiv] using h)

@[reassoc (attr := simp)]
lemma map_i_op_hom :
    (presheafToSheaf J _).map (yoneda.map S.i) ≫ glue.hom S F u v h =
      ((sheafificationAdjunction J _).homEquiv _ F).symm (yonedaEquiv.symm u) :=
  PushoutCocone.IsColimit.inl_desc S.isColimit _ _ _

@[reassoc (attr := simp)]
lemma map_j_op_hom :
    (presheafToSheaf J _).map (yoneda.map S.j) ≫ glue.hom S F u v h =
      ((sheafificationAdjunction J _).homEquiv _ F).symm (yonedaEquiv.symm v) :=
  PushoutCocone.IsColimit.inr_desc S.isColimit _ _ _

end glue

/-- If `S` is a Mayer-Vietoris square, a section of a sheaf
on `S.X` can be constructed by gluing sections over `S.U` and `S.V`
which coincide on `S.W`. -/
noncomputable def glue : F.val.obj (op S.X) :=
  yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _
    (glue.hom S F u v h))

lemma map_i_op_glue : F.val.map S.i.op (S.glue F u v h) = u := by
  apply yonedaEquiv.symm.injective
  have eq := congr_arg ((sheafificationAdjunction J _).homEquiv _ _)
    (glue.map_i_op_hom S F u v h)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left] at eq
  simpa only [glue, yonedaEquiv_naturality, Equiv.symm_apply_apply] using eq

lemma map_j_op_glue : F.val.map S.j.op (S.glue F u v h) = v := by
  apply yonedaEquiv.symm.injective
  have eq := congr_arg ((sheafificationAdjunction J _).homEquiv _ _)
    (glue.map_j_op_hom S F u v h)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left] at eq
  simpa only [glue, yonedaEquiv_naturality, Equiv.symm_apply_apply] using eq

end

lemma isPushoutAddCommGrpFreeSheaf :
    letI F := yoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.free ⋙
      presheafToSheaf J _
    IsPushout (F.map S.p) (F.map S.q) (F.map S.i) (F.map S.j) := by
  have e := presheafToSheafCompComposeAndSheafifyIso J AddCommGrp.free
  exact (S.isPushout.map (Sheaf.composeAndSheafify J AddCommGrp.free)).of_iso
    (e.app _) (e.app _) (e.app _) (e.app _) (e.hom.naturality _)
      (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

-- TODO: deduce a short exact sequence in the category of abelian sheaves

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory

namespace Opens

open CategoryTheory Limits

variable {T : Type u} [TopologicalSpace T]
  (U V X W : TopologicalSpace.Opens T)
  (hX : X = U ⊔ V)
  (hW : W = U ⊓ V)

instance (f : U ⟶ V) : Mono f where
  right_cancellation := by
    intros
    apply Subsingleton.elim

@[simps! X U V W i j p q]
noncomputable def mayerVietorisSquare' :
    (Opens.grothendieckTopology T).MayerVietorisSquare :=
  GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := (Opens.grothendieckTopology T))
    (X := X) (U := U) (V := V) (W := W)
    (i := homOfLE (by simp only [hX, le_sup_left]))
    (j := homOfLE (by simp only [hX, le_sup_right]))
    (p := homOfLE (by simp only [hW, inf_le_left]))
    (q := homOfLE (by simp only [hW, inf_le_right]))
    { w := by simp
      isLimit' := ⟨by
        refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
        · intro s
          apply homOfLE
          rw [hW, le_inf_iff]
          exact ⟨leOfHom s.fst, leOfHom s.snd⟩
        all_goals intros; apply Subsingleton.elim⟩ }
    (fun x hx ↦ by
      rw [hX] at hx
      obtain (hx|hx) := hx
      · exact ⟨U, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.left, hx⟩⟩
      · exact ⟨V, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.right, hx⟩⟩)

@[simps! X U V W i j p q]
noncomputable def mayerVietorisSquare :
    (Opens.grothendieckTopology T).MayerVietorisSquare :=
  mayerVietorisSquare' U V _ _ rfl rfl

end Opens
