/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.CategoryTheory.Sites.Preserves
/-!

# The Regular and Extensive Coverages

This file defines two coverages on a category `C`.

The first one is called the *regular* coverage and for that to exist, the category `C` must satisfy
a condition called `Preregular C`. This means that effective epimorphisms can be "pulled back". The
covering sieves of this coverage are generated by presieves consisting of a single effective
epimorphism.

The second one is called the *extensive* coverage and for that to exist, the category `C` must
satisfy a condition called `FinitaryPreExtensive C`. This means `C` has finite coproducts and that
those are preserved by pullbacks. The covering sieves of this coverage are generated by presieves
consisting finitely many arrows that together induce an isomorphism from the coproduct to the
target. This condition is weaker than `FinitaryExtensive`, where in addition finite coproducts are
disjoint.

## Main results

* `extensive_union_regular_generates_coherent`: the union of the regular and extensive coverages
  generates the coherent topology on `C` if `C` is precoherent, preextensive and preregular.

* `isSheaf_iff_equalizerCondition`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.

* `isSheaf_iff_preservesFiniteProducts`: In a finitary extensive category, the sheaves for the
  extensive topology are precisely those preserving finite products.
-/

universe v u w

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

/--
The condition `Preregular C` is property that effective epis can be "pulled back" along any
morphism. This is satisfied e.g. by categories that have pullbacks that preserve effective
epimorphisms (like `Profinite` and `CompHaus`), and categories where every object is projective
(like  `Stonean`).
-/
class Preregular : Prop where
  /--
  For `X`, `Y`, `Z`, `f`, `g` like in the diagram, where `g` is an effective epi, there exists
  an object `W`, an effective epi `h : W ⟶ X` and a morphism `i : W ⟶ Z` making the diagram
  commute.
  ```
  W --i-→ Z
  |       |
  h       g
  ↓       ↓
  X --f-→ Y
  ```
  -/
  exists_fac : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [EffectiveEpi g],
    (∃ (W : C) (h : W ⟶ X) (_ : EffectiveEpi h) (i : W ⟶ Z), i ≫ g = h ≫ f)

/--
The regular coverage on a regular category `C`.
-/
def regularCoverage [Preregular C] : Coverage C where
  covering B := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f }
  pullback := by
    intro X Y f S ⟨Z, π, hπ, h_epi⟩
    have := Preregular.exists_fac f π
    obtain ⟨W, h, _, i, this⟩ := this
    refine ⟨Presieve.singleton h, ⟨?_, ?_⟩⟩
    · exact ⟨W, h, by {rw [Presieve.ofArrows_pUnit h]}, inferInstance⟩
    · intro W g hg
      cases hg
      refine ⟨Z, i, π, ⟨?_, this⟩⟩
      cases hπ
      rw [Presieve.ofArrows_pUnit]
      exact Presieve.singleton.mk

/--
The extensive coverage on an extensive category `C`
-/
def extensiveCoverage [FinitaryPreExtensive C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only, FinitaryPreExtensive.sigma_desc_iso (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      exact Presieve.ofArrows.mk a


/-- The union of the extensive and regular coverages generates the coherent topology on `C`. -/
lemma extensive_regular_generate_coherent [Preregular C] [FinitaryPreExtensive C] [Precoherent C] :
    ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck =
    (coherentTopology C) := by
  ext B S
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · induction h with
    | of Y T hT =>
      apply Coverage.saturate.of
      simp only [Coverage.sup_covering, Set.mem_union] at hT
      exact Or.elim hT
        (fun ⟨α, x, X, π, ⟨h, _⟩⟩ ↦ ⟨α, x, X, π, ⟨h, inferInstance⟩⟩)
        (fun ⟨Z, f, ⟨h, _⟩⟩ ↦ ⟨Unit, inferInstance, fun _ ↦ Z, fun _ ↦ f, ⟨h, inferInstance⟩⟩)
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]
  · induction h with
    | of Y T hT =>
      obtain ⟨I, hI, X, f, ⟨h, hT⟩⟩ := hT
      let φ := fun (i : I) ↦ Sigma.ι X i
      let F := Sigma.desc f
      let Z := Sieve.generate T
      let Xs := (∐ fun (i : I) => X i)
      let Zf := Sieve.generate (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F))
      apply Coverage.saturate.transitive Y Zf
      · apply Coverage.saturate.of
        simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
          Set.mem_setOf_eq]
        exact Or.inr ⟨Xs, F, ⟨rfl, inferInstance⟩⟩
      · intro R g hZfg
        dsimp at hZfg
        rw [Presieve.ofArrows_pUnit] at hZfg
        obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg
        induction hW
        rw [← hW', Sieve.pullback_comp Z]
        suffices Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
          ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck R by assumption
        apply GrothendieckTopology.pullback_stable'
        suffices Coverage.saturate ((extensiveCoverage C) ⊔ (regularCoverage C)) Xs
          (Z.pullback F) by assumption
        suffices : Sieve.generate (Presieve.ofArrows X φ) ≤ Z.pullback F
        · apply Coverage.saturate_of_superset _ this
          apply Coverage.saturate.of
          simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
            Set.mem_setOf_eq]
          refine Or.inl ⟨I, hI, X, φ, ⟨rfl, ?_⟩⟩
          suffices Sigma.desc φ = 𝟙 _ by rw [this]; infer_instance
          ext
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
        intro Q q hq
        simp only [Sieve.pullback_apply, Sieve.generate_apply]
        simp only [Sieve.generate_apply] at hq
        obtain ⟨E, e, r, hq⟩ := hq
        refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩
        · rw [h]
          induction hq.1
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
          exact Presieve.ofArrows.mk _
        · rw [← hq.2]
          simp only [Category.assoc]
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]

section RegularSheaves

variable {C}

open Opposite

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

/--
The map to the explicit equalizer used in the sheaf condition.
-/
def MapToEqualizer (P : Cᵒᵖ ⥤ Type (max u v)) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  fun t ↦ ⟨P.map f.op t, by
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _;
    simp_rw [← P.map_comp, ← op_comp, w] ⟩

/--
The sheaf condition with respect to regular presieves, given the existence of the relavant pullback.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ Type (max u v)) : Prop :=
  ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
    pullback.condition)

/--
The `FirstObj` in the sheaf condition diagram is isomorphic to `F` applied to `X`.
-/
noncomputable
def EqualizerFirstObjIso (F : Cᵒᵖ ⥤ Type (max u v)) {B X : C} (π : X ⟶ B) :
    Equalizer.FirstObj F (Presieve.singleton π) ≅ F.obj (op X) :=
  CategoryTheory.Equalizer.firstObjEqFamily F (Presieve.singleton π) ≪≫
  { hom := fun e ↦ e π (Presieve.singleton_self π)
    inv := fun e _ _ h ↦ by
      induction h with
      | mk => exact e
    hom_inv_id := by
      funext _ _ _ h
      induction h with
      | mk => rfl
    inv_hom_id := by aesop }

instance {B X : C} (π : X ⟶ B) [HasPullback π π] :
    (Presieve.singleton π).hasPullbacks where
  has_pullbacks hf _ hg := by
    cases hf
    cases hg
    infer_instance

/--
The `SecondObj` in the sheaf condition diagram is isomorphic to `F` applied to the pullback of `π` 
with itself
-/
noncomputable
def EqualizerSecondObjIso (F : Cᵒᵖ ⥤ Type (max u v)) {B X : C} (π : X ⟶ B) [HasPullback π π] :
    Equalizer.Presieve.SecondObj F (Presieve.singleton π) ≅ F.obj (op (Limits.pullback π π)) :=
  Types.productIso.{max u v, max u v} _ ≪≫
  { hom := fun e ↦ e (⟨X, ⟨π, Presieve.singleton_self π⟩⟩, ⟨X, ⟨π, Presieve.singleton_self π⟩⟩)
    inv := fun x ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩ ↦ by
      induction h₁
      induction h₂
      exact x
    hom_inv_id := by
      funext _ ⟨⟨_, ⟨_, h₁⟩⟩ , ⟨_, ⟨_, h₂⟩⟩⟩
      induction h₁
      induction h₂
      rfl
    inv_hom_id := by aesop }

lemma EqualizerCondition.isSheafFor {B : C} {S : Presieve B} [S.regular] [S.hasPullbacks]
    {F : Cᵒᵖ ⥤ Type (max u v)}
    (hFecs : EqualizerCondition F) : S.IsSheafFor F := by
  obtain ⟨X, π, ⟨hS, πsurj⟩⟩ := Presieve.regular.single_epi (R := S)
  rw [Presieve.ofArrows_pUnit] at hS
  haveI : (Presieve.singleton π).hasPullbacks := by rw [← hS]; infer_instance
  haveI : HasPullback π π :=
    Presieve.hasPullbacks.has_pullbacks (Presieve.singleton.mk) (Presieve.singleton.mk)
  subst hS
  rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
  intro y h
  specialize hFecs X B π
  have hy : F.map (pullback.fst (f := π) (g := π)).op ((EqualizerFirstObjIso F π).hom y) =
      F.map (pullback.snd (f := π) (g := π)).op ((EqualizerFirstObjIso F π).hom y) :=
    calc
      _ = (Equalizer.Presieve.firstMap F (Presieve.singleton π) ≫
          (EqualizerSecondObjIso F π).hom) y := by
          simp [EqualizerSecondObjIso, EqualizerFirstObjIso, Equalizer.Presieve.firstMap]
      _ = (Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫ (EqualizerSecondObjIso F π).hom)
          y := by simp only [Equalizer.Presieve.SecondObj, types_comp_apply]; rw [h]
      _ = _ := by
          simp [EqualizerSecondObjIso, EqualizerFirstObjIso, Equalizer.Presieve.secondMap]
  obtain ⟨x, ⟨hx₁, hx₂⟩⟩ : ∃! x, F.map π.op x = (EqualizerFirstObjIso F π).hom y
  · rw [Function.bijective_iff_existsUnique] at hFecs
    specialize hFecs ⟨(EqualizerFirstObjIso F π).hom y, hy⟩
    obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := hFecs
    refine ⟨x, ⟨Subtype.ext_iff.mp hx₁, ?_⟩⟩
    intros
    apply hx₂
    rwa [Subtype.ext_iff]
  have fork_comp : Equalizer.forkMap F (Presieve.singleton π) ≫ (EqualizerFirstObjIso F π).hom =
      F.map π.op := by ext; simp [EqualizerFirstObjIso, Equalizer.forkMap]
  rw [← fork_comp] at hx₁ hx₂
  refine ⟨x, ⟨?_, ?_⟩⟩
  · apply_fun (EqualizerFirstObjIso F π).hom using injective_of_mono (EqualizerFirstObjIso F π).hom
    exact hx₁
  · intro z hz
    apply_fun (EqualizerFirstObjIso F π).hom at hz
    exact hx₂ z hz

lemma IsSheafForRegular.equalizerCondition {F : Cᵒᵖ ⥤ Type (max u v)}
    (hSF : ∀ {B : C} (S : Presieve B) [S.regular] [S.hasPullbacks], S.IsSheafFor F) :
    EqualizerCondition F := by
  intro X B π _ _
  haveI : (Presieve.singleton π).regular :=
    ⟨X, π, ⟨(Presieve.ofArrows_pUnit π).symm, inferInstance⟩⟩
  specialize hSF (Presieve.singleton π)
  rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hSF
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  specialize hSF ((EqualizerFirstObjIso F π).inv b) ?_
  · apply_fun (EqualizerSecondObjIso F π).hom using injective_of_mono _
    calc
      _ = F.map (pullback.fst (f := π) (g := π)).op b := by
        simp only [Equalizer.Presieve.SecondObj, EqualizerSecondObjIso, Equalizer.Presieve.firstMap,
          EqualizerFirstObjIso, Iso.trans_inv, types_comp_apply, Equalizer.firstObjEqFamily_inv,
          Iso.trans_hom, Types.productIso_hom_comp_eval_apply, Types.Limit.lift_π_apply', Fan.mk_pt,
          Fan.mk_π_app]; rfl
      _ = F.map (pullback.snd (f := π) (g := π)).op b := hb
      _ = ((EqualizerFirstObjIso F π).inv ≫ Equalizer.Presieve.secondMap F (Presieve.singleton π) ≫
        (EqualizerSecondObjIso F π).hom) b := by
          simp only [EqualizerFirstObjIso, Iso.trans_inv, Equalizer.Presieve.SecondObj,
            Equalizer.Presieve.secondMap, EqualizerSecondObjIso, Iso.trans_hom,
            Types.productIso_hom_comp_eval, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, types_comp_apply,
            Equalizer.firstObjEqFamily_inv, Types.Limit.lift_π_apply']; rfl
  · obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := hSF
    refine ⟨a, ⟨?_, ?_⟩⟩
    · ext
      dsimp [MapToEqualizer]
      apply_fun (EqualizerFirstObjIso F π).hom at ha₁
      simp only [inv_hom_id_apply] at ha₁
      rw [← ha₁]
      simp only [EqualizerFirstObjIso, Equalizer.forkMap, Iso.trans_hom, types_comp_apply,
        Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]
    · intro y hy
      apply ha₂
      apply_fun (EqualizerFirstObjIso F π).hom using injective_of_mono _
      simp only [inv_hom_id_apply]
      simp only [MapToEqualizer, Set.mem_setOf_eq, Subtype.mk.injEq] at hy
      rw [← hy]
      simp only [EqualizerFirstObjIso, Equalizer.forkMap, Iso.trans_hom, types_comp_apply,
        Equalizer.firstObjEqFamily_hom, Types.pi_lift_π_apply]

lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type (max u v)) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  let g := Projective.factorThru (𝟙 _) f
  have hfg : g ≫ f = 𝟙 _ := by
    simp only [Projective.factorThru_comp]
  intro y hy
  refine' ⟨F.map g.op <| y f <| Presieve.ofArrows.mk (), fun Z h hZ => _, fun z hz => _⟩
  · cases' hZ with u
    have := hy (f₁ := f) (f₂ := f) (𝟙 Y) (f ≫ g) (Presieve.ofArrows.mk ())
        (Presieve.ofArrows.mk ()) ?_
    · rw [op_id, F.map_id, types_id_apply] at this
      rw [← types_comp_apply (F.map g.op) (F.map f.op), ← F.map_comp, ← op_comp]
      exact this.symm
    · rw [Category.id_comp, Category.assoc, hfg, Category.comp_id]
  · have := congr_arg (F.map g.op) <| hz f (Presieve.ofArrows.mk ())
    rwa [← types_comp_apply (F.map f.op) (F.map g.op), ← F.map_comp, ← op_comp, hfg, op_id,
      F.map_id, types_id_apply] at this

lemma isSheaf_iff_equalizerCondition (F : Cᵒᵖ ⥤ Type (max u v)) [Preregular C] [HasPullbacks C] :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck F ↔ EqualizerCondition F := by
  rw [Presieve.isSheaf_coverage]
  refine ⟨?_, ?_⟩
  · intro h
    apply IsSheafForRegular.equalizerCondition
    intro B S _ _
    apply h S
    obtain ⟨Y, f, rfl, _⟩ := Presieve.regular.single_epi (R := S)
    use Y, f
  · intro h X S ⟨Y, f, hh⟩
    haveI : S.regular := ⟨Y, f, hh⟩
    exact h.isSheafFor

lemma isSheaf_of_projective (F : Cᵒᵖ ⥤ Type (max u v)) [Preregular C] [∀ (X : C), Projective X] :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck F := by
  rw [Presieve.isSheaf_coverage]
  intro X S ⟨Y, f, hh⟩
  haveI : S.regular := ⟨Y, f, hh⟩
  exact isSheafFor_regular_of_projective _ _

end RegularSheaves

section ExtensiveSheaves

variable [FinitaryPreExtensive C] {C}

/-- A presieve is *extensive* if it is finite and its arrows induce an isomorphism from the
coproduct to the target. -/
class Presieve.extensive [HasFiniteCoproducts C] {X : C} (R : Presieve X) :
    Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_sigma_desc_iso : ∃ (α : Type) (_ : Fintype α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ IsIso (Sigma.desc π)

instance {X : C} (S : Presieve X) [S.extensive] : S.hasPullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, hS, _⟩ := Presieve.extensive.arrows_sigma_desc_iso (R := S)
    intro _ _ f hf _ hg
    rw [hS] at hf hg
    cases' hg with b
    apply FinitaryPreExtensive.hasPullbacks_of_inclusions f

instance {α : Type} [Fintype α] {Z : α → C} {F : C ⥤ Type w}
    [PreservesFiniteProducts F] : PreservesLimit (Discrete.functor fun a => (Z a)) F :=
  (PreservesFiniteProducts.preserves α).preservesLimit

open Presieve Opposite

/--
A finite product preserving presheaf is a sheaf for the extensive topology on a category which is
`FinitaryPreExtensive`.
-/
theorem isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.extensive]
    (F : Cᵒᵖ ⥤ Type max u v) [PreservesFiniteProducts F] : S.IsSheafFor F  := by
  obtain ⟨_, _, Z, π, hS, _⟩ := extensive.arrows_sigma_desc_iso (R := S)
  subst hS
  have : (ofArrows Z (Cofan.mk X π).inj).hasPullbacks :=
    (inferInstance : (ofArrows Z π).hasPullbacks)
  have : IsIso (Sigma.desc (Cofan.mk X π).inj) := (inferInstance : IsIso (Sigma.desc π))
  exact isSheafFor_of_preservesProduct _ _ (Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π))

instance {α : Type} [Fintype α] (Z : α → C) : (ofArrows Z (fun i ↦ Sigma.ι Z i)).extensive where
  arrows_sigma_desc_iso := by
    refine ⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ?_⟩
    convert IsIso.id _
    ext
    simp

/--
A presheaf on a category which is `FinitaryExtensive` is a sheaf iff it preserves finite products.
-/
theorem isSheaf_iff_preservesFiniteProducts [FinitaryExtensive C] (F : Cᵒᵖ ⥤ Type max u v) :
    Presieve.IsSheaf (extensiveCoverage C).toGrothendieck F ↔
    Nonempty (PreservesFiniteProducts F) := by
  refine ⟨fun hF ↦ ⟨⟨fun α _ ↦ ⟨fun {K} ↦ ?_⟩⟩⟩, fun hF ↦ ?_⟩
  · rw [Presieve.isSheaf_coverage] at hF
    let Z : α → C := fun i ↦ unop (K.obj ⟨i⟩)
    have : (Presieve.ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).hasPullbacks :=
      (inferInstance : (Presieve.ofArrows Z (Sigma.ι Z)).hasPullbacks)
    have : ∀ (i : α), Mono (Cofan.inj (Cofan.mk (∐ Z) (Sigma.ι Z)) i) :=
      (inferInstance : ∀ (i : α), Mono (Sigma.ι Z i))
    let i : K ≅ Discrete.functor (fun i ↦ op (Z i)) := Discrete.natIsoFunctor
    let _ : PreservesLimit (Discrete.functor (fun i ↦ op (Z i))) F :=
        Presieve.preservesProductOfIsSheafFor F ?_ initialIsInitial _ (coproductIsCoproduct Z)
        (FinitaryExtensive.isPullback_initial_to_sigma_ι Z)
        (hF (Presieve.ofArrows Z (fun i ↦ Sigma.ι Z i)) ?_)
    · exact preservesLimitOfIsoDiagram F i.symm
    · apply hF
      refine ⟨Empty, inferInstance, Empty.elim, IsEmpty.elim inferInstance, rfl, ⟨default,?_, ?_⟩⟩
      · ext b
        cases b
      · simp only [eq_iff_true_of_subsingleton]
    · refine ⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ?_⟩
      suffices Sigma.desc (fun i ↦ Sigma.ι Z i) = 𝟙 _ by rw [this]; infer_instance
      ext
      simp
  · let _ := hF.some
    rw [Presieve.isSheaf_coverage]
    intro _ R ⟨Y, hR⟩
    have _ : R.extensive := ⟨Y, hR⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts R F

end ExtensiveSheaves

end CategoryTheory
