/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Flasque Sheaves

We define and prove basic properties about flasque sheaves on topological spaces.

## Main definition

* `TopCat.Sheaf.IsFlasque`: A sheaf is flasque if all of the restriction morphisms are epimorphisms.

## Main results

* `TopCat.Sheaf.IsFlasque.epi_of_shortExact`: Given a short exact sequence of sheaves,
  `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then `𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`.

* `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ `: Given a short exact sequence of
  sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque, then `𝓗` is flasque.

* `TopCat.Sheaf.IsFlasque.of_injective`: Injective sheaves are flasque.

* `TopCat.Sheaf.IsFlasque.H_isZero`: Flasque sheaves have no higher cohomology. For most
  applications, it is probably better to use `Subsingleton (H F (n + 1))` which can be proven by
  `infer_instance`

-/

@[expose] public section

universe u v w

open TopCat TopologicalSpace Opposite CategoryTheory Presheaf Limits
open scoped AlgebraicGeometry

variable {X : TopCat.{u}}

namespace TopCat

namespace Presheaf

variable {C : Type v} [Category.{w} C] (F : Presheaf C X)

/-- A sheaf is flasque if all of the restriction morphisms are epimorphisms. -/
class IsFlasque : Prop where
  epi : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (F.map i)

namespace IsFlasque

attribute [instance low] IsFlasque.epi

instance pushforward_isFlasque {Y : TopCat.{u}} [IsFlasque F] (f : X ⟶ Y) :
    IsFlasque (f _* F) where
  epi {U V} i := by
    simp only [pushforward_obj_obj, pushforward_obj_map]
    infer_instance

end IsFlasque

end Presheaf

namespace Sheaf

/-- A sheaf is flasque if it is flasque as a presheaf -/
abbrev IsFlasque {C : Type v} [Category.{w} C] (F : Sheaf C X) := Presheaf.IsFlasque F.obj

namespace IsFlasque

instance pushforward_isFlasque {C : Type v} [Category.{w} C] {Y : TopCat.{u}} (F : Sheaf C X)
    [IsFlasque F] (f : X ⟶ Y) : IsFlasque ((pushforward C f).obj F) :=
  Presheaf.IsFlasque.pushforward_isFlasque F.1 f

variable {U : Opens X} {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) (s : G.obj.obj (op U))

/-- Given a morphism of sheaves `g: F ⟶ G` and a section `s` of `G(U)`, `Under g s` is comprised of
an open `V` and a section of `F(V)` that maps to `s |_ V` via `g`. -/
abbrev Under := StructuredArrow ⟨op U, s⟩ (Functor.whiskerRight g.hom
  (CategoryTheory.forget AddCommGrpCat.{u})).mapElements

/- The next lemma proves that the relation `fun x y ↦ Nonempty (y ⟶ x)` on `Under g s`
satisfies the requirements for applying Zorn's lemma -/
lemma structured_arrows_elements_sheaf_chains_bounded (c : Set (Under g s))
    (h : IsChain (fun x y ↦ Nonempty (y ⟶ x)) c) : ∃ ub, ∀ a ∈ c, Nonempty (ub ⟶ a) := by
  let f : c → (Opens X) := fun x => x.1.right.1.unop
  obtain ⟨t, ht, _⟩ : ∃! s_1, IsGluing F.obj f (fun x => x.val.right.2) s_1 := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j ↦ ?_)
    obtain (rfl | h₁ | h₁) : i = j ∨ Nonempty (i.val ⟶ j.val) ∨ Nonempty (j.val ⟶ i.val) := by
      grind [h i.property j.property]
    · rfl
    all_goals
      simp only [← CategoryOfElements.map_snd h₁.some.2, Functor.comp_obj,
        Functor.comp_map, ConcreteCategory.forget_map_eq_coe, ← CategoryTheory.comp_apply,
        ← Functor.map_comp]
      rfl
  have le₁ : iSup f ≤ U := iSup_le <| fun j => leOfHom j.1.hom.1.unop
  have le₂ : ∀ i, i ∈ c → unop i.right.1 ≤ iSup f := fun i hi ↦ le_iSup f ⟨i, hi⟩
  use StructuredArrow.mk (CategoryOfElements.homMk _ _ (homOfLE le₁).op (eq_app_of_locally_eq ht
      (fun i ↦ leOfHom i.1.hom.1.unop) (fun i ↦ (CategoryOfElements.map_snd i.1.hom).symm)).symm :
      ⟨op U, s⟩ ⟶ (Functor.whiskerRight g.hom
      (CategoryTheory.forget AddCommGrpCat)).mapElements.obj ⟨op (iSup f), t⟩)
  exact fun i hi => Nonempty.intro (StructuredArrow.homMk (CategoryOfElements.homMk _ _
    (homOfLE (le₂ i hi)).op (ht ⟨i, hi⟩)) (by cat_disch))

set_option backward.isDefEq.respectTransparency false in
/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then
`𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`. -/
theorem epi_of_shortExact {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] : Epi (S.g.1.app (op U)) := by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s ↦ ?_)
  -- We want to find a preimage of `s` by `S.g`.
  -- We apply Zorn's lemma to obtain a term `t` of `Under S.g s` that is maximal.
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (structured_arrows_elements_sheaf_chains_bounded S.g s)
    (fun ⟨f⟩ ⟨g⟩ ↦ ⟨g ≫ f⟩)
  have tle : t.right.1.unop ≤ U := leOfHom t.hom.1.unop
  have tcomp : s |_ t.right.1.unop = S.g.hom.app t.right.1 t.right.2 :=
      CategoryOfElements.map_snd t.hom
  -- We get a section `t.right.2` of `S.g` defined on an open subset `t.right.1.unop` of `U`,
  -- that is sent to the restriction of `s` by `S.g`.
  have : U ≤ t.right.1.unop := by
  -- Prove that the set of definition of `t.right.2` contains `U`.
    intro x hx
    have := (isLocallySurjective_iff_epi S.g).mpr hS.epi_g
    -- We use local surjectivity to find a section `t₁` of `S.X₂` on a neighborhood `W` of `x`
    -- that maps to `s |_ W` by `S.g`.
    obtain ⟨W, Wle, ⟨t₁, ht₁⟩, hW⟩ := (isLocallySurjective_iff S.g.hom).mp this U s x hx
    --`t.right.2` and `t₁` need not agree on their overlap so we need to deal with their
    -- difference `t₂`
    let t₂ := t.right.2 |_ (t.right.1.unop ⊓ W) - t₁ |_ (t.right.1.unop ⊓ W)
    have : (S.g.hom.app (op (t.right.1.unop ⊓ W))) t₂ = 0 := by
      simp [map_restrict, ← tcomp, restrict_restrict, ht₁, t₂]
    -- Since `S` is exact and `t₂` maps to zero, we can lift it to a section `t₃` of `S.X₁`
    obtain ⟨t₃, ht₃⟩ := Sheaf.sections_exact_of_left_exact hS.1 hS.2 t₂ this
    -- Using that `S.X₁` is flasque, we can lift `t₃` to a section on `W`.
    obtain ⟨t₄, (ht₄ : t₄ |_ (t.right.1.unop ⊓ W) = t₃)⟩ := (AddCommGrpCat.epi_iff_surjective
      (S.X₁.obj.map (homOfLE inf_le_right).op)).mp inferInstance t₃
    let f : Fin 2 → Opens X := ![t.right.1.unop, W]
    let sf : (i : Fin 2) → S.X₂.obj.obj (op (f i))
    | 0 => t.right.2
    | 1 => t₁ + (S.f.hom.app (op W)) t₄
    have : sf 0 |_ (t.right.1.unop ⊓ W) = sf 1 |_ (t.right.1.unop ⊓ W) := by
      dsimp [sf, f]
      simp only [restrict_sum, ← map_restrict, ht₄, ht₃, t₂, add_sub_cancel]
    -- We glue `t.right.2` and `t₁ + (S.f.hom.app (op W)) t₄` together to form `t₅`
    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.obj f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, this⟩, Eq.symm ?_, rfl⟩
      apply_fun (fun s ↦ restrictOpen s (W ⊓ t.right.1.unop) (le_of_eq (inf_comm _ _))) at this
      rw [restrict_restrict, restrict_restrict] at this
      exact this
    have le : iSup f ≤ U := iSup_le_iff.mpr (Fin.forall_fin_two.mpr ⟨tle, Wle⟩)
    -- We upgrade `t₅` to an object in `Under S.g s` that is defined on `t.right.1.unop ⊔ W`.
    let t₆ : Under S.g s :=
      StructuredArrow.mk (S := ⟨op U, s⟩)
        (T := (Functor.whiskerRight S.g.hom (CategoryTheory.forget AddCommGrpCat)).mapElements)
        (Y := ⟨op (iSup f), t₅⟩) <| CategoryOfElements.homMk _ _ (homOfLE le).op (by
          refine (eq_app_of_locally_eq ht₅ (by rw [Fin.forall_fin_two]; exact ⟨tle, Wle⟩) ?_).symm
          rw [Fin.forall_fin_two]
          refine ⟨tcomp.symm, ?_⟩
          simp only [Fin.isValue, Functor.comp_obj, map_add, homOfLE_leOfHom, sf, f]
          have : (S.f.hom.app (op W) ≫ S.g.hom.app (op W)) = 0 := by
            rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
            rfl
          simp [← CategoryTheory.comp_apply, this, ht₁]
          rfl)
    -- We prove that `t₆` is bigger than `t` for the preorder used on `Under S.g s`.
    have : Nonempty (t₆ ⟶ t) := Nonempty.intro (StructuredArrow.homMk (CategoryOfElements.homMk _ _
      (homOfLE (le_iSup f 0)).op (ht₅ 0)) (by cat_disch))
    exact leOfHom ((ht t₆) this).some.right.1.unop ((le_iSup f 1) hW)
  exact ⟨t.right.2 |_ U, by simp [map_restrict, ← tcomp, restrict_restrict]⟩

/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque,
then `𝓗` is flasque. -/
theorem of_shortExact_of_isFlasque₁₂ {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [IsFlasque S.X₁] [IsFlasque S.X₂] : IsFlasque S.X₃ where
  epi {U V} i := by
    have : Epi (S.g.1.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app U) (S.X₃.obj.map i)

noncomputable section

def freeAbSheaf (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf _ _).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

def freeAbSheafMap {U V : Opens X} (i : U ⟶ V) : freeAbSheaf U ⟶ freeAbSheaf V :=
  (presheafToSheaf _ _).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

def freeAbSheafHomEquiv (U : Opens X) (I : Sheaf AddCommGrpCat.{u} X) :
    (freeAbSheaf U ⟶ I) ≃ I.obj.obj (op U) :=
  ((sheafificationAdjunction _ _).homEquiv (yoneda.obj U ⋙ AddCommGrpCat.free) I).trans <|
    ((AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj U)
    (sheafToPresheaf _ _ |>.obj I)).trans <|
      yonedaEquiv

set_option backward.isDefEq.respectTransparency false in
lemma freeAbSheafHomEquiv_naturality {U V : Opens X} (i : U ⟶ V)
    (I : Sheaf AddCommGrpCat.{u} X) (f : freeAbSheaf V ⟶ I) :
    freeAbSheafHomEquiv U I (freeAbSheafMap i ≫ f) =
      I.obj.map i.op (freeAbSheafHomEquiv V I f) := by
  dsimp [freeAbSheafHomEquiv, freeAbSheafMap, yonedaEquiv]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  convert (NatTrans.naturality ((Adjunction.whiskerRight _ AddCommGrpCat.adj).homEquiv _ _
    ((sheafificationAdjunction _ _).homEquiv _ I f)) i.op) using 1
  exact ⟨fun _ => (NatTrans.naturality ((Adjunction.whiskerRight _ _).homEquiv _ _ _) i.op),
    fun h => congr_arg (fun g => g (𝟙 V)) h⟩

set_option backward.isDefEq.respectTransparency false in
instance freeAbSheafMap_mono {U V : Opens X} (i : U ⟶ V) :
    Mono (freeAbSheafMap i) :=
  haveI : PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) := HasSheafify.isLeftExact
  Functor.map_mono _ _

end

-- Injective sheaves are flasque (proved by Aristotle 8f42abaa).
-- Uses free abelian sheaf + Yoneda identification + Injective.factors.
instance of_injective {X : TopCat.{u}}
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasque I where
  epi := by
    intro U V i
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    obtain ⟨h, hh⟩ :=
      Injective.factors ((freeAbSheafHomEquiv (unop V) I).symm s) (freeAbSheafMap i.unop)
    exact ⟨freeAbSheafHomEquiv (unop U) I h, by
      erw [← freeAbSheafHomEquiv_naturality i.unop I h, hh]
      simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- Flasque sheaves have no higher cohomology. For most applications, it is probably better to use
`Subsingleton (H F (n + 1))` which can be proven by `TopCat.Sheaf.IsFlasque.subsingleton_H` -/
theorem H_isZero (F : Sheaf AddCommGrpCat X) [IsFlasque F] (n : ℕ) :
    IsZero (AddCommGrpCat.of (H F (n+1))) := by
  induction n generalizing F with
  | zero =>
    obtain ⟨I, _, f, hf⟩ := CategoryTheory.EnoughInjectives.presentation F
    let S := ShortComplex.mk f (cokernel.π f) (by cat_disch)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
    have hLS := Sheaf.H.longSequence_exact hS 0 1 rfl
    refine ShortComplex.Exact.isZero_of_both_zeros (hLS.exact 2) ?_
      (zero_of_target_iso_zero _ (IsZero.isoZero (AddCommGrpCat.isZero_of_subsingleton
      (AddCommGrpCat.of (H I 1)))))
    rw[← ShortComplex.Exact.epi_f_iff (hLS.exact 1), AddCommGrpCat.epi_iff_surjective,
      ← Equiv.surjective_comp (H.equiv₀ I).symm.toEquiv]
    change Function.Surjective ((H.map S.g 0) ∘ (H.equiv₀ I).symm.toEquiv)
    conv => right; equals (H.equiv₀ S.X₃).symm.toEquiv ∘ S.g.hom.app (op ⊤)
      => ext x; exact Sheaf.H.equiv₀_symm_naturality Limits.isTerminalTop S.g x
    rw [Equiv.comp_surjective, ← AddCommGrpCat.epi_iff_surjective]
    exact epi_of_shortExact hS
  | succ n hn =>
    obtain ⟨I, _, f, hf⟩ := CategoryTheory.EnoughInjectives.presentation F
    have hS := ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
    haveI := of_shortExact_of_isFlasque₁₂ hS
    exact ShortComplex.Exact.isZero_of_both_isZero
      ((Sheaf.H.longSequence_exact hS (n+1) (n+2) rfl).exact 2) (hn _)
      (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (H I (n + 2))))

instance subsingleton_H {F : Sheaf AddCommGrpCat X} [IsFlasque F] (n : ℕ) :
    Subsingleton (H F (n + 1)) :=
  AddCommGrpCat.subsingleton_of_isZero (H_isZero F n)

end TopCat.Sheaf.IsFlasque
