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

* `TopCat.Sheaf.IsFlasque.epi_of_shortExact_Γ_map`: Given a short exact sequence of sheaves,
  `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then `𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`.

* `TopCat.Sheaf.IsFlasque.X₃_shortExact_isFlasque_X₁_isFlasque_X₂`: Given a short exact sequence of
  sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque, then `𝓗` is flasque.

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
  epi : ∀{U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (F.map i)

namespace IsFlasque

instance (priority := low) [h : IsFlasque F]
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : Epi (F.map i) := h.epi i

theorem pushforward_isFlasque {Y : TopCat.{u}} [IsFlasque F] (f : X ⟶ Y) :
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

theorem pushforward_isFlasque {C : Type v} [Category.{w} C] {Y : TopCat.{u}} (F : Sheaf C X)
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
    by_cases hij : i = j
    · subst hij; rfl
    obtain h₁ | h₁ := h i.property j.property (fun h ↦ hij (SetCoe.ext_iff.mp h))
    · simp only [← CategoryOfElements.map_snd (Classical.choice h₁).2, Functor.comp_obj,
        Functor.comp_map, ConcreteCategory.forget_map_eq_coe,
        ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    · simp only [← CategoryOfElements.map_snd (Classical.choice h₁).2, Functor.comp_obj,
        Functor.comp_map, ConcreteCategory.forget_map_eq_coe, ← CategoryTheory.comp_apply,
        ← Functor.map_comp]
      rfl
  have le₁ : iSup f ≤ U := iSup_le <| fun j => leOfHom j.1.hom.1.unop
  have le₂ : ∀ i, i ∈ c → unop i.right.1 ≤ iSup f := fun i hi ↦ le_iSup f ⟨i, hi⟩
  use StructuredArrow.mk (CategoryOfElements.homMk _ _ (homOfLE le₁).op (eq_app_of_forall_eq ht
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
    (fun h₁ h₂ ↦ Nonempty.intro (Classical.choice h₂ ≫ Classical.choice h₁))
  have tle : t.right.1.unop ≤ U := leOfHom t.hom.1.unop
  have tcomp : s |_ t.right.1.unop = (ConcreteCategory.hom (S.g.hom.app t.right.1)) t.right.2 :=
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
    obtain ⟨t₃, ht₃⟩ := addCommGrpCat_mono_exact hS.1 hS.2 t₂ this
    -- Using that `S.X₁` is flasque, we can lift `t₃` to a section on `W`.
    obtain ⟨t₄, (ht₄ : t₄ |_ (t.right.1.unop ⊓ W) = t₃)⟩ := (AddCommGrpCat.epi_iff_surjective
      (S.X₁.obj.map (homOfLE inf_le_right).op)).mp inferInstance t₃
    let f : Fin 2 → Opens X
    | 0 => t.right.1.unop
    | 1 => W
    let sf : (i : Fin 2) → S.X₂.obj.obj (op (f i))
    | 0 => t.right.2
    | 1 => t₁ + (S.f.hom.app (op W)) t₄
    have : sf 0 |_ (t.right.1.unop ⊓ W) = sf 1 |_ (t.right.1.unop ⊓ W) := by
      rw [restrict_sum, ← map_restrict, ht₄]
      simp only [ht₃, t₂, Fin.isValue, add_sub_cancel]
      rfl
    -- We glue `t.right.2` and `t₁ + (S.f.hom.app (op W)) t₄` together to form `t₅`
    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.obj f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, this⟩, Eq.symm ?_, rfl⟩
      apply_fun (fun s ↦ restrictOpen s (W ⊓ t.right.1.unop) (le_of_eq (inf_comm _ _))) at this
      rw [restrict_restrict, restrict_restrict] at this
      exact this
    have le : iSup f ≤ U := by
      simp only [iSup_le_iff, Fin.forall_fin_two]
      exact ⟨tle, Wle⟩
    have comp : s |_ (iSup f) = S.g.hom.app (op (iSup f)) t₅:= by
      refine (eq_app_of_forall_eq ht₅ (by rw [Fin.forall_fin_two]; exact ⟨tle, Wle⟩) ?_).symm
      rw [Fin.forall_fin_two]
      refine ⟨tcomp.symm, ?_⟩
      change S.g.hom.app (op W) (t₁ + (S.f.hom.app (op W)) t₄) = s |_ W
      have : (S.f.hom.app (op W) ≫ S.g.hom.app (op W)) = 0 := by
        rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.6]; rfl
      simp [← ConcreteCategory.comp_apply, this, ht₁]
    -- We upgrade `t₅` to an object in `Under S.g s` that is defined on `t.right.1.unop ⊔ W`.
    let t₆ : Under S.g s := by
      refine StructuredArrow.mk (S := ⟨op U, s⟩)
        (T := (Functor.whiskerRight S.g.hom (CategoryTheory.forget AddCommGrpCat)).mapElements)
        (Y := ⟨op (iSup f), t₅⟩) ?_
      exact CategoryOfElements.homMk _ _ (homOfLE le).op comp
    -- We prove that `t₆` is bigger than `t` for the preorder used on `Under S.g s`.
    have : Nonempty (t₆ ⟶ t) := Nonempty.intro (StructuredArrow.homMk (CategoryOfElements.homMk _ _
      (homOfLE (le_iSup f 0)).op (ht₅ 0)) (by cat_disch))
    exact leOfHom (Classical.choice ((ht t₆) this)).right.1.unop ((le_iSup f 1) hW)
  use t.right.2 |_ U
  conv => rhs; equals (S.g.hom.app (op t.right.1.unop)) t.right.2 |_ U =>
    rw [← tcomp]
    dsimp
    change s = S.X₃.obj.map _ _
    erw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    conv_rhs => congr; congr; congr; equals 𝟙 _ => exact Subsingleton.elim _ _
    simp
  apply map_restrict

/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque,
then `𝓗` is flasque. -/
theorem X₃_shortExact_isFlasque_X₁_isFlasque_X₂ {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [IsFlasque S.X₁] [IsFlasque S.X₂] : IsFlasque S.X₃ where
  epi {U V} := fun i => by
    have : Epi (S.g.1.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app U) (S.X₃.obj.map i)

end TopCat.Sheaf.IsFlasque
