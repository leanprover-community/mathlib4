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
abbrev IsFlasque {C : Type v} [Category.{w} C] (F : Sheaf C X) := Presheaf.IsFlasque F.val

namespace IsFlasque

theorem pushforward_isFlasque {C : Type v} [Category.{w} C] {Y : TopCat.{u}} (F : Sheaf C X)
    [IsFlasque F] (f : X ⟶ Y) : IsFlasque ((pushforward C f).obj F) :=
  Presheaf.IsFlasque.pushforward_isFlasque F.1 f

variable {U : Opens X} {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) (s : G.val.obj (op U))

/-- Given a morphism of sheaves `g: F ⟶ G` and a section `s` of `G(U)`, `Under g s` is comprised of
an open `V` and a section of `F(V)` that maps to `s |_ V` via `g`. This is not likely to be useful
elsewhere so we leave it in the `IsFlasque` namespace. -/
structure Under : Type u where
  /-- the open subset that our section is on -/
  V : Opens X
  /-- V must be contained in U -/
  le : V ≤ U
  /-- the section itself -/
  sec : F.val.obj (op V)
  /-- `sec` must be "under s" in the sense that `g` applied to `sec` is `s |_ V` -/
  app_s : g.val.app (op V) sec = s |_ V

/-- Given `t₁` and `t₂` in `Under g s`, we say `t₁ ≤ t₂` if `t₂.sec` restricts to `t₁.sec` -/
structure Under.R (t₁ t₂ : Under g s) : Prop where
  /-- inclusion of the opens that the sections live on -/
  le : t₁.V ≤ t₂.V
  /-- the second section restricts to the first -/
  restricts : t₂.sec |_ t₁.V = t₁.sec

open Under

/- The next two lemmas prove that the relation `R` satisfies the requirements for applying Zorn's
lemma -/
lemma Under.R.trans {a b c : Under g s} (h1 : (R g s) a b) (h2 : (R g s) b c) : (R g s) a c := by
  apply R.mk (le_trans h1.le h2.le)
  rw [← h1.restricts, ← h2.restricts]
  exact Eq.symm (restrict_restrict h1.le h2.le c.sec)

lemma Under.R.chains_bounded (c : Set (Under g s)) (h : IsChain (R g s) c) :
    ∃ ub, ∀ a ∈ c, (R g s) a ub := by
  let f : c → (Opens X) := fun x => x.val.V
  obtain ⟨t, ht, _⟩ : ∃! s_1, IsGluing F.val f (fun x => x.val.sec) s_1 := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j ↦ ?_)
    by_cases hij : i = j
    · subst hij; rfl
    obtain h1 | h1 := h i.property j.property (by grind)
    · rw [← h1.restricts]
      have := h1.le
      change (j.1.sec |_ i.1.V) |_ ((f i) ⊓ (f j)) = j.1.sec |_ ((f i) ⊓ (f j))
      rw [restrict_restrict]
    · rw [← h1.restricts]
      have := h1.le
      change i.1.sec |_ ((f i) ⊓ (f j)) = (i.1.sec |_ j.1.V) |_ ((f i) ⊓ (f j))
      rw [restrict_restrict]
  use ⟨iSup f, iSup_le <| fun j => j.1.le, t, eq_app_of_forall_eq ht _ (fun i => i.val.app_s)⟩
  exact fun a ha => ⟨_, ht ⟨a, ha⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then
`𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`. -/
theorem epi_of_shortExact {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] : Epi (S.g.1.app (op U)) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  -- We apply Zorn's lemma to obtain a term `t` of `Under S.g s` that is maximal.
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded (R.chains_bounded S.g s) (R.trans S.g s)
  have : U ≤ t.V := by
    intro x hx
    have := (isLocallySurjective_iff_epi S.g).mpr hS.epi_g
    -- We use local surjectivity to find a section of `S.X₂` on a neighborhood `W` of `x` that maps
    -- to `s |_ W`
    obtain ⟨W, Wle, ⟨t₁, ht₁⟩, hW⟩ := (isLocallySurjective_iff S.g.val).mp this U s x hx
    --`t.sec` and `t₁` need not agree on their overlap so we need to deal with their difference `t₂`
    let t₂ := t.sec |_ (t.V ⊓ W) - t₁ |_ (t.V ⊓ W)
    have : (S.g.val.app (op (t.V ⊓ W))) t₂ = 0 := by
      simp [map_restrict, t.app_s, restrict_restrict, ht₁, t₂]
    -- Since `S` is exact and `t₂` maps to zero, we can lift it to a section `t₃` of `S.X₁`
    obtain ⟨t₃, ht₃⟩ := addCommGrpCat_mono_exact hS.1 hS.2 t₂ this
    have i₁ : t.V ⊓ W ⟶ W := homOfLE inf_le_right
    -- Using that `S.X₁` is flasque, we can lift `t₃` to a section on `W`
    obtain ⟨t₄, (ht₄ : t₄ |_ (t.V ⊓ W) = t₃)⟩ :=
      (AddCommGrpCat.epi_iff_surjective (S.X₁.val.map i₁.op)).mp inferInstance t₃
    let f : Fin 2 → Opens X
    | 0 => t.V
    | 1 => W
    let sf : (i : Fin 2) → S.X₂.val.obj (op (f i))
    | 0 => t.sec
    | 1 => t₁ + (S.f.val.app (op W)) t₄
    have : sf 0 |_ (t.V ⊓ W) = sf 1 |_ (t.V ⊓ W) := by
      rw [restrict_sum, ← map_restrict, ht₄]
      simp only [ht₃, t₂, Fin.isValue, add_sub_cancel]
      rfl
    -- We glue `t.sec` and `t₁ + (S.f.val.app (op W)) t₄` together to form `t₅`
    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.val f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      exact ⟨⟨rfl, this⟩, Eq.symm (restrict_inf_flip this), rfl⟩
    have le : iSup f ≤ U := by
      simp only [iSup_le_iff, Fin.forall_fin_two]
      exact ⟨t.le, Wle⟩
    have app : S.g.val.app (op (iSup f)) t₅ = s |_ (iSup f) := by
      apply eq_app_of_forall_eq ht₅ (by rw [Fin.forall_fin_two]; exact ⟨t.le, Wle⟩)
      rw [Fin.forall_fin_two]
      refine ⟨t.app_s, ?_⟩
      change S.g.val.app (op W) (t₁ + (S.f.val.app (op W)) t₄) = s |_ W
      have : (S.f.val.app (op W) ≫ S.g.val.app (op W)) = 0 := by
        change (S.f ≫ S.g).val.app (op W) = 0; rw [S.6]; rfl
      simp [← ConcreteCategory.comp_apply, this, ht₁]
    let t₆ : Under S.g s := ⟨iSup f, le, t₅, app⟩
    exact (ht t₆ ⟨_, ht₅ 0⟩).le (by cat_disch)
  use t.sec |_ U
  conv => rhs; equals (S.g.val.app (op t.V)) t.sec |_ U =>
    rw [t.app_s, restrict_restrict, restrictOpen, restrict]
    cat_disch
  apply map_restrict

/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque,
then `𝓗` is flasque. -/
theorem X₃_shortExact_isFlasque_X₁_isFlasque_X₂ {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [IsFlasque S.X₁] [IsFlasque S.X₂] : IsFlasque S.X₃ where
  epi {U V} := fun i => by
    have : Epi (S.g.1.app U ≫ S.X₃.val.map i) := by
      rw [← S.g.val.naturality i]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app U) (S.X₃.val.map i)

end TopCat.Sheaf.IsFlasque
