/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Sheaves of abelian groups.

Results for sheaves of abelian groups on topological spaces.

## Main definitions

* `TopCat.Sheaf.H`: The cohomology of a sheaf of abelian groups in degree `n`

* `TopCat.Sheaf.H.map`: Given a morphism `𝓕 ⟶ 𝓖`, we get an induced morphism on cohomology
  `H 𝓕 n ⟶ H 𝓖 n`

* `TopCat.Sheaf.H.equiv₀`: The equivalence between `H F 0` and the global sections of `F`. This is
  shown to be natural in `TopCat.Sheaf.H.equiv₀_comp`.

-/

@[expose] public section

universe u

open TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

namespace TopCat

variable {X : TopCat.{u}} {U : Opens X}

set_option backward.isDefEq.respectTransparency false in
theorem Presheaf.addCommGrpCat_shortExact_app_zero {S : ShortComplex (Presheaf AddCommGrpCat.{u} X)}
    (hS : S.Exact) {s : S.X₂.obj (op U)} (h : S.g.app (op U) s = 0) :
    ∃(t : S.X₁.obj (op U)), S.f.app (op U) t = s := by
  dsimp [Presheaf] at S
  let F := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  apply (ShortComplex.ab_exact_iff (S.map F)).mp
  · have := ((Functor.exact_tfae F).out 1 3).mpr
    exact this ⟨inferInstance, inferInstance⟩ S hS
  exact h

lemma Presheaf.restrict_sum {V : Opens X} {F : Presheaf AddCommGrpCat X} (h : V ≤ U)
    (s t : F.obj (op U)) : (s + t) |_ V = s |_V + t |_V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  cat_disch

lemma Sheaf.addCommGrpCat_shortExact_app_zero {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.Exact) (hf : Mono S.f) (s : S.X₂.obj.obj (op U)) (h : S.g.hom.app (op U) s = 0) :
    ∃(t : S.X₁.obj.obj (op U)), S.f.hom.app (op U) t = s := by
  have := ((Functor.preservesFiniteLimits_tfae (forget AddCommGrpCat X)).out 1 3).mpr
    (inferInstanceAs (Limits.PreservesFiniteLimits (forget AddCommGrpCat X)))
  exact Presheaf.addCommGrpCat_shortExact_app_zero (this S ⟨hS, hf⟩).left h

namespace Sheaf

noncomputable section

/-- The documention for `HasExt` says to be very careful about making instances of it so we only
make this instance for `AddCommGrpCat`. -/
instance : HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives _

/-- The cohomology of a sheaf of abelian groups in degree `n`. -/
abbrev H (F : (Sheaf AddCommGrpCat.{u} X)) (n : ℕ) : Type u := CategoryTheory.Sheaf.H F n

variable {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)

/-- Given a morphism `𝓕 ⟶ 𝓖`, we get an induced morphism on cohomology `H 𝓕 n ⟶ H 𝓖 n` -/
abbrev H.map (n : ℕ) : H F n →+ H G n :=
    CategoryTheory.Sheaf.H.map f n

instance {n : ℕ} : AddCommGroup (H F n) :=
  inferInstanceAs <| AddCommGroup <| CategoryTheory.Sheaf.H _ _

variable (F) in
set_option backward.isDefEq.respectTransparency false in
instance {n : ℕ} [Injective F] : Subsingleton (H F (n + 1)) :=
  inferInstanceAs <| Subsingleton (CategoryTheory.Sheaf.H F (n + 1))

variable (F) in
set_option backward.isDefEq.respectTransparency false in
/-- `H F 0` is equivalent to taking global sections. -/
abbrev H.equiv₀ : H F 0 ≃+ F.obj.obj (op ⊤) :=
    CategoryTheory.Sheaf.H.equiv₀ F Limits.isTerminalTop

set_option backward.isDefEq.respectTransparency false in
/-- `H.equiv₀` is natural. -/
theorem H.equiv₀_naturality (x : H F 0) :
    f.hom.app (op ⊤) ((H.equiv₀ F) x) = H.equiv₀ G (H.map f 0 x) :=
  CategoryTheory.Sheaf.H.equiv₀_naturality Limits.isTerminalTop f x

set_option backward.isDefEq.respectTransparency false in
theorem H.equiv₀_symm_naturality (x : F.obj.obj (op ⊤)) :
    H.map f 0 ((H.equiv₀ F).symm x) = (H.equiv₀ G).symm (f.hom.app (op ⊤) x)
  := CategoryTheory.Sheaf.H.equiv₀_symm_naturality Limits.isTerminalTop f x

@[simp]
lemma H.map_id_apply {n : ℕ} (x : H F n) : H.map (𝟙 F) n x = x :=
  CategoryTheory.Sheaf.H.map_id_apply x

lemma H.map_comp_apply {n : ℕ} {G' : Sheaf AddCommGrpCat.{u} X} (g : G ⟶ G') (x : H F n) :
    H.map (f ≫ g) n x = H.map g n (H.map f n x) :=
  CategoryTheory.Sheaf.H.map_comp_apply f g x

attribute [local simp] H.map_comp_apply in
variable (X) in
/-- `H` as a functor. -/
@[simps!]
noncomputable abbrev functorH (n : ℕ) : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.functorH _ n

instance (n : ℕ) : (functorH X n).Additive :=
  inferInstanceAs (CategoryTheory.Sheaf.functorH _ n).Additive

end

end TopCat.Sheaf
