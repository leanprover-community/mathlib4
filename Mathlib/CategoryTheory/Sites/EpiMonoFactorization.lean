/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.LocallySurjective
/-!
# Epi-mono factorization for morphisms between sheaves of types

In this file, given a morphism `φ : F ⟶ G` in a category of sheaves
of types `Sheaf J (Type w)`, we construct a factorization
`π φ ≫ ι φ = φ` with an epi `π φ` and a mono `ι φ`
(see `CategoryTheory.Sheaf.EpiMonoFactorization.π_ι`).
By construction, the epimorphism `π φ` is locally surjective: this fact
shall be used in order to show that `φ` is an epi iff it is locally surjective.

-/

universe w v u

namespace CategoryTheory

open Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J (Type w)} (φ : F ⟶ G)

namespace EpiMonoFactorization

/-- The underlying presheaf of the image of a sheaf of types, which consists of sections
of the target sheaf which can be locally lifted to the source sheaf. -/
@[simps]
def presheafI : Cᵒᵖ ⥤ Type w where
  obj X := { x : G.1.obj X | ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
    ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
      φ.1.app _ y = G.1.map f.op x }
  map {X X'} g a := ⟨G.1.map g a.1, by
    obtain ⟨S, hS, h⟩ := a.2
    refine' ⟨S.pullback g.unop, J.pullback_stable _ hS, fun Y f hf => _⟩
    obtain ⟨y, hy⟩ := h (f ≫ g.unop) hf
    exact ⟨y, by simp [hy]⟩⟩

/-- The inclusion of the image of a morphism of sheaves of types, as a morpshim of presheaves. -/
@[simps]
def presheafι : presheafI φ ⟶ G.1 where
  app _ x := x.1
  naturality _ _ _ := rfl

/-- The image of a morphism of sheaves of types. -/
@[simps]
def I : Sheaf J (Type w) := ⟨presheafI φ, by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS α hα
  have hS' := (((isSheaf_iff_isSheaf_of_type _ _).1 G.2) _ hS)
  refine' ⟨⟨hS'.amalgamate _
    (hα.compPresheafMap (presheafι φ)), _⟩, _, _⟩
  · let U := fun ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S.arrows f) => (α f hf).2.choose
    have hU : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S.arrows f), U hf ∈ J _:= fun Y f hf =>
        (α f hf).2.choose_spec.choose
    refine' ⟨_, J.bind_covering hS hU, fun Y f hf => _⟩
    obtain ⟨T, a, b, hb, ha : U hb a, fac⟩ := hf
    obtain ⟨y, hy⟩ := (α _ hb).2.choose_spec.choose_spec _ ha
    refine' ⟨y, _⟩
    have hf : S.arrows f := by
      rw [← fac]
      apply S.downward_closed hb
    rw [hy, Presieve.IsSheafFor.valid_glue hS' (hα.compPresheafMap (presheafι φ)) f hf]
    simpa using (hα.compPresheafMap (presheafι φ)) a (𝟙 _) hb hf (by simpa using fac)
  · intro Y f hf
    apply Subtype.ext
    apply Presieve.IsSheafFor.valid_glue hS' (hα.compPresheafMap (presheafι φ))
  · rintro ⟨y, _⟩ hy
    apply Subtype.ext
    apply ((Presieve.isSeparated_of_isSheaf _ _
      ((isSheaf_iff_isSheaf_of_type _ _).1 G.2)) S hS).ext
    intro Y f hf
    dsimp
    replace hy := hy f hf
    rw [Subtype.ext_iff] at hy
    dsimp at hy
    rw [hy]
    symm
    apply Presieve.IsSheafFor.valid_glue⟩

/-- The inclusion of the image of a morphism of sheaves of types. -/
@[simps]
def ι : I φ ⟶ G := Sheaf.Hom.mk (presheafι φ)

/-- The projection to the image of a morphism of sheaves of types. -/
@[simps]
def π : F ⟶ I φ where
  val :=
    { app := fun X x => ⟨φ.1.app X x, ⟨⊤, J.top_mem X.unop, fun Y f _ =>
        ⟨F.1.map f.op x, congr_fun (φ.val.naturality f.op) x⟩⟩⟩
      naturality := fun X X' g => by
        ext x
        exact Subtype.ext (congr_fun (φ.val.naturality g) x) }

instance locallySurjective_π : LocallySurjective (π φ) where
  locally_surjective x := by
    obtain ⟨S, hS, hS'⟩ := x.2
    refine ⟨S, hS, fun f hf => ?_⟩
    obtain ⟨y, hy⟩ := hS' f hf
    exact ⟨y, Subtype.ext hy⟩

instance : Epi (π φ) := epi_of_locallySurjective _

instance locallyInjective_ι : LocallyInjective (ι φ) where
  locally_injective := by
    rintro X ⟨x, hx⟩ ⟨_, _⟩ rfl
    exact ⟨⊤, J.top_mem X.unop, fun _ _ => rfl⟩

instance : Mono (ι φ) := mono_of_locallyInjective _

@[reassoc (attr := simp)]
lemma π_ι : π φ ≫ ι φ = φ := rfl

instance [Epi φ] : Epi (ι φ) := epi_of_epi_fac (π_ι φ)

end EpiMonoFactorization

end Sheaf

end CategoryTheory
