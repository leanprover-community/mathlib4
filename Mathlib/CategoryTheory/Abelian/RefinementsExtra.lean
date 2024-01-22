import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Sheaf

universe w v u

namespace CategoryTheory

open Opposite Limits

namespace Abelian

variable (C : Type u) [Category.{v} C] [Abelian C]

def refinementsTopology : GrothendieckTopology C where
  sieves X S := ∃ (T : C) (p : T ⟶ X) (_ : Epi p), S p
  top_mem' X := ⟨X, 𝟙 X, inferInstance, by simp⟩
  pullback_stable' X Y S f hS := by
    obtain ⟨T, p, hp, h⟩ := hS
    refine' ⟨pullback f p, pullback.fst, inferInstance, _⟩
    dsimp
    rw [pullback.condition]
    apply S.downward_closed h
  transitive' X S hS R hR := by
    obtain ⟨T, p, hp, h⟩ := hS
    obtain ⟨U, q, hq, h'⟩ := hR h
    exact ⟨_, q ≫ p, epi_comp _ _, h'⟩

end Abelian

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J (Type w)} (φ : F ⟶ G)

lemma mono_of_injective
    (hφ : ∀ (X : Cᵒᵖ), Function.Injective (fun (x : F.1.obj X) => φ.1.app _ x)) : Mono φ where
  right_cancellation := by
    intro H f₁ f₂ h
    ext Z x
    exact hφ Z (congr_fun (congr_app (congr_arg Sheaf.Hom.val h) Z) x)

lemma epi_of_locally_surjective (hφ : ∀ (X : Cᵒᵖ) (x : G.1.obj X),
    ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
    ∀ (Y : C) (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
    φ.1.app _ y = G.1.map f.op x) : Epi φ where
  left_cancellation := by
    intro H f₁ f₂ h
    ext X x
    obtain ⟨S, hS, hS'⟩ := hφ _ x
    apply ((Presieve.isSeparated_of_isSheaf _ _
      ((isSheaf_iff_isSheaf_of_type _ _).1 H.2)) S hS).ext
    intro Y f hf
    obtain ⟨y, hy⟩ := hS' Y f hf
    have h₁ := congr_fun (f₁.1.naturality f.op) x
    have h₂ := congr_fun (f₂.1.naturality f.op) x
    dsimp at h₁ h₂
    simp only [← h₁, ← h₂, ← hy]
    exact congr_fun (congr_app (congr_arg Sheaf.Hom.val h) (op Y)) y

namespace EpiMonoFactorization

@[simps]
def presheafI : Cᵒᵖ ⥤ Type w where
  obj X := { x : G.1.obj X | ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
    ∀ (Y : C) (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
      φ.1.app _ y = G.1.map f.op x }
  map {X X'} g a := ⟨G.1.map g a.1, by
    obtain ⟨S, hS, h⟩ := a.2
    refine' ⟨S.pullback g.unop, J.pullback_stable _ hS, fun Y f hf => _⟩
    obtain ⟨y, hy⟩ := h Y (f ≫ g.unop) hf
    exact ⟨y, by simp [hy]⟩⟩

@[simps]
def presheafι : presheafI φ ⟶ G.1 where
  app _ x := x.1
  naturality _ _ _ := rfl

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
    obtain ⟨y, hy⟩ := (α _ hb).2.choose_spec.choose_spec _ a ha
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

@[simps]
def ι : I φ ⟶ G := Sheaf.Hom.mk (presheafι φ)

@[simps]
def π : F ⟶ I φ where
  val :=
    { app := fun X x => ⟨φ.1.app X x, ⟨⊤, J.top_mem X.unop, fun Y f _ =>
        ⟨F.1.map f.op x, congr_fun (φ.val.naturality f.op) x⟩⟩⟩
      naturality := fun X X' g => by
        ext x
        exact Subtype.ext (congr_fun (φ.val.naturality g) x) }

instance : Epi (π φ) := by
  apply epi_of_locally_surjective
  intro X x
  obtain ⟨S, hS, hS'⟩ := x.2
  refine' ⟨S, hS, fun Y f hf => _⟩
  obtain ⟨y, hy⟩ := hS' Y f hf
  exact ⟨y, Subtype.ext hy⟩

instance : Mono (ι φ) := by
  apply mono_of_injective
  intro X x₁ x₂ h
  exact Subtype.ext h

@[reassoc (attr := simp)]
lemma π_ι : π φ ≫ ι φ = φ := rfl

end EpiMonoFactorization

end Sheaf

end CategoryTheory
