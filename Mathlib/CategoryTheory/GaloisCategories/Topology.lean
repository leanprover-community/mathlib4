import Mathlib.CategoryTheory.GaloisCategories.Basic
import Mathlib.CategoryTheory.GaloisCategories.Prorepresantability
import Mathlib.Data.Rel

universe u v w

open CategoryTheory Limits Functor

namespace Galois

section Topology

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w})
  [PreGaloisCategory C] [FibreFunctor F]

def fundamentalGroup : Type (max u w) := Aut F

def autEmbedding (σ : Aut F) : (X : C) → Aut (F.obj X) := fun X => σ.app X

lemma autEmbedding_injective : Function.Injective (autEmbedding F) := by
  intro σ τ h
  apply Iso.ext
  apply NatTrans.ext σ.hom τ.hom
  ext X x
  have : σ.app X = τ.app X := congrFun h X
  rw [←Iso.app_hom, ←Iso.app_hom, this]

instance (X : C) : TopologicalSpace (F.obj X) := ⊥
instance (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩
instance (X : C) : TopologicalSpace (Aut (F.obj X)) := ⊥
instance (X : C) : DiscreteTopology (Aut (F.obj X)) := ⟨rfl⟩
instance : TopologicalSpace (Aut F) := TopologicalSpace.induced (autEmbedding F) inferInstance

lemma autEmbedding_range :
    Set.range (autEmbedding F) =
    { a | ∀ (X Y : C) (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F.map f } := by
  ext a
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  intro ⟨σ, h⟩
  rw [←h]
  exact σ.hom.naturality
  intro h
  use NatIso.ofComponents (fun X => (a X))
  aesop

lemma fundamentalGroup_closed : IsClosed (Set.range (autEmbedding F)) := by
  rw [autEmbedding_range]
  constructor
  apply isOpen_iff_forall_mem_open.mpr
  intro a h
  simp at h
  obtain ⟨X, Y, f, (h : (a Y).hom ∘ F.map f ≠ F.map f ∘ (a X).hom)⟩ := h
  rw [Function.ne_iff] at h
  obtain ⟨x, hx⟩ := h
  simp at hx
  let U : Set (Aut (F.obj X)) := { γ | γ.hom x = (a X).hom x }
  let V : Set (Aut (F.obj Y)) := { γ | γ.hom (F.map f x) = (a Y).hom (F.map f x) }
  have : IsOpen U := trivial
  have : IsOpen V := trivial
  let sx (A : C) : Set (Aut (F.obj A)) :=
    { γ | ∀ (h : X ⟶ A), γ.hom (F.map h x) = (a A).hom (F.map h x) }
  let sy (A : C) : Set (Aut (F.obj A)) :=
    { γ | ∀ (h : Y ⟶ A), γ.hom (F.map h (F.map f x)) = (a A).hom (F.map h (F.map f x)) }
  let Ix : Set C := {X}
  let Iy : Set C := {Y}
  let tx : Set (∀ A, Aut (F.obj A)) := Set.pi Ix sx
  let ty : Set (∀ A, Aut (F.obj A)) := Set.pi Iy sy
  have hx : IsOpen tx := isOpen_set_pi (Set.toFinite Ix) (fun _ _ => trivial)
  have hy : IsOpen ty := isOpen_set_pi (Set.toFinite Iy) (fun _ _ => trivial)
  let t : Set (∀ A, Aut (F.obj A)) := tx ∩ ty
  have : IsOpen t := IsOpen.inter hx hy
  use t
  refine ⟨?_, ?_, ?_⟩
  intro γ hγ
  simp at hγ
  simp
  use X
  use Y
  use f
  show (γ Y).hom ∘ F.map f ≠ F.map f ∘ (γ X).hom
  rw [Function.ne_iff]
  use x
  simp
  have hty : (γ Y).hom (F.map f x) = (a Y).hom (F.map f x) := by
    have := hγ.2 (𝟙 Y)
    simp at this
    assumption
  have htx : (γ X).hom x = (a X).hom x := by
    have := hγ.1 (𝟙 X)
    simp at this
    assumption
  rw [htx, hty]
  assumption
  assumption
  simp

def autEmbedding_embedding : ClosedEmbedding (autEmbedding F) where
  induced := rfl
  inj := autEmbedding_injective F
  closed_range := fundamentalGroup_closed F

instance (X Y : C) : Finite (F.obj X ⟶ F.obj Y) := by
  show Finite (F.obj X → F.obj Y)
  infer_instance

instance (X : C) : Finite (Aut (F.obj X)) := by
  have : Function.Injective (fun σ : Aut (F.obj X) ↦ σ.hom) := by
    intro σ τ h
    exact Iso.ext h
  exact Finite.of_injective _ this

instance : CompactSpace (∀ X, Aut (F.obj X)) := by
  have (X : C) : CompactSpace (Aut (F.obj X)) := Finite.compactSpace
  exact Pi.compactSpace

instance : CompactSpace (Aut F) := ClosedEmbedding.compactSpace (autEmbedding_embedding F)

instance (X : C) : T2Space (Aut (F.obj X)) := DiscreteTopology.toT2Space

instance : T2Space (∀ X, Aut (F.obj X)) := Pi.t2Space

instance (X : C) : TotallyDisconnectedSpace (Aut (F.obj X)) := inferInstance
instance : TotallyDisconnectedSpace (∀ X, Aut (F.obj X)) := inferInstance

instance : T2Space (Aut F) :=
  T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom

instance : TotallyDisconnectedSpace (Aut F) := by
  apply (Embedding.isTotallyDisconnected_range (autEmbedding_embedding F).embedding).mp
  exact isTotallyDisconnected_of_totallyDisconnectedSpace _

instance : Group (∀ X, Aut (F.obj X)) := inferInstance

instance : ContinuousMul (∀ X, Aut (F.obj X)) := inferInstance
instance : ContinuousInv (∀ X, Aut (F.obj X)) := inferInstance

def autEmbeddingMonoidHom : Aut F →* (∀ X, Aut (F.obj X)) := by
  apply MonoidHom.mk' (autEmbedding F)
  intro σ τ
  rfl

instance : ContinuousMul (Aut F) :=
  Inducing.continuousMul (autEmbeddingMonoidHom F)
    (autEmbedding_embedding F).toInducing

instance : ContinuousInv (Aut F) := by
  apply Inducing.continuousInv (autEmbedding_embedding F).toInducing
  intro σ
  rfl

instance : TopologicalGroup (Aut F) := ⟨⟩

instance (X : C) : SMul (Aut F) (F.obj X) := ⟨fun σ a => (σ.app X).hom a⟩
instance (X : C) : SMul (Aut (F.obj X)) (F.obj X) := ⟨fun σ a => σ.hom a⟩

instance (X : C) : ContinuousSMul (Aut (F.obj X)) (F.obj X) := by
  constructor
  continuity

instance (X : C) : ContinuousSMul (Aut F) (F.obj X) := by
  constructor
  let f : Aut F × F.obj X → F.obj X := fun ⟨σ, x⟩ => (σ.app X).hom x
  show Continuous f
  admit

end Topology

section Action

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{u})
  [PreGaloisCategory C] [FibreFunctor F]

def H : C ⥤ Action FintypeCat (MonCat.of (Aut F)) where
  obj X := {
    V := F.obj X
    ρ := MonCat.ofHom {
      toFun := fun (g : Aut F) => g.hom.app X
      map_one' := rfl
      map_mul' := by aesop
    }
  }
  map f := {
    hom := F.map f
    comm := by
      intro g
      exact symm <| g.hom.naturality f
  }

lemma lift_transitive_subobjects (X : C) (Y : FintypeCat) (i : Y ⟶ F.obj X)
    [Mono i] [MulAction (Aut F) Y] [MulAction.IsPretransitive (Aut F) Y]
    [Nonempty Y]
    (h : ∀ (σ : Aut F) (y : Y), i (σ • y) = σ • i y) :
    ∃ (Z : C) (f : Z ⟶ X) (u : F.obj Z ≅ Y),
    ConnectedObject Z ∧ Mono f ∧ u.hom ≫ i = F.map f := by
  obtain ⟨i, f, t, h1, h2, h3⟩ := hasDecompConnectedComponents F X
  have : X ≅ ∐ f := sorry
  have : F.obj (∐ f) ≅ ∐ fun j => F.obj (f j) := sorry
  admit

lemma lift_subobjects (X : C) (Y : FintypeCat) (i : Y ⟶ F.obj X)
      [Mono i] [MulAction (Aut F) Y]
      (h : ∀ (σ : Aut F) (y : Y), i (σ • y) = σ • i y)
    : ∃ (Z : C) (f : Z ⟶ X) (u : F.obj Z ≅ Y),
    Mono f ∧ u.hom ≫ i = F.map f :=
  sorry

lemma H_full : Full (H F) := by
  constructor
  intro X Y ⟨(f : F.obj X → F.obj Y), hf⟩
  --let Γ_s'' := Function.graph f
  let Γ_s' := { p : F.obj X × F.obj Y | p.2 = f p.1 }
  have : Finite Γ_s' := inferInstance
  have : Fintype Γ_s' := Fintype.ofFinite Γ_s'
  let Γ_s : FintypeCat := FintypeCat.of Γ_s'
  let u : Γ_s ⟶ prod (F.obj X) (F.obj Y) := sorry
  let i : Γ_s ⟶ F.obj (prod X Y) := sorry
  have : Mono i := sorry
  obtain ⟨Z, f, u, h1, h2⟩ := lift_subobjects F (prod X Y) Γ_s i
  admit
  admit

end Action

end Galois
