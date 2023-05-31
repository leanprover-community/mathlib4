import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.CompHaus.Basic

open CategoryTheory Limits

namespace CompHaus

namespace EffectiveEpiFamily

universe u

variable {α : Type} [Fintype α] {B : CompHaus.{u}}
  (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

def Pullback {X Y B : CompHaus.{u}} (f : X ⟶ B) (g : Y ⟶ B) : CompHaus.{u} :=
  letI set := { xy : X × Y | f xy.1 = g xy.2 }
  haveI : CompactSpace set := sorry
  CompHaus.of set

def Pullback.fst {X Y B : CompHaus.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    Pullback f g ⟶ X where
  toFun := fun ⟨⟨x,y⟩,h⟩ => x
  continuous_toFun := sorry

def Pullback.snd {X Y B : CompHaus.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    Pullback f g ⟶ Y where
  toFun := fun ⟨⟨x,y⟩,h⟩ => y
  continuous_toFun := sorry

def DisjointUnion : CompHaus.{u} := CompHaus.of <| Σ (a : α), X a

variable {X}

def Relation : Setoid (DisjointUnion X) where
  r a b := ∃ (Z : CompHaus.{u}) (z : Z)
    (fst : Z ⟶ X a.fst) (snd : Z ⟶ X b.fst) (w : fst ≫ π _ = snd ≫ π _),
    fst z = a.snd ∧ snd z = b.snd
  iseqv := by
    constructor
    · rintro ⟨a,x⟩
      refine ⟨X a, x, 𝟙 _, 𝟙 _, by simp, rfl, rfl⟩
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨Z,z,fst,snd,w,h1,h2⟩
      exact ⟨Z,z,snd,fst,w.symm,h2,h1⟩
    · rintro ⟨a,x⟩ ⟨b,y⟩ ⟨z,c⟩ ⟨Z,z,fstZ,sndZ,hZ,hZ1,hZ2⟩ ⟨W,w,fstW,sndW,hW,hW1,hW2⟩
      refine ⟨Pullback sndZ fstW, ⟨⟨z,w⟩, by simp [hZ2, hW1]⟩,
        Pullback.fst _ _ ≫ fstZ, Pullback.snd _ _ ≫ sndW, ?_, hZ1, hW2⟩
      dsimp at *
      simp only [Category.assoc, hZ, ← hW]
      apply ContinuousMap.ext
      rintro ⟨⟨u,v⟩,h⟩
      change π b (sndZ u) = π b (fstW v)
      rw [h]

def ι_fun : Quotient (Relation π) → B :=
  Quotient.lift (fun ⟨a,x⟩ => π a x) sorry

lemma ι_fun_continuous : Continuous (ι_fun π) := by
  apply Continuous.quotient_lift
  apply continuous_sigma
  intro a
  exact (π a).continuous

lemma ι_fun_injective : (ι_fun π).Injective := sorry

def QB : CompHaus.{u} :=
  haveI : T2Space (Quotient <| Relation π) :=
    ⟨fun _ _ h => separated_by_continuous (ι_fun_continuous π) <| (ι_fun_injective π).ne h ⟩
  CompHaus.of (Quotient <| Relation π)

def ι_hom : (QB π) ⟶ B := ⟨ι_fun π, ι_fun_continuous π⟩

noncomputable
def ι : (QB π) ≅ B :=
  haveI : IsIso (ι_hom π) := by
    apply isIso_of_bijective
    refine ⟨ι_fun_injective _, ?_⟩
    intro b
    obtain ⟨a,x,h⟩ := surj b
    refine ⟨Quotient.mk _ ⟨a,x⟩, h⟩
  asIso (ι_hom π)

def π' : (a : α) → (X a ⟶ QB π) := fun a =>
  { toFun := fun x => Quotient.mk _ ⟨a, x⟩
    continuous_toFun := by
      apply Continuous.comp
      apply continuous_quot_mk
      apply continuous_sigmaMk (σ := fun a => X a) }

def struct_aux : EffectiveEpiFamilyStruct X (π' π) where
  desc := fun {W} e h => {
    toFun := Quotient.lift (fun ⟨a,x⟩ => e a x) sorry
    continuous_toFun := sorry
  }
  fac := sorry
  uniq := sorry

noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => (ι π surj).inv ≫ (struct_aux π).desc e sorry
  fac := sorry
  uniq := sorry

end EffectiveEpiFamily

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : CompHaus.{u}}
    (X : α → CompHaus.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨CompHaus.EffectiveEpiFamily.struct π surj⟩⟩

instance : Precoherent CompHaus.{u} := sorry

end CompHaus

namespace Condensed

def Condensed.{u} (C : Type _) [Category C] :=
  Sheaf (CoherentTopology CompHaus.{u}) C

end Condensed
