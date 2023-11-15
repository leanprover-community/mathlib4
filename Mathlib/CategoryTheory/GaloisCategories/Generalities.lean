import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.MonoCoprod

universe u v w v₁ u₁ u₂ w₂

open CategoryTheory Limits Functor

variable {C : Type u} [Category.{v, u} C]

section CombineLimits

namespace Limits

section Def

variable {α : Type*} (f : α → Type*) (g : (a : α) → f a → C)
    (t : ∀ a, ColimitCocone (Discrete.functor (g a)))
    (s : ColimitCocone (Discrete.functor (fun a ↦ (t a).cocone.pt)))

def combCofan : Cofan (Sigma.uncurry g : Sigma f → C) := by
  apply Cofan.mk
  intro ⟨a, x⟩
  let u : g a x ⟶ (t a).cocone.pt := Cofan.inj (t a).cocone x
  let v : (t a).cocone.pt ⟶ s.cocone.pt := Cofan.inj s.cocone a
  exact u ≫ v

@[simp]
lemma combCofan_pt_eq : (combCofan f g t s).pt = s.cocone.pt :=
  rfl

def combCofanIsColimit : IsColimit (combCofan f g t s) :=
  let cc (c : Cofan (Sigma.uncurry g)) (a : α) : Cocone (Discrete.functor (g a)) := by
    apply Cofan.mk
    intro x
    exact Cofan.inj c ⟨a, x⟩
  let sf (c : Cofan (Sigma.uncurry g)) : Cocone (Discrete.functor (fun a ↦ (t a).cocone.pt)) := by
    apply Cofan.mk
    intro a
    exact (t a).isColimit.desc (cc c a)
  mkCofanColimit _
  (fun c => by exact s.isColimit.desc (sf c))
  (fun c ⟨a, x⟩ => by
    erw [Category.assoc, s.isColimit.fac (sf c) ⟨a⟩, (t a).isColimit.fac (cc c a) ⟨x⟩]
    rfl
  )
  (fun c m h => by
    apply s.isColimit.uniq (sf c) m
    intro ⟨a⟩
    show Cofan.inj s.cocone a ≫ m = Cofan.inj (sf c) a
    have ha (x : Discrete (f a)) : Cofan.inj (t a).cocone x.as ≫
      Cofan.inj s.cocone a ≫ m = Cofan.inj (cc c a) x.as := by
      erw [←h ⟨a, x.as⟩, Category.assoc]
    simp only [(t a).isColimit.uniq (cc c a) _ ha, cofan_mk_inj]
  )

def combCofanColimitCocone : ColimitCocone (Discrete.functor (Sigma.uncurry g)) where
  cocone := combCofan f g t s
  isColimit := combCofanIsColimit f g t s

@[simp]
lemma combCofanColimitCocone_pt_eq : (combCofanColimitCocone f g t s).cocone.pt = s.cocone.pt :=
  rfl

end Def

def combCofanPairType (α β : Type w) (i : WalkingPair) : Type w := WalkingPair.casesOn i α β

instance {α β : Type w} [Finite α] [Finite β] (i : WalkingPair) :
    Finite (combCofanPairType α β i) := by
  cases i
  show Finite α
  infer_instance
  show Finite β
  infer_instance

def combCofanPairMap {α β : Type w} (f : α → C) (g : β → C) (i : WalkingPair)
    (x : combCofanPairType α β i) : C := match i with
  | WalkingPair.left => f x
  | WalkingPair.right => g x

def myEq : WalkingPair ≃ Bool where
  toFun
    | WalkingPair.left => False
    | WalkingPair.right => True
  invFun
    | Bool.false => WalkingPair.left
    | Bool.true => WalkingPair.right
  left_inv := by simp
  right_inv := by simp

def combEquiv (α β : Type w) : α ⊕ β ≃ (i : WalkingPair) × (WalkingPair.casesOn i α β) := by
  trans
  exact Equiv.sumEquivSigmaBool α β
  apply Equiv.sigmaCongr
  swap
  exact myEq.symm
  intro i
  match i with
    | Bool.false => exact Equiv.refl _
    | Bool.true => exact Equiv.refl _

@[simp]
lemma combEquiv_eq_inl (α β : Type w) (a : α) :
    (combEquiv α β) (Sum.inl a) = ⟨WalkingPair.left, a⟩ :=
  rfl

def combCofanPairColimitCocone {α β : Type w} {f : α → C} {g : β → C}
    {s : ColimitCocone (Discrete.functor f)}
    {t : ColimitCocone (Discrete.functor g)}
    (u : ColimitCocone (pair s.cocone.pt t.cocone.pt)) :
    ColimitCocone
      (Discrete.functor (Sum.elim f g)) := by
  let hc (i : WalkingPair) : ColimitCocone (Discrete.functor (combCofanPairMap f g i)) := match i with
    | WalkingPair.left => s
    | WalkingPair.right => t
  --let a : WalkingPair → Type w := fun i ↦ WalkingPair.casesOn i α β
  --let b (i : WalkingPair) (x : a i) : C := match i with
  --  | WalkingPair.left => f x
  --  | WalkingPair.right => g x
  --have : b = combCofanPairMap f g := by
  --  ext i x
  --  match i with
  --  | WalkingPair.left => rfl
  --  | WalkingPair.right => rfl
  --have (i : WalkingPair) : Category.{w, w} (Discrete (a i)) := inferInstance
  --let hc (i : WalkingPair) : ColimitCocone (@Discrete.functor C _ (a i) (b i)) := match i with
  --  | WalkingPair.left => s
  --  | WalkingPair.right => t
  let F : Discrete WalkingPair ⥤ C := Discrete.functor (fun j ↦ (hc j).cocone.pt)
  let G : Discrete WalkingPair ⥤ C := pair s.cocone.pt t.cocone.pt 
  let h2 : G ≅ F := by
    apply Discrete.natIso
    intro ⟨i⟩
    match i with
    | WalkingPair.left => exact Iso.refl _
    | WalkingPair.right => exact Iso.refl _
  let hcc1 : Cocone G := u.cocone
  let hcc2 : IsColimit hcc1 := u.isColimit
  let hcc : Cocone F := (Cocones.precompose h2.inv).obj hcc1
  let bla : IsColimit hcc ≃ IsColimit hcc1 :=
    IsColimit.precomposeInvEquiv h2 hcc1
  let hccC : IsColimit hcc := bla.invFun hcc2
  let hu : ColimitCocone F := {
    cocone := hcc
    isColimit := hccC
  }
  let cu : ColimitCocone (Discrete.functor (Sigma.uncurry <| combCofanPairMap f g)) :=
    combCofanColimitCocone (combCofanPairType α β) (combCofanPairMap f g) hc hu 
  let blab : α ⊕ β ≃ Sigma (combCofanPairType α β) := combEquiv α β
  let blabe : Discrete (α ⊕ β) ≌ Discrete (Sigma (combCofanPairType α β)) :=
    Discrete.equivalence blab
  let H : Discrete (α ⊕ β) ⥤ C :=
    blabe.functor ⋙ Discrete.functor (Sigma.uncurry (combCofanPairMap f g))
  let cu1 : Cocone H := (Cocone.whisker blabe.functor cu.cocone)
  let cu2 : IsColimit cu1 := IsColimit.whiskerEquivalence cu.isColimit blabe
  let Heq : H ≅ Discrete.functor (Sum.elim f g) := by
    apply Discrete.natIso
    intro ⟨i⟩
    match i with
    | Sum.inl a => 
        show f a ≅ f a
        exact eqToIso rfl
    | Sum.inr b =>
        show g b ≅ g b
        exact eqToIso rfl
  let cuu1 : Cocone (Discrete.functor (Sum.elim f g)) :=
    (Cocones.precompose Heq.inv).obj cu1
  let cuu2 : IsColimit cuu1 :=
    (IsColimit.precomposeInvEquiv Heq cu1).invFun cu2
  exact {
    cocone := cuu1
    isColimit := cuu2
  }

lemma combCofanPairColimitCocone_pt_eq {α β : Type w} {f : α → C} {g : β → C}
    {s : ColimitCocone (Discrete.functor f)}
    {t : ColimitCocone (Discrete.functor g)}
    (u : ColimitCocone (pair s.cocone.pt t.cocone.pt)) :
    (combCofanPairColimitCocone u).cocone.pt = u.cocone.pt :=
  rfl

end Limits
    
end CombineLimits

section SingleObjectLimits

namespace Limits

variable (X : C)

def constantCofan : Cofan ((fun _ ↦ X) : PUnit → C) := by
  apply Cofan.mk
  intro _
  exact eqToHom rfl

def constantCofanIsColimit : IsColimit (constantCofan X) := mkCofanColimit _
  (fun s ↦ Cofan.inj s PUnit.unit)
  (fun s ↦ by
    intro _
    show 𝟙 X ≫ (fun s ↦ Cofan.inj s PUnit.unit) s = Cofan.inj s PUnit.unit
    simp only [Category.id_comp]
    )
  (fun s ↦ by
    intro m h
    have : 𝟙 X ≫ m = Cofan.inj s PUnit.unit := h PUnit.unit
    simp [←this]
    )

end Limits

end SingleObjectLimits

namespace Limits

abbrev PreservesInitialObjects {D : Type w} [Category.{w₂, w} D] (F : C ⥤ D) :=
  PreservesColimitsOfShape (Discrete PEmpty.{1}) F

abbrev ReflectsInitialObjects {D : Type w} [Category.{w₂, w} D] (F : C ⥤ D) :=
  ReflectsColimitsOfShape (Discrete PEmpty.{1}) F

end Limits

open Limits

lemma IsInitial.isInitialIffObj {D : Type w} [Category.{w₂, w} D] (F : C ⥤ D)
    [PreservesInitialObjects F] [ReflectsInitialObjects F] (X : C) :
    Nonempty (IsInitial X) ↔ Nonempty (IsInitial (F.obj X)) := by
  constructor
  intro ⟨h⟩
  exact Nonempty.intro (IsInitial.isInitialObj F X h)
  intro ⟨h⟩
  exact Nonempty.intro (IsInitial.isInitialOfObj F X h)

lemma Types.initialIffEmpty (X : Type u) : Nonempty (IsInitial X) ↔ IsEmpty X := by
  constructor
  intro ⟨h⟩
  exact Function.isEmpty (IsInitial.to h PEmpty)
  intro h
  apply Nonempty.intro
  apply IsInitial.ofIso Types.isInitialPunit
  apply Equiv.toIso
  exact Equiv.equivOfIsEmpty PEmpty X

lemma FintypeCat.initialIffEmpty (X : FintypeCat.{u}) : Nonempty (IsInitial X) ↔ IsEmpty X := by
  constructor
  intro ⟨h⟩
  have h1 : ⊥_ FintypeCat ≅ X := initialIsoIsInitial h
  have h2 : FintypeCat.incl.{u}.obj (⊥_ FintypeCat.{u}) ≅ ⊥_ Type u :=
    PreservesInitial.iso (FintypeCat.incl.{u})
  have h3 : ⊥_ Type u ≅ PEmpty := Types.initialIso
  have : PEmpty ≅ FintypeCat.incl.{u}.obj X := by
    trans
    exact h3.symm
    trans
    exact h2.symm
    apply mapIso
    exact h1
  have : PEmpty ≃ FintypeCat.incl.{u}.obj X := this.toEquiv
  have : IsEmpty (FintypeCat.incl.{u}.obj X) := Function.isEmpty this.invFun
  exact this
  intro h
  have h1 : PEmpty ≃ FintypeCat.incl.{u}.obj X := Equiv.equivOfIsEmpty PEmpty X
  have h2 : PEmpty ≅ FintypeCat.incl.{u}.obj X := Equiv.toIso h1
  have h3 : IsInitial PEmpty := Types.isInitialPunit
  have h4 : IsInitial (FintypeCat.incl.{u}.obj X) := IsInitial.ofIso h3 h2
  have : IsInitial X := IsInitial.isInitialOfObj FintypeCat.incl X h4
  exact Nonempty.intro this

lemma FintypeCat.isIso_iff_bijective { X Y : FintypeCat.{u} } (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective f := by
  constructor
  intro _
  exact ConcreteCategory.bijective_of_isIso f
  intro h
  have : IsIso (FintypeCat.incl.map f) :=
    (CategoryTheory.isIso_iff_bijective _).mpr h
  exact CategoryTheory.isIso_of_reflects_iso f FintypeCat.incl

example (ι : Type u) (f : ι → Type u) (t : Cofan f) (h : IsColimit t) (i : ι) :
    Function.Injective (Cofan.inj t i) := by
  let φ : ∐ f ≅ Σ j, f j := Types.coproductIso f
  have : Function.Injective (@Sigma.mk ι f i) := sigma_mk_injective
  let blo : f i ⟶ Sigma f := @Sigma.mk ι f i
  have h1 : Sigma.ι f i = blo ≫ inv φ.hom := by
    simp only [IsIso.eq_comp_inv φ.hom, Types.coproductIso_ι_comp_hom]
  let e : ∐ f ≅ t.pt := colimit.isoColimitCocone ⟨t, h⟩
  have h2 : Cofan.inj t i = Sigma.ι f i ≫ e.hom := by
    show t.ι.app ⟨i⟩ = Sigma.ι f i ≫ e.hom
    simp only [Discrete.functor_obj, const_obj_obj, colimit.isoColimitCocone_ι_hom]
  rw [h2]
  apply Function.Injective.comp
  exact injective_of_mono e.hom
  rw [h1]
  apply Function.Injective.comp
  exact injective_of_mono (inv φ.hom)
  assumption

lemma Types.jointlySurjective_inclusionsCoproduct (ι : Type*) (F : Discrete ι ⥤ Type u)
    (t : ColimitCocone F) (x : t.cocone.pt) : ∃ (i : ι) (y : F.obj ⟨i⟩),
    t.cocone.ι.app ⟨i⟩ y = x :=
  sorry
