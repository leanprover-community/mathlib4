import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Data.Finite.Card
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.RepresentationTheory.Action.Limits
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Logic.Equiv.TransferInstance

universe u v w v₁ u₁ u₂ w₂ w₁ v₂

section Finite

theorem bijective_of_injective_of_card_eq {α β : Type*} [Finite β] (f : α → β)
    (hfinj : Function.Injective f) (hcardeq : Nat.card α = Nat.card β) : Function.Bijective f := by
  have : Finite α := Finite.of_injective f hfinj
  have : Fintype α := Fintype.ofFinite α
  have : Fintype β := Fintype.ofFinite β
  simp only [Fintype.bijective_iff_injective_and_card f]
  refine ⟨hfinj, ?_⟩
  rwa [←Nat.card_eq_fintype_card, ←Nat.card_eq_fintype_card]

end Finite

open CategoryTheory Limits Functor

section

def MulEquivSingleObjEquiv {G : Type v} {H : Type w} [Monoid G] [Monoid H] (e : G ≃* H) : SingleObj G ≌ SingleObj H :=
  CategoryTheory.Equivalence.mk
    (MonoidHom.toFunctor e.toMonoidHom)
    (MonoidHom.toFunctor e.symm.toMonoidHom)
    (by dsimp [MonoidHom.toFunctor, SingleObj.mapHom, Functor.comp]
        apply eqToIso
        simp only [MulEquiv.symm_apply_apply]
        rfl)
    (by dsimp [MonoidHom.toFunctor, SingleObj.mapHom, Functor.comp]
        apply eqToIso
        simp only [MulEquiv.apply_symm_apply]
        rfl)

attribute [-instance] Fin.instMulFin
attribute [-instance] Distrib.toMul

instance (G : Type v) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) FintypeCat.{w} := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let H : Type := Fin n
  let groupH : Group H := Equiv.group e.symm
  let e' : H ≃* G := Equiv.mulEquiv e.symm
  let eq : SingleObj G ≌ SingleObj H := MulEquivSingleObjEquiv e'.symm
  apply Limits.hasColimitsOfShape_of_equivalence eq.symm

end

variable {C : Type u} [Category.{v, u} C]

section Pi

@[simp]
lemma Pi.lift_π {β : Type w} {f : β → C} [HasProduct f] {P : C} (p : (b : β) → P ⟶ f b) (b : β) :
    Pi.lift p ≫ Pi.π f b = p b := by
  simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]

end Pi

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
  left_inv := by decide
  right_inv := by decide

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

lemma Types.mono_of_cofanInj {ι : Type w} {f : ι → TypeMax.{w, u}} (t : Cofan f) (h : IsColimit t)
    (i : ι) : Mono (Cofan.inj t i) := by
  simp only [mono_iff_injective]
  show Function.Injective (t.ι.app ⟨i⟩)
  erw [←colimit.isoColimitCocone_ι_hom ⟨t, h⟩]
  apply Function.Injective.comp
  exact injective_of_mono _
  show Function.Injective (Sigma.ι f i)
  let blo : f i ⟶ Sigma f := Sigma.mk i
  let φ : ∐ f ≅ Σ j, f j := Types.coproductIso f
  have h1 : Sigma.ι f i = blo ≫ inv φ.hom := by
    simp only [IsIso.eq_comp_inv φ.hom, Types.coproductIso_ι_comp_hom]
  rw [h1]
  apply Function.Injective.comp
  exact injective_of_mono (inv φ.hom)
  exact sigma_mk_injective

lemma FintypeCat.mono_of_cofanInj {ι : Type} [Fintype ι] {f : ι → FintypeCat.{u}} (t : Cofan f)
    (h : IsColimit t) (i : ι) : Mono (Cofan.inj t i) := by
  apply mono_of_mono_map FintypeCat.incl
  let s : Cofan (fun j => FintypeCat.incl.obj <| f j) := FintypeCat.incl.mapCocone t
  show Mono (Cofan.inj s i)
  let h : IsColimit s := isColimitOfPreserves FintypeCat.incl h
  exact Types.mono_of_cofanInj s h i

lemma FintypeCat.mono_of_cofanInj' {ι : Type} [Fintype ι] (F : Discrete ι ⥤ FintypeCat.{u})
    (t : ColimitCocone F) (i : ι) : Mono (t.cocone.ι.app ⟨i⟩) := by
  let f : ι → FintypeCat.{u} := fun i => F.obj ⟨i⟩
  have hi : F ≅ Discrete.functor f := Discrete.natIsoFunctor
  let s : Cofan f := (Cocones.precompose hi.inv).obj t.cocone
  let hs : IsColimit s := (IsColimit.precomposeHomEquiv hi.symm t.cocone).symm t.isColimit
  have : hi.hom.app ⟨i⟩ ≫ Cofan.inj s i = t.cocone.ι.app ⟨i⟩ := by
    show hi.hom.app ⟨i⟩ ≫ hi.inv.app ⟨i⟩ ≫ t.cocone.ι.app ⟨i⟩ = t.cocone.ι.app ⟨i⟩
    simp
  rw [←this]
  have : Mono (Cofan.inj s i) := FintypeCat.mono_of_cofanInj s hs i
  exact mono_comp _ _

lemma FintypeCat.jointly_surjective {J : Type} [SmallCategory J] [FinCategory J]
    (F : J ⥤ FintypeCat.{u}) (t : Cocone F) (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x := by
  let s : Cocone (F ⋙ FintypeCat.incl) := FintypeCat.incl.mapCocone t
  let hs : IsColimit s := isColimitOfPreserves FintypeCat.incl.{u} h
  exact Types.jointly_surjective (F ⋙ FintypeCat.incl) hs x

namespace FintypeCat

def FProd.fst {X Y : FintypeCat.{u}} : FintypeCat.of (X × Y) ⟶ X := Prod.fst

@[simps! pt]
def binaryProductCone (X Y : FintypeCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk FProd.fst Prod.snd

@[simp]
theorem binaryProductCone_fst (X Y : FintypeCat.{u}) : (binaryProductCone X Y).fst = Prod.fst :=
  rfl

@[simp]
theorem binaryProductCone_snd (X Y : FintypeCat.{u}) : (binaryProductCone X Y).snd = Prod.snd :=
  rfl

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps!]
def binaryProductLimit (X Y : FintypeCat.{u}) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) x := (s.fst x, s.snd x)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Prod.ext (congr_fun (w ⟨WalkingPair.left⟩) x) (congr_fun (w ⟨WalkingPair.right⟩) x)

/-- The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
def binaryProductLimitCone (X Y : FintypeCat.{u}) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩

/-- The categorical binary product in `Type u` is cartesian product. -/
noncomputable def binaryProductIso (X Y : FintypeCat.{u}) : Limits.prod X Y ≅ FintypeCat.of (X × Y) :=
  limit.isoLimitCone (binaryProductLimitCone X Y)

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_fst (X Y : FintypeCat.{u}) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.fst = Limits.prod.fst :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_snd (X Y : FintypeCat.{u}) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.snd = Limits.prod.snd :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

@[simp]
lemma hom_inv_id_apply {X Y : FintypeCat.{u}} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  congr_fun f.hom_inv_id x

@[simp]
lemma inv_hom_id_apply {X Y : FintypeCat.{u}} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  congr_fun f.inv_hom_id y

@[simp]
lemma FunctorToFintypeCat.map_inv_map_hom_apply {C : Type u} [Category.{v, u} C]
    (F : C ⥤ FintypeCat.{w}) {X Y : C} (f : X ≅ Y) (x : F.obj X) :
    F.map f.inv (F.map f.hom x) = x :=
  congr_fun (F.mapIso f).hom_inv_id x

noncomputable def Limit.mk [UnivLE.{v, u}] {J : Type v} [SmallCategory J] [FinCategory J]
    (F : J ⥤ FintypeCat.{u}) (x : ∀ j, F.obj j)
    (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') : (limit F : FintypeCat.{u}) := by
  let y : limit (F ⋙ FintypeCat.incl) := Types.Limit.mk (F ⋙ FintypeCat.incl) x h
  have h2 : IsLimit (incl.mapCone (limit.cone F)) := PreservesLimit.preserves (limit.isLimit F)
  let i : FintypeCat.incl.obj (limit F) ≅ limit (F ⋙ FintypeCat.incl) := by
    exact IsLimit.conePointUniqueUpToIso h2 (limit.isLimit (F ⋙ incl))
  exact i.inv y

@[simp]
lemma Limit.π_mk [UnivLE.{v, u}] {J : Type v} [SmallCategory J] [FinCategory J]
    (F : J ⥤ FintypeCat.{u}) (x : ∀ j, F.obj j)
    (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j : J) :
    limit.π F j (Limit.mk F x h) = x j := by
  dsimp [Limit.mk]
  show ((IsLimit.conePointUniqueUpToIso
    (PreservesLimit.preserves _) (limit.isLimit (F ⋙ incl))).inv ≫ (limit.cone F).π.app j) _ = x j
  erw [IsLimit.conePointUniqueUpToIso_inv_comp]
  simp only [limit.cone_x, limit.cone_π, Types.Limit.π_mk]

noncomputable def Pi.mk [UnivLE.{v, u}] {ι : Type v} [Fintype ι] (f : ι → FintypeCat.{u})
    (x : ∀ j, f j) : (∏ f : FintypeCat.{u}) := by
  apply FintypeCat.Limit.mk (Discrete.functor f) (fun ⟨i⟩ => x i)
  intro ⟨i⟩ ⟨j⟩ u
  have h : i = j := Discrete.eq_of_hom u
  aesop_subst h
  simp only [Discrete.functor_obj, Discrete.functor_map_id, id_apply]

@[simp]
lemma Pi.π_mk [UnivLE.{v, u}] {ι : Type v} [Fintype ι] (f : ι → FintypeCat.{u})
    (x : ∀ j, f j) (j : ι) : Pi.π f j (Pi.mk f x) = x j := by
  dsimp [Pi.mk]
  simp only [Limit.π_mk]

noncomputable def imageComplement {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    FintypeCat.{u} := by
  let h : Fintype (↑(Set.range f)ᶜ) := Fintype.ofFinite _
  exact of (↑(Set.range f)ᶜ)

noncomputable def imageComplementIncl {X Y : FintypeCat.{u}}
    (f : X ⟶ Y) : imageComplement f ⟶ Y := Subtype.val

--noncomputable def isCoprodOfMono {X Y : FintypeCat.{u}}
--    (f : X ⟶ Y) [Mono f] : IsColimit
--    (BinaryCofan.mk f (imageComplementIncl f)) := by
--  apply isColimitOfReflects FintypeCat.incl
--  dsimp [mapCocone]
--  convert_to IsColimit (BinaryCofan.mk (incl.map f) (incl.map (imageComplementIncl f)))
--  aesop
--  apply CategoryTheory.Functor.ext
--  intro i j u
--  aesop
--  admit
--  admit
--  admit
--  admit

end FintypeCat

section Binary

variable {D : Type w₁} [Category.{w₂, w₁} D]

def mapPairIso' {X Y : C} (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) := by
  apply Discrete.natIso
  intro ⟨j⟩
  match j with
  | WalkingPair.left => exact eqToIso rfl
  | WalkingPair.right => exact eqToIso rfl

def mapBinaryCofanIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  (F : C ⥤ D) : F.mapCocone (BinaryCofan.mk f g)
    ≅ (Cocones.precompose (mapPairIso' F).hom).obj (BinaryCofan.mk (F.map f) (F.map g)) := by
  apply Cocones.ext
  swap
  exact eqToIso rfl
  intro ⟨j⟩
  match j with
  | WalkingPair.left => 
      dsimp [mapPairIso']
      simp only [Category.comp_id, Category.id_comp]
  | WalkingPair.right => 
      dsimp [mapPairIso']
      simp only [Category.comp_id, Category.id_comp]

def isColimitMapBinaryCofan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (F : C ⥤ D) :
    IsColimit (F.mapCocone (BinaryCofan.mk f g)) ≃ IsColimit (BinaryCofan.mk (F.map f) (F.map g)) := by
  trans
  apply IsColimit.equivIsoColimit
  exact mapBinaryCofanIso f g F
  apply IsColimit.precomposeHomEquiv

end Binary

namespace Types

noncomputable def Pi.mk [UnivLE.{v, u}] {ι : Type v} (f : ι → Type u) (x : ∀ j, f j) :
    (∏ f : Type u) := by
  apply Types.Limit.mk (Discrete.functor f) (fun ⟨i⟩ => x i)
  intro ⟨i⟩ ⟨j⟩ u
  have h : i = j := Discrete.eq_of_hom u
  aesop_subst [h]
  simp only [Discrete.functor_obj, Discrete.functor_map_id, types_id_apply]

@[simp]
lemma Pi.π_mk [UnivLE.{v, u}] {ι : Type v} (f : ι → Type u) (x : ∀ j, f j) (j : ι) :
    Pi.π f j (Pi.mk f x) = x j := by
  show limit.π (Discrete.functor f) ⟨j⟩ (Pi.mk f x) = x j
  erw [Types.Limit.π_mk]

end Types

example (X Y : FintypeCat.{u}) (x : X) (y : Y) :
    @prod.fst FintypeCat.{u} _ X Y _ ((FintypeCat.binaryProductIso X Y).inv (x, y)) = x := by
  rw [←FintypeCat.binaryProductIso_hom_comp_fst]
  simp only [FintypeCat.comp_apply, FintypeCat.inv_hom_id_apply]

example (X Y : Type u) (x : X) (y : Y) :
    @prod.fst (Type u) _ X Y _ ((Types.binaryProductIso X Y).inv (x, y)) = x := by
  rw [←Types.binaryProductIso_hom_comp_fst]
  simp only [types_comp_apply, inv_hom_id_apply]

section SingleObj

def SingleObj.functor {α : Type w} [Monoid α] {X : C} (f : α →* End X) :
    SingleObj α ⥤ C where
  obj _ := X
  map a := f a
  map_id _ := by
    show f 1 = 1
    rw [MonoidHom.map_one]
  map_comp a b := by
    show f (b * a) = f b * f a
    rw [MonoidHom.map_mul]

def SingleObj.natTrans {α : Type w} [Monoid α] {F G : SingleObj α ⥤ C}
    (u : F.obj (SingleObj.star α) ⟶ G.obj (SingleObj.star α))
    (h : ∀ a : α, F.map a ≫ u = u ≫ G.map a)
    : F ⟶ G where
  app _ := u
  naturality _ _ a := h a

def equivMulOfFullyFaithful {D : Type u₁} [Category.{v₁, u₁} D] (F : C ⥤ D)
    [Full F] [Faithful F] {X : C } :
    End X ≃* End (F.obj X) := by
  apply MulEquiv.mk'
  intro f g
  erw [equivOfFullyFaithful_apply, equivOfFullyFaithful_apply, equivOfFullyFaithful_apply]
  simp only [End.mul_def, map_comp]

@[simp]
lemma equivMulOfFullyFaithful_symm_apply {D : Type u₁} [Category.{v₁, u₁} D] (F : C ⥤ D)
    [Full F] [Faithful F] {X : C } (f : End (F.obj X)) :
    F.map ((equivMulOfFullyFaithful F).symm f) = f := by
  show F.map ((equivOfFullyFaithful F).symm f) = f
  simp only [equivOfFullyFaithful_symm_apply, image_preimage]

end SingleObj

section Profinite

--open TopologicalSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]

lemma closed_of_open (U : Subgroup G) (h : IsOpen (U : Set G)) : IsClosed (U : Set G) :=
  OpenSubgroup.isClosed ⟨U, h⟩

open Function Set

lemma QuotientGroup.preimage_mk_singleton_mk (H : Subgroup G) (g : G) :
    mk (s := H) ⁻¹' {mk g} = (g * ·) '' H := by
  ext g'
  simp only [mem_preimage, mem_singleton_iff, QuotientGroup.eq, image_mul_left, SetLike.mem_coe]
  rw [← H.inv_mem_iff]
  simp

lemma Subgroup.discreteTopology (U : Subgroup G) (U_open : IsOpen (U : Set G)) : DiscreteTopology (G ⧸ U) := by
  apply singletons_open_iff_discrete.mp
  rintro ⟨g⟩
  erw [isOpen_mk, QuotientGroup.preimage_mk_singleton_mk]
  exact Homeomorph.mulLeft g |>.isOpen_image|>.mpr U_open

def finiteQuotientOfOpen [CompactSpace G] (U : Subgroup G) (h : IsOpen (U : Set G)) :
    Finite (G ⧸ U) :=
  have : CompactSpace (G ⧸ U) := Quotient.compactSpace
  have : DiscreteTopology (G ⧸ U) := U.discreteTopology h
  finite_of_compact_of_discrete

def finiteQuotientSubgroups [CompactSpace G] (U K : Subgroup G) (hUopen : IsOpen (U : Set G))
    (hKpoen : IsOpen (K : Set G)) : Finite (U ⧸ Subgroup.subgroupOf K U) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp <| IsClosed.isCompact
    <| closed_of_open U hUopen
  apply finiteQuotientOfOpen (Subgroup.subgroupOf K U)
  show IsOpen (((Subgroup.subtype U) ⁻¹' K) : Set U)
  apply Continuous.isOpen_preimage
  continuity
  assumption

end Profinite

section ActionLimitPreservation

variable (V : Type (w + 1)) [LargeCategory.{w} V] [ConcreteCategory V] (G : MonCat.{w})

private def SingleObj.preservesColimit {C : Type*} [Category C] (F : C ⥤ SingleObj G ⥤ V)
    {J : Type w₁} [Category.{w₂, w₁} J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G)))
    : PreservesColimit K F := by
  apply preservesColimitOfEvaluation
  intro _
  exact h

def Action.preservesColimitOfPreserves (F : C ⥤ Action V G) {J : Type w₁}
    [Category.{w₂, w₁} J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ forget₂ (Action V G) V)) : PreservesColimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  let i : PreservesColimit K F' := by
    apply SingleObj.preservesColimit
    show PreservesColimit K (F ⋙ forget₂ (Action V G) V)
    assumption
  apply preservesColimitOfReflectsOfPreserves F (Action.functorCategoryEquivalence V G).functor

def Action.preservesColimitOfShapeOfPreserves (F : C ⥤ Action V G) {J : Type w₁}
    [Category.{w₂, w₁} J] (h : PreservesColimitsOfShape J (F ⋙ forget₂ (Action V G) V)) :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesColimitOfPreserves
  exact PreservesColimitsOfShape.preservesColimit

def Action.preservesColimitOfSizeOfPreserves (F : C ⥤ Action V G)
    (h : PreservesColimitsOfSize.{w₂, w₁} (F ⋙ forget₂ (Action V G) V)) :
    PreservesColimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesColimitOfShapeOfPreserves
  exact PreservesColimitsOfSize.preservesColimitsOfShape

instance : ReflectsColimits (forget₂ (Action V G) V) := by
  constructor
  intro J _
  constructor
  intro K
  constructor
  intro c h
  let c' : Cocone (K ⋙ (Action.functorCategoryEquivalence V G).functor) := (Action.functorCategoryEquivalence V G).functor.mapCocone c
  apply isColimitOfReflects ((Action.functorCategoryEquivalence V G).functor)
  exact evaluationJointlyReflectsColimits c' (fun _ => h)

noncomputable instance forget₂PreservesFiniteColimits [HasFiniteColimits V] :
    PreservesFiniteColimits (forget₂ (Action V G) V) := by
  show PreservesFiniteColimits ((Action.functorCategoryEquivalence V G).functor ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteColimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro J _ _
    infer_instance
  apply compPreservesFiniteColimits

noncomputable instance [HasFiniteLimits V] : PreservesFiniteLimits (forget₂ (Action V G) V) := by
  show PreservesFiniteLimits ((Action.functorCategoryEquivalence V G).functor ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteLimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro J _ _
    infer_instance
  apply compPreservesFiniteLimits

noncomputable instance forgetPreservesFiniteLimits [HasFiniteLimits V] [PreservesFiniteLimits (forget V)] :
    PreservesFiniteLimits (forget (Action V G)) := by
  show PreservesFiniteLimits (forget₂ (Action V G) V ⋙ forget V)
  apply compPreservesFiniteLimits

noncomputable instance {J : Type v₁} [Category.{v₂, v₁} J] [HasColimitsOfShape J V] :
    PreservesColimitsOfShape J (forget₂ (Action V G) V) := by
  show PreservesColimitsOfShape J ((Action.functorCategoryEquivalence V G).functor ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))
  infer_instance

instance {J : Type v₁} [Category.{v₂, v₁} J] [HasColimitsOfShape J V] : HasColimitsOfShape J (Action V G) :=
  Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

noncomputable example (H : Type v) [Group H] [Finite H] : PreservesColimitsOfShape (SingleObj H) (forget₂ (Action FintypeCat G) FintypeCat) :=
  inferInstance

example (H : Type v) [Group H] [Finite H] : HasColimitsOfShape (SingleObj H) (Action FintypeCat G) := inferInstance

instance : PreservesMonomorphisms (forget₂ (Action FintypeCat G) FintypeCat) := by
  constructor
  intro X Y f hf
  apply ConcreteCategory.mono_of_injective
  show Function.Injective f.hom
  have : PreservesFiniteLimits (forget FintypeCat) := by
    show PreservesFiniteLimits FintypeCat.incl
    infer_instance
  have : PreservesFiniteLimits (forget (Action FintypeCat G)) := forgetPreservesFiniteLimits FintypeCat G
  apply ConcreteCategory.injective_of_mono_of_preservesPullback f

instance : PreservesMonomorphisms (forget (Action FintypeCat G)) := by
  show PreservesMonomorphisms ((forget₂ (Action FintypeCat G) FintypeCat) ⋙ FintypeCat.incl)
  infer_instance

end ActionLimitPreservation

section ActionFintypeCat

variable {G : MonCat.{w}}

--noncomputable def imageComplement {X Y : Action FintypeCat G} (f : X ⟶ Y) :
--    Action FintypeCat G where
--  V := FintypeCat.imageComplement f.hom
--  ρ := by
--    let g : G →* End Y.V := Y.ρ
--    
--    admit
--
--noncomputable def imageComplementIncl {X Y : Action FintypeCat G}
--    (f : X ⟶ Y) : imageComplement f ⟶ Y :=
--  sorry

end ActionFintypeCat
