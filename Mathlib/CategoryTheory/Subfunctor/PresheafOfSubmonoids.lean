module

public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder

/-

## Presheaf Of Submonoids

Given a presheaf of monoids `R`, we define a presheaf of submonoids. We also define
a sheaf of monoids when `R` is a sheaf.

-/

@[expose] public section

universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ MonCat.{w}}


variable (R) in
@[ext]
structure PresheafOfSubmonoids where
  /-- a family of submonoids of `R.obj X` for all `X`. -/
  obj : ∀ U, Submonoid (R.obj U)
  /-- If `S` is a presheaf of submonoids of `R` and `i : U ⟶ V`, then for each `S`-sections on `U`
  `x`, `R i x` is in `S(V)`. -/
  map : ∀ {U V : Cᵒᵖ} (i : U ⟶ V), (obj U).carrier ⊆ R.map i ⁻¹' (obj V).carrier

namespace PresheafOfSubmonoids

/-- The presheaf of monoids associated to a presheaf of submonoids. -/
@[simps obj map]
def toPresheafOfMonoids (S : PresheafOfSubmonoids R) : Cᵒᵖ ⥤ MonCat.{w} where
  obj _ := MonCat.of (S.obj _)
  map i:= MonCat.ofHom ({
    toFun := ↾fun x => ⟨R.map i x, S.map i x.prop⟩
    map_one' := by simp_all only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      OneMemClass.coe_one, map_one, Submonoid.mk_eq_one]
    map_mul' _ _ := by
      simp_all only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Submonoid.coe_mul, map_mul,
      Submonoid.mk_mul_mk]
    })
  map_id _ := by
    simp_all only [Functor.map_id, MonCat.hom_id, MonoidHom.id_apply, Subtype.coe_eta,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    rfl
  map_comp _ _ := by
    simp_all only [Functor.map_comp, MonCat.hom_comp, MonoidHom.coe_comp,
      Function.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    rfl

variable {R R' : Cᵒᵖ ⥤ MonCat.{w}} (S : PresheafOfSubmonoids R) (S' : PresheafOfSubmonoids R')

instance {U : Cᵒᵖ} : CoeHead (S.toPresheafOfMonoids.obj U) (R.obj U) where
  coe := Subtype.val

instance : PartialOrder (PresheafOfSubmonoids R) :=
  PartialOrder.lift PresheafOfSubmonoids.obj (fun _ _ => PresheafOfSubmonoids.ext)

instance : CompleteLattice (PresheafOfSubmonoids R) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map i _ := by
        expose_names
        simp only [Set.mem_preimage, Submonoid.mem_carrier, Submonoid.sup_eq_closure,
          Submonoid.mem_closure]
        intro h T hT
        have : (R.map i)⁻¹' (↑(F.obj V) ∪ ↑(G.obj V)) ⊆ (R.map i)⁻¹' T := by tauto
        have : ((F.obj U).carrier ∪ (G.obj U).carrier) ⊆ (R.map i)⁻¹' T := by
          simp_all only [Set.union_subset_iff, SetLike.coe_subset_coe, and_imp, Set.preimage_union]
          obtain ⟨left, right⟩ := hT
          obtain ⟨left_1, right_1⟩ := this
          apply And.intro
          · have : (F.obj U).carrier ⊆ ⇑(hom (R.map i)) ⁻¹' ↑(F.obj V).carrier :=  F.map i
            tauto
          · have : (G.obj U).carrier ⊆ ⇑(hom (R.map i)) ⁻¹' ↑(G.obj V).carrier :=  G.map i
            tauto
        exact h (Submonoid.comap (MonCat.Hom.hom (R.map i)) T) this
         }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    simp only [sup_le_iff]
    tauto
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj _ := sSup (Set.image (fun T ↦ T.obj _) S)
      map f x hx := by
        rw [Set.mem_preimage, @Submonoid.mem_carrier, sSup_image', Submonoid.mem_iSup]
        rw [Submonoid.mem_carrier,@sSup_image',Submonoid.mem_iSup ] at hx
        intro N hN
        expose_names
        have : ∀ (i : S), ⇑(hom (R.map f)) ⁻¹' ((@Subtype.val (PresheafOfSubmonoids R)
          (fun x ↦ x ∈ S) i).obj V) ≤ ⇑(hom (R.map f)) ⁻¹' N.carrier := by tauto
        have : ∀ (i : S), ((@Subtype.val (PresheafOfSubmonoids R) (fun x ↦ x ∈ S) i).obj U) ≤
          ⇑(hom (R.map f)) ⁻¹' N.carrier := by
          intro i
          simp_all only [Subtype.forall, Set.le_eq_subset]
          obtain ⟨val, property⟩ := i
          have : (val.obj U).carrier ⊆ ⇑(hom (R.map f)) ⁻¹' ↑(val.obj V).carrier := val.map f
          tauto
        apply hx (Submonoid.comap (MonCat.Hom.hom (R.map f)) N) this
        }
  isLUB_sSup _ := ⟨fun _ _ _ _ ↦ by
    intro a
    simp only [sSup_image', Submonoid.mem_iSup];
    intro N i
    aesop, fun _ _ _ ↦ by aesop⟩
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        rintro _ ⟨s, h, rfl⟩
        rw [Submonoid.mem_carrier, Submonoid.mem_sInf] at hx
        simp_all only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
          Set.iInter_exists, Set.mem_iInter, SetLike.mem_coe]
        intro i a a_1
        subst a_1
        expose_names
        have : (i.obj U).carrier ⊆ ⇑(hom (R.map f)) ⁻¹' ↑(i.obj V).carrier := i.map f
        tauto  }
  isGLB_sInf _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  bot :=
    { obj _ := ⊥
      map _ _ h := by simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Submonoid.mem_bot, Set.mem_preimage, map_one, one_mem]}
  bot_le _ _ := bot_le
  top :=
    { obj _ := ⊤
      map _ _ h:= Set.mem_preimage.mpr h }
  le_top _ _ := le_top

/-- The inclusion of a presheaf of submonoids `S` to the original presheaf of monoids `R`. -/
@[simps]
def ι : S.toPresheafOfMonoids ⟶ R where
  app _ := MonCat.ofHom {
    toFun := fun x ↦ x
    map_one' := by simp only [OneMemClass.coe_one]
    map_mul' _ _  := by
      simp only [Submonoid.coe_mul]
    }
  naturality _ _ _ := by
    simp_all only [toPresheafOfMonoids_obj, toPresheafOfMonoids_map, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk]
    rfl

section range

/-- The presheaf defined by the image along a morphism of presheaves of monoids. -/
@[simps]
def range (S : PresheafOfSubmonoids R) (p : R ⟶ R') : PresheafOfSubmonoids R' where
  obj _ := Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map := by
    rintro U V i a h
    obtain ⟨x, h ⟩ := h
    use (hom (R.map i)) x
    have : x ∈ (hom (R.map i)) ⁻¹' (S.obj V).carrier := by
      exact (Set.mem_of_mem_of_subset h.1 (S.map i))
    rw [@Set.mem_preimage] at this
    simp_all only [SetLike.mem_coe, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      NatTrans.naturality_apply, and_self]

variable (R) in
lemma range_id : range ⊤ (𝟙 R) = ⊤  := by aesop

end range

section comap

/-- The presheaf defined by the preimage along a morphism of presheaves of monoids. -/
@[simps]
def comap (S' : PresheafOfSubmonoids R') (p : R ⟶ R') : PresheafOfSubmonoids R where
  obj _ := Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    rw [Set.mem_preimage, Submonoid.mem_carrier, Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

@[simp]
lemma range_comap_ι : range (comap S (S.ι)) (S.ι) = S := by aesop

end comap

section lift

variable (p' : R' ⟶ R) (S : PresheafOfSubmonoids R) (S' : PresheafOfSubmonoids R')
  (hp' : range S' p' ≤ S)

/-- If the image of a presheaf of submonoids `S'` under a morphism of
presheaves of monoids falls in another presheaf ofsubmonoids `S`,
then the morphism factors through it. -/
@[simps! app]
def lift : S'.toPresheafOfMonoids ⟶ S.toPresheafOfMonoids where
  app U := MonCat.ofHom {
      toFun := (↾fun x => ⟨p'.app U x, hp' U (by aesop)⟩)
      map_one' := by aesop
      map_mul' := by aesop
  }
  naturality _ _ g := by
    ext x
    simp only [toPresheafOfMonoids_obj,toPresheafOfMonoids_map,
      TypeCat.Fun.coe_mk, MonCat.hom_comp, hom_ofHom, Subtype.ext_iff]
    simp only [SetLike.coe_eq_coe]
    erw [MonoidHom.comp_apply]
    simpa [Subtype.ext_iff, -NatTrans.naturality_apply] using NatTrans.naturality_apply p' g x

theorem lift_ι : lift p' S S' hp' ≫ S.ι = S'.ι ≫ p' := rfl

end lift

end PresheafOfSubmonoids

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}
  {R : Sheaf J MonCat.{w}}

variable (R) in
/-- A sheaf of submonoids is a presheaf of submonoids that satisfies
the sheaf condition. -/
structure SheafOfSubmonoids where
  val : PresheafOfSubmonoids R.obj
  isSheaf : Presheaf.IsSheaf J (PresheafOfSubmonoids.toPresheafOfMonoids val)

variable (S : SheafOfSubmonoids R)

namespace SheafOfSubmonoids

/-- The sheaf of monoids associated to a sheaf of submonoids. -/
def toSheafOfMonoids : Sheaf J MonCat where
  obj := S.val.toPresheafOfMonoids
  property := S.isSheaf

end SheafOfSubmonoids

end CategoryTheory
