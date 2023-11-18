import Mathlib.AlgebraicTopology.SplitSimplicialObject
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.GroupTheory.Perm.Basic

universe v u

open CategoryTheory Category Limits

def NonemptyFintypeCat :=
  CategoryTheory.FullSubcategory (fun (X : FintypeCat.{u}) ↦ Nonempty X)

namespace NonemptyFintypeCat

instance : CoeSort NonemptyFintypeCat.{u} (Type u) where
  coe X := X.1.1

def of (X : Type u) [Fintype X] [Nonempty X] :
    NonemptyFintypeCat.{u} :=
  ⟨⟨X, inferInstance⟩, inferInstance⟩

@[simps!]
instance : Category NonemptyFintypeCat.{u} := by
  dsimp [NonemptyFintypeCat]
  infer_instance

@[ext]
lemma hom_ext {X Y : NonemptyFintypeCat.{u}} {f g : X ⟶ Y}
    (h : ∀ (x : X), f x = g x) : f = g := funext h

end NonemptyFintypeCat

@[simps]
def SimplexCategory.toNonemptyFintypeCat :
    SimplexCategory ⥤ NonemptyFintypeCat.{0} where
  obj Δ := NonemptyFintypeCat.of (Fin (Δ.len + 1))
  map f x := f.toOrderHom x

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

def SymmetricObject := NonemptyFintypeCat.{0}ᵒᵖ ⥤ C

namespace SymmetricObject

@[simps!]
instance category : Category (SymmetricObject C) := by
  dsimp only [SymmetricObject]
  infer_instance

def toSimplicialObjectFunctor :
    SymmetricObject C ⥤ SimplicialObject C :=
  (whiskeringLeft _ _ _).obj SimplexCategory.toNonemptyFintypeCat.op

variable {C}

abbrev toSimplicialObject (X : SymmetricObject C) : SimplicialObject C :=
  (toSimplicialObjectFunctor C).obj X

def rep (X : SymmetricObject C) (A : NonemptyFintypeCat) :
  Equiv.Perm A →* Aut (X.obj (Opposite.op A)) where
  toFun g :=
    { hom := X.map (Quiver.Hom.op (g⁻¹).1)
      inv := X.map (Quiver.Hom.op g.1)
      hom_inv_id := by
        rw [← X.map_comp, ← X.map_id]
        congr
        apply Quiver.Hom.unop_inj
        ext
        simp
      inv_hom_id := by
        rw [← X.map_comp, ← X.map_id]
        congr
        apply Quiver.Hom.unop_inj
        ext
        simp }
  map_one' := by
    ext
    apply X.map_id
  map_mul' g₁ g₂ := by
    ext
    dsimp [Aut.Aut_mul_def]
    rw [← X.map_comp]
    rfl

variable [HasFiniteCoproducts C]

/-structure Splitting (X : SymmetricObject C) where
  s : SimplicialObject.Splitting X.toSimplicialObject
  rep (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* Aut (s.N n)
  Z : ℕ → C
  i : ∀ (n : ℕ), Z n ⟶ s.N n
  hi : ∀ (n : ℕ),
    IsColimit (Cofan.mk (s.N n) (fun (g : Equiv.Perm (Fin (n + 1))) => i n ≫ (rep n g).hom))
  d₀ : ∀ (n : ℕ), Z (n + 1) ⟶ Z n
  hd₀ : ∀ (n : ℕ), d₀ n ≫ i n ≫ s.ι n =
    i (n + 1) ≫ s.ι (n + 1) ≫ X.toSimplicialObject.δ (0 : Fin (n + 2)) -/

end SymmetricObject

namespace SymmetricObject

variable {C I : Type*} [Category C]

section

variable {S : C} {X : I → C} (f : ∀ i, X i ⟶ S)

abbrev HasCechObjectWidePullbacks :=
  ∀ (A : NonemptyFintypeCat.{0}) (φ : A → I),
    HasWidePullback S (fun a => X (φ a)) (fun a => f (φ a))

abbrev HasCechObjectCoproducts [HasCechObjectWidePullbacks f] :=
  ∀ (A : NonemptyFintypeCat.{0}), HasCoproduct
    (fun (φ : A → I) => widePullback S (fun a => X (φ a)) (fun a => f (φ a)))

noncomputable def cechObject [HasCechObjectWidePullbacks f]
    [HasCechObjectCoproducts f] : SymmetricObject C where
  obj A := ∐ (fun (φ : A.unop → I) => widePullback S (fun a => X (φ a)) (fun a => f (φ a)))
  map {A₁ A₂} g := Sigma.desc (fun φ => by
    refine' _ ≫ Sigma.ι _ (φ.comp g.unop)
    exact WidePullback.lift (WidePullback.base _)
      (fun a => WidePullback.π _ (g.unop a)) (by simp))
  map_id A := by
    ext φ
    dsimp
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, comp_id]
    refine' Eq.trans _ (id_comp _)
    congr 1
    aesop_cat
  map_comp {A₁ A₂ A₃} g h := by
    ext φ
    dsimp
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc_assoc,
      Discrete.functor_obj, assoc, Function.comp_apply]
    simp only [← assoc]
    congr 1
    ext <;> dsimp <;> simp

end

section

variable {S : C} {X : Unit → C} (f : ∀ i, X i ⟶ S)
  [HasCechObjectWidePullbacks f] [HasCechObjectCoproducts f]
  [∀ (n : ℕ), HasWidePullback (Arrow.mk (f ())).right (fun (_ : Fin (n + 1)) ↦ (Arrow.mk (f ())).left) fun _ ↦ (Arrow.mk (f ())).hom]

/-noncomputable def cechObjectToSimplicialObjectIso :
    (cechObject f).toSimplicialObject ≅ Arrow.cechNerve (Arrow.mk (f Unit.unit)) :=
  NatIso.ofComponents (fun n => by
    sorry) sorry-/

end

end SymmetricObject

end CategoryTheory
