import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.Topology.Category.TopCat.Basic
-- import Mathlib.Topology.ExtremallyDisconnected
-- import Mathlib.Topology.Sets.Closeds

universe u

open CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike

variable (P : TopCat.{u} → Prop)

/-- The type of Compact Hausdorff topological spaces satisfying an additional property `P`. -/
structure CompHausLike where
  /-- The underlying topological space of an object of `CompHausLike P`. -/
  toTop : TopCat
  /-- The underlying topological space is compact. -/
  [is_compact : CompactSpace toTop]
  /-- The underlying topological space is T2. -/
  [is_hausdorff : T2Space toTop]
  /-- The underlying topological space satisfies P. -/
  prop : P toTop

-- Porting note (#10754): Adding instance
attribute [instance] CompHausLike.is_compact
-- Porting note (#10754): Adding instance
attribute [instance] CompHausLike.is_hausdorff

namespace CompHausLike

instance : CoeSort (CompHausLike P) (Type u) :=
  ⟨fun X => X.toTop⟩

instance category : Category (CompHausLike P) :=
  InducedCategory.category toTop

instance concreteCategory : ConcreteCategory (CompHausLike P) :=
  InducedCategory.concreteCategory _

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] (h : (P (TopCat.of X)))

/-- A constructor for objects of the category `CompHausLike P`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHausLike P where
  toTop := TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := ‹_›

@[simp]
theorem coe_of : (CompHausLike.of P X h : Type _) = X :=
  rfl

-- Porting note: have changed statement as the original LHS simplified.
@[simp]
theorem coe_id (X : CompHausLike P) : (𝟙 ((forget (CompHausLike P)).obj X)) = id :=
  rfl

-- Porting note: have changed statement as the original LHS simplified.
@[simp]
theorem coe_comp {X Y Z : CompHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget (CompHausLike P)).map f ≫ (forget (CompHausLike P)).map g) = g ∘ f :=
  rfl

-- Porting note (#10688): This lemma was not needed in mathlib3
@[simp]
lemma forget_ContinuousMap_mk {X Y : CompHausLike P} (f : X → Y) (hf : Continuous f) :
    (forget (CompHausLike P)).map (ContinuousMap.mk f hf) = f :=
  rfl

-- Porting note (#10754): Adding instance
instance (X : CompHausLike.{u} P) : TopologicalSpace ((forget (CompHausLike P)).obj X) :=
  show TopologicalSpace X.toTop from inferInstance

-- Porting note (#10754): Adding instance
instance (X : CompHausLike.{u} P) : CompactSpace ((forget (CompHausLike P)).obj X) :=
  show CompactSpace X.toTop from inferInstance

-- Porting note (#10754): Adding instance
instance (X : CompHausLike.{u} P) : T2Space ((forget (CompHausLike P)).obj X) :=
  show T2Space X.toTop from inferInstance

variable {P}

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
theorem isClosedMap {X Y : CompHausLike.{u} P} (f : X ⟶ Y) : IsClosedMap f := fun _ hC =>
  (hC.isCompact.image f.continuous).isClosed

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
theorem isIso_of_bijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) :
    IsIso f := by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage]
    exact isClosedMap f S hS
  refine ⟨⟨⟨E.symm, hE⟩, ?_, ?_⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable def isoOfBijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
    (bij : Function.Bijective f) : X ≅ Y :=
  letI := isIso_of_bijective _ bij
  asIso f

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
def isoOfHomeo {X Y : CompHausLike.{u} P} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.continuous⟩
  inv := ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : CompHausLike.{u} P} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by sorry
  right_inv x := by sorry
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

/-- The equivalence between isomorphisms in `CompHaus` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : CompHausLike.{u} P} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

@[simps]
def toCompHausLike {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    CompHausLike P ⥤ CompHausLike P' where
  obj X := CompHausLike.of _ X (h _ X.prop)
  map f := f

instance {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    (toCompHausLike h).Full := show (inducedFunctor _).Full from inferInstance

instance {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    (toCompHausLike h).Faithful := show (inducedFunctor _).Faithful from inferInstance

variable (P)

/-- The fully faithful embedding of `CompHaus` in `TopCat`. -/
-- Porting note: `semireducible` -> `.default`.
@[simps (config := { rhsMd := .default })]
def compHausLikeToTop : CompHausLike.{u} P ⥤ TopCat.{u} :=
  inducedFunctor _ -- deriving Full, Faithful -- Porting note: deriving fails, adding manually.

example {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    toCompHausLike h ⋙ compHausLikeToTop P' = compHausLikeToTop P := rfl

instance : (compHausLikeToTop P).Full  :=
  show (inducedFunctor _).Full from inferInstance

instance : (compHausLikeToTop P).Faithful :=
  show (inducedFunctor _).Faithful from inferInstance

instance (X : CompHausLike P) : CompactSpace ((compHausLikeToTop P).obj X) :=
  show CompactSpace X.toTop from inferInstance

instance (X : CompHausLike P) : T2Space ((compHausLikeToTop P).obj X) :=
  show T2Space X.toTop from inferInstance

instance forget_reflectsIsomorphisms :
    (forget (CompHausLike.{u} P)).ReflectsIsomorphisms :=
  ⟨by intro A B f hf; exact isIso_of_bijective _ ((isIso_iff_bijective f).mp hf)⟩

variable {P}

theorem epi_of_surjective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (hf : Function.Surjective f) :
    Epi f := by
  rw [← CategoryTheory.epi_iff_surjective] at hf
  exact (forget (CompHausLike P)).epi_of_epi_map hf

theorem mono_iff_injective {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
    (hPUnit : P (TopCat.of PUnit) /- Added that the one-point space satisfies `P` -/) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : of _ PUnit hPUnit ⟶ X := ⟨fun _ => x₁, continuous_const⟩
    let g₂ : of _ PUnit hPUnit ⟶ X := ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by
      ext
      exact h
    rw [cancel_mono] at this
    apply_fun fun e => e PUnit.unit at this
    exact this
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget (CompHausLike P)).mono_of_mono_map
