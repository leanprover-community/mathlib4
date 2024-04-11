import Mathlib.Condensed.Explicit

universe u

open CategoryTheory Limits

namespace CompHaus.aux

section FiniteCoproducts

variable {α : Type u} [Finite α] (X : α → CompHaus.{u})

/--
The coproduct of a finite family of objects in `CompHaus`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : CompHaus := CompHaus.of <| Σ (a : α), X a

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : CompHaus.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : CompHaus.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : CompHaus.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/--
The coproduct cocone associated to the explicit finite coproduct.
-/
@[simps]
def finiteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/--
The explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

section Iso

/-- The isomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductIsoCoproduct : finiteCoproduct X ≅ ∐ X :=
  Limits.IsColimit.coconePointUniqueUpToIso (finiteCoproduct.isColimit X)
    (Limits.colimit.isColimit _)

theorem Sigma.ι_comp_toFiniteCoproduct (a : α) :
    (Limits.Sigma.ι X a) ≫ (coproductIsoCoproduct X).inv = finiteCoproduct.ι X a := by
  dsimp [coproductIsoCoproduct]
  simp only [Limits.colimit.comp_coconePointUniqueUpToIso_inv, finiteCoproduct.cocone_pt,
    finiteCoproduct.cocone_ι, Discrete.natTrans_app]

/-- The homeomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductHomeoCoproduct : finiteCoproduct X ≃ₜ (∐ X : _) :=
  CompHaus.homeoOfIso (coproductIsoCoproduct X)

end Iso

lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X a r := ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {B : CompHaus} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  intro x
  change (ι X a ≫ desc X π) _ = _
  simp only [ι_desc]
-- `elementwise` should work here, but doesn't

end FiniteCoproducts

end CompHaus.aux

namespace Condensed

variable (X : CondensedSet.{u}) {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]

def sigmaComparison : X.val.obj ⟨(CompHaus.of ((a : α) × σ a))⟩ ⟶
    ((a : α) → X.val.obj ⟨CompHaus.of (σ a)⟩) :=
  fun x a ↦ X.val.map ⟨Sigma.mk a, continuous_sigmaMk⟩ x

noncomputable instance : PreservesLimitsOfShape (Discrete α) X.val :=
  let α' := (Countable.toSmall α).equiv_small.choose
  let e : α ≃ α' := (Countable.toSmall α).equiv_small.choose_spec.some
  have : Fintype α := Fintype.ofFinite _
  have : Fintype α' := Fintype.ofEquiv α e
  have : PreservesFiniteProducts X.val := inferInstance
  have := this.preserves α'
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) X.val

instance : IsIso <| sigmaComparison X σ := by
  let i₁ := PreservesProduct.iso X.val fun a ↦ ⟨CompHaus.of (σ a)⟩
  let i₂ := Types.productIso.{u, u + 1} fun a ↦ (X.val.obj ⟨(CompHaus.of (σ a))⟩)
  have : sigmaComparison X σ = (X.val.mapIso
      (opCoproductIsoProduct'
      (CompHaus.aux.finiteCoproduct.isColimit (fun (a : α) ↦ CompHaus.of (σ a))) (productIsProduct _))).hom ≫ i₁.hom ≫ i₂.hom := by
    ext x a
    simp only [CompHaus.aux.finiteCoproduct.cocone_pt, Fan.mk_pt, Functor.mapIso_hom,
      PreservesProduct.iso_hom, types_comp_apply, Types.productIso_hom_comp_eval_apply, i₁, i₂]
    have := congrFun (piComparison_comp_π X.val (fun a ↦ ⟨CompHaus.of (σ a)⟩) a)
    simp [-piComparison_comp_π] at this
    rw [this, ← FunctorToTypes.map_comp_apply]
    simp only [sigmaComparison]
    apply congrFun
    congr 2
    erw [← opCoproductIsoProduct_inv_comp_ι]
    simp only [CompHaus.coe_of, Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
    change CompHaus.aux.finiteCoproduct.ι (fun a ↦ CompHaus.of (σ a)) _ = _
    rw [← CompHaus.aux.Sigma.ι_comp_toFiniteCoproduct]
    congr
    simp only [opCoproductIsoProduct, ← unop_comp, CompHaus.aux.coproductIsoCoproduct,
      opCoproductIsoProduct'_comp_self]
    rfl
  rw [this]
  infer_instance
