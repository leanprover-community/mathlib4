/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Torsion Theory

A **torsion theory** on an abelian category `C` is a pair of classes `T` and `F` of objects from `C`
such that `T` is the left orthogonal of `F` and `F` is the right orthogonal of `T`. We call `T`
the *torsion class* and its objects *torsion objects*.  We call `F` the *torsion-free class*
and its objects *torsion-free objects*.

## Main definitions

* `CategoryTheory.Abelian.TorsionTheory T F`: the statement that the pair of object properties
  `T` and `F` is a torsion theory on `C`.
* `CategoryTheory.Abelian.IsTorsionClass P`: the statement that `P` is the torsion class of
  some torsion theory on `C`.
* `CategoryTheory.Abelian.IsTorsionFreeClass P`: the statement that `P` is the torsion-free
  class of some torsion theory on `C`.

## Main results

* `CategoryTheory.Abelian.isTorsionClass_iff`: in a well-powered abelian category with
  coproducts, `P` is a torsion class if and only if it is closed under quotients, extensions,
  and coproducts (a theorem of Dickson).
* `CategoryTheory.Abelian.isTorsionFreeClass_iff`: dually, in a well-copowered abelian
  category with products, `P` is a torsion-free class if and only if it is closed under
  subobjects, extensions, and products.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-!
### Interaction of the left and right orthogonal

Everything in this section only needs `C` to have zero morphisms. The two instances for closure
under extensions, further down, additionally need `Preadditive C` and `Balanced C`.
-/

section Orthogonal

variable (P Q : ObjectProperty C)

/-- The pair `(rightOrthogonal, leftOrthogonal)` forms a Galois connection between
`ObjectProperty C` and its opposite order. -/
lemma gc_rightOrthogonal_leftOrthogonal :
    GaloisConnection (OrderDual.toDual (α := ObjectProperty C) ∘ rightOrthogonal)
      (leftOrthogonal ∘ OrderDual.ofDual) :=
  fun _ _ ↦ ⟨fun h _ hPX _ f hQY ↦ h _ hQY f hPX, fun h _ hQY _ f hPX ↦ h _ hPX f hQY⟩

lemma le_leftOrthogonal_iff_le_rightOrthogonal :
    P ≤ Q.leftOrthogonal ↔ Q ≤ P.rightOrthogonal :=
  -- the Galois connection has `rightOrthogonal` as its left adjoint, so its two sides
  -- appear in the opposite order
  (gc_rightOrthogonal_leftOrthogonal P (OrderDual.toDual Q)).symm

lemma le_rightOrthogonal_leftOrthogonal : P ≤ P.rightOrthogonal.leftOrthogonal :=
  fun _ hX _ f hY ↦ hY f hX

lemma le_leftOrthogonal_rightOrthogonal : P ≤ P.leftOrthogonal.rightOrthogonal :=
  fun _ hY _ f hX ↦ hX f hY

lemma antitone_rightOrthogonal : Antitone (rightOrthogonal (C := C)) :=
  fun _ _ h _ hY _ f hX ↦ hY f (h _ hX)

lemma antitone_leftOrthogonal : Antitone (leftOrthogonal (C := C)) :=
  fun _ _ h _ hX _ f hY ↦ hX f (h _ hY)

@[simp]
lemma leftOrthogonal_rightOrthogonal_leftOrthogonal :
    P.leftOrthogonal.rightOrthogonal.leftOrthogonal = P.leftOrthogonal :=
  le_antisymm (antitone_leftOrthogonal (le_leftOrthogonal_rightOrthogonal P))
    (le_rightOrthogonal_leftOrthogonal P.leftOrthogonal)

@[simp]
lemma rightOrthogonal_leftOrthogonal_rightOrthogonal :
    P.rightOrthogonal.leftOrthogonal.rightOrthogonal = P.rightOrthogonal :=
  le_antisymm (antitone_rightOrthogonal (le_rightOrthogonal_leftOrthogonal P))
    (le_leftOrthogonal_rightOrthogonal P.rightOrthogonal)

lemma rightOrthogonal_op : P.op.rightOrthogonal = P.leftOrthogonal.op := by
  ext X
  constructor
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.unop (h f.op hY)
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.op (h f.unop hY)

lemma leftOrthogonal_op : P.op.leftOrthogonal = P.rightOrthogonal.op := by
  ext X
  constructor
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.unop (h f.op hY)
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.op (h f.unop hY)

lemma rightOrthogonal_unop (R : ObjectProperty Cᵒᵖ) :
    R.unop.rightOrthogonal = R.leftOrthogonal.unop := by
  ext X
  constructor
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.op (h f.unop hY)
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.unop (h f.op hY)

lemma leftOrthogonal_unop (R : ObjectProperty Cᵒᵖ) :
    R.unop.leftOrthogonal = R.rightOrthogonal.unop := by
  ext X
  constructor
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.op (h f.unop hY)
  · intro h Y f hY
    simpa using congrArg Quiver.Hom.unop (h f.op hY)

end Orthogonal

/-- The left orthogonal of a property of objects is closed under quotients. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderQuotients where
  prop_of_epi f _ hX := (P.leftOrthogonal_iff _).mpr
    fun _ g hZ ↦ zero_of_epi_comp f (hX (f ≫ g) hZ)

/-- The left orthogonal of a property of objects is closed under colimits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isColimit.hom_ext
    intro j
    simp only [comp_zero]
    exact hX.prop_diag_obj j (hX.ι.app j ≫ f) hY

/-- The right orthogonal of a property of objects is closed under subobjects. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderSubobjects where
  prop_of_mono i _ hY := (P.rightOrthogonal_iff _).mpr
    fun _ f hX ↦ zero_of_comp_mono i (hY (f ≫ i) hX)

/-- The right orthogonal of a property of objects is closed under limits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.rightOrthogonal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isLimit.hom_ext
    intro j
    simp only [zero_comp]
    exact hX.prop_diag_obj j (f ≫ hX.π.app j) hY

omit [HasZeroMorphisms C] in
/-- A property of objects `P.op` is closed under quotients iff `P` is closed under
subobjects, since epimorphisms in `Cᵒᵖ` correspond to monomorphisms in `C`. -/
lemma isClosedUnderQuotients_op_iff (P : ObjectProperty C) :
    P.op.IsClosedUnderQuotients ↔ P.IsClosedUnderSubobjects :=
  ⟨fun h ↦ ⟨fun i _ hY ↦ h.prop_of_epi i.op hY⟩,
    fun h ↦ ⟨fun f _ hA ↦ h.prop_of_mono f.unop hA⟩⟩

/-- A property of objects `P.op` is closed under extensions iff `P` is, since a short
complex in `Cᵒᵖ` is short exact iff the corresponding short complex in `C` is. -/
lemma isClosedUnderExtensions_op_iff (P : ObjectProperty C) :
    P.op.IsClosedUnderExtensions ↔ P.IsClosedUnderExtensions :=
  ⟨fun h ↦ ⟨fun hS h₁ h₃ ↦ h.prop_X₂_of_shortExact hS.op h₃ h₁⟩,
    fun h ↦ ⟨fun hS h₁ h₃ ↦ h.prop_X₂_of_shortExact hS.unop h₃ h₁⟩⟩

end HasZeroMorphisms

/-! Closure under extensions uses the kernel and cokernel supplied by a short exact sequence, so
these two instances are stated for preadditive balanced categories. -/

section Extensions

variable [Preadditive C] [Balanced C]

/-- The left orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : CokernelCofork s.f := CokernelCofork.ofπ k (hX₁ (s.f ≫ k) hZ)
    let l : s.X₃ ⟶ Z := hs.gIsCokernel.desc t
    have hl : l = 0 := hX₃ l hZ
    have hfac : s.g ≫ l = k := hs.gIsCokernel.fac t WalkingParallelPair.one
    simp [← hfac, hl]

/-- The right orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : KernelFork s.g := KernelFork.ofι k (hX₃ (k ≫ s.g) hZ)
    let l : Z ⟶ s.X₁ := hs.fIsKernel.lift t
    have hl : l = 0 := hX₁ l hZ
    have hfac : l ≫ s.f = k := hs.fIsKernel.fac t WalkingParallelPair.zero
    simp [← hfac, hl]

end Extensions

end ObjectProperty

variable [Abelian C]

namespace Abelian

/-- In an abelian category, the projection `Subobject.pullbackπ f B` from the pullback of a
subobject `B` along an epimorphism `f` is an epimorphism. -/
instance {X Y : C} (f : X ⟶ Y) [Epi f] (B : Subobject Y) : Epi (Subobject.pullbackπ f B) :=
  epi_fst_of_isLimit _ _ (Subobject.isPullback f B).isLimit

section PullbackCokernel

variable {X : C} {A : Subobject X} (B : Subobject (cokernel A.arrow))

/-- For `A : Subobject X`, the pullback of `B : Subobject (cokernel A.arrow)` along
`cokernel.π A.arrow` is a subobject of `X` that contains `A`. -/
lemma le_pullback_cokernel_π :
    A ≤ (Subobject.pullback (cokernel.π A.arrow)).obj B :=
  Subobject.le_of_comm
    ((Subobject.isPullback (cokernel.π A.arrow) B).lift 0 A.arrow (by simp))
    ((Subobject.isPullback (cokernel.π A.arrow) B).lift_snd 0 A.arrow (by simp))

/-- The canonical inclusion of `A` into the pullback of `B` along `cokernel.π A.arrow`,
composed with the projection `Subobject.pullbackπ` onto `B`, vanishes. -/
lemma ofLE_comp_pullbackπ_cokernel_π :
    Subobject.ofLE A _ (le_pullback_cokernel_π B) ≫
      Subobject.pullbackπ (cokernel.π A.arrow) B = 0 := by
  apply (cancel_mono B.arrow).mp
  rw [Category.assoc, (Subobject.isPullback (cokernel.π A.arrow) B).toCommSq.w,
    ← Category.assoc, Subobject.ofLE_arrow (le_pullback_cokernel_π B), cokernel.condition,
    zero_comp]

/-- Given a subobject `A` of `X` and a subobject `B` of `cokernel A.arrow`, the canonical
inclusion of `A` into the pullback of `B` along `cokernel.π A.arrow` is a kernel of
`Subobject.pullbackπ (cokernel.π A.arrow) B`. -/
noncomputable def isLimitKernelForkPullbackπCokernelπ :
    IsLimit (KernelFork.ofι _ (ofLE_comp_pullbackπ_cokernel_π B)) := by
  let A' := (Subobject.pullback (cokernel.π A.arrow)).obj B
  -- `A.arrow` is a kernel of `cokernel.π A.arrow`, since it is a monomorphism
  have hker := monoIsKernelOfCokernel
    (CokernelCofork.ofπ (cokernel.π A.arrow) (cokernel.condition A.arrow))
    (cokernelIsCokernel A.arrow)
  apply KernelFork.IsLimit.ofι' _ (ofLE_comp_pullbackπ_cokernel_π B)
  intro Z f hf
  -- a map into `A'` killed by `pullbackπ` is, after `A'.arrow`, killed by `cokernel.π A.arrow`,
  -- so it factors through `A`; that factorization is the required lift
  have hf' : (f ≫ A'.arrow) ≫ cokernel.π A.arrow = 0 := by
    rw [Category.assoc, ← (Subobject.isPullback (cokernel.π A.arrow) B).toCommSq.w,
      ← Category.assoc, hf, zero_comp]
  let s : KernelFork (cokernel.π A.arrow) := KernelFork.ofι (f ≫ A'.arrow) hf'
  refine ⟨hker.lift s, ?_⟩
  apply (cancel_mono A'.arrow).mp
  rw [Category.assoc, Subobject.ofLE_arrow (le_pullback_cokernel_π B)]
  exact Fork.IsLimit.lift_ι hker

/-- Given a subobject `A` of `X` and a subobject `B` of `cokernel A.arrow`, the short complex
`A ⟶ (Subobject.pullback (cokernel.π A.arrow)).obj B ⟶ B` with first map the canonical
inclusion and second map `Subobject.pullbackπ`. -/
noncomputable def shortComplexPullbackπCokernelπ : ShortComplex C :=
  ShortComplex.mk _ _ (ofLE_comp_pullbackπ_cokernel_π B)

/-- The short complex `A ⟶ (Subobject.pullback (cokernel.π A.arrow)).obj B ⟶ B` is short
exact; that is, the pullback of `B` along `cokernel.π A.arrow` is an extension of `B`
by `A`. -/
lemma shortExact_shortComplexPullbackπCokernelπ :
    (shortComplexPullbackπCokernelπ B).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (isLimitKernelForkPullbackπCokernelπ B)
  mono_f := by dsimp [shortComplexPullbackπCokernelπ]; infer_instance
  epi_g := by dsimp [shortComplexPullbackπCokernelπ]; infer_instance

end PullbackCokernel

end Abelian

namespace ObjectProperty

open Abelian

/-- If `P` is closed under quotients and coproducts, then the supremum of the `P`-subobjects
of any object satisfies `P`; that is, every object has a largest `P`-subobject. -/
lemma prop_sSup (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] (X : C) :
    P (Subobject.sSup {A : Subobject X | P (A : C)}) := by
  -- `Subobject.sSup s` is the image of the canonical map out of the coproduct of the
  -- members of `s`, so it is a quotient of a coproduct of objects satisfying `P`.
  apply P.prop_of_iso
    (Subobject.underlyingIso (Limits.image.ι (Subobject.smallCoproductDesc _))).symm
  apply P.prop_of_epi (Limits.factorThruImage _)
  apply ObjectProperty.prop_colimit
  rintro ⟨⟨_, S, hS, rfl⟩⟩
  simpa using hS

/-- If `P` is closed under quotients, extensions, and coproducts, then for any `X`, the
cokernel of the arrow of the largest `P`-subobject of `X` satisfies `P.rightOrthogonal`. -/
lemma rightOrthogonal_cokernel_sSup (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] (X : C) :
    P.rightOrthogonal (cokernel (Subobject.sSup {A : Subobject X | P (A : C)}).arrow) := by
  rw [ObjectProperty.rightOrthogonal_iff]
  intro Z f hZ
  let A : Subobject X := Subobject.sSup {A : Subobject X | P (A : C)}
  -- `B` is the image of `f`, viewed as a subobject of the cokernel.
  let B : Subobject (cokernel A.arrow) := Subobject.mk (Abelian.image.ι f)
  have hB : P (B : C) := P.prop_of_iso (Subobject.underlyingIso (Abelian.image.ι f)).symm
    (P.prop_of_epi (Abelian.factorThruImage f) hZ)
  -- The pullback `A'` of `B` along the cokernel projection is an extension of `B` by `A`,
  -- so it satisfies `P` and is therefore contained in `A`.
  let A' : Subobject X := (Subobject.pullback (cokernel.π A.arrow)).obj B
  have hA' : P (A' : C) :=
    P.prop_X₂_of_shortExact (shortExact_shortComplexPullbackπCokernelπ B) (prop_sSup P X) hB
  have hle : A' ≤ A := Subobject.le_sSup _ _ hA'
  -- Hence the projection of `A'` onto `B` vanishes, so `B`, and with it the image of `f`,
  -- is zero.
  have hzero : A'.arrow ≫ cokernel.π A.arrow = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc, cokernel.condition, comp_zero]
  have hπ : Subobject.pullbackπ (cokernel.π A.arrow) B = 0 := by
    apply (cancel_mono B.arrow).mp
    rw [(Subobject.isPullback (cokernel.π A.arrow) B).toCommSq.w, hzero, zero_comp]
  have himf : IsZero (Abelian.image f) :=
    IsZero.of_iso (IsZero.of_epi_eq_zero (Subobject.pullbackπ (cokernel.π A.arrow) B) hπ)
      (Subobject.underlyingIso (Abelian.image.ι f)).symm
  simp [← Abelian.image.fac f, IsZero.eq_zero_of_src himf]

/-- If `P` is closed under quotients, extensions, and coproducts, then
`P.rightOrthogonal.leftOrthogonal ≤ P`. Together with
`ObjectProperty.le_rightOrthogonal_leftOrthogonal`, this gives equality
`rightOrthogonal_leftOrthogonal_eq_self`. -/
lemma rightOrthogonal_leftOrthogonal_le (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P.rightOrthogonal.leftOrthogonal ≤ P :=
  fun X hX ↦
    let A : Subobject X := Subobject.sSup {A : Subobject X | P (A : C)}
    haveI : Epi A.arrow :=
      Preadditive.epi_of_cokernel_zero (hX (cokernel.π _) (rightOrthogonal_cokernel_sSup P X))
    P.prop_of_epi A.arrow (prop_sSup P X)

/-- If an object property `P` in an abelian category is closed under quotients, extensions,
and coproducts, then `P.rightOrthogonal.leftOrthogonal = P`. -/
theorem rightOrthogonal_leftOrthogonal_eq_self (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P.rightOrthogonal.leftOrthogonal = P :=
  le_antisymm P.rightOrthogonal_leftOrthogonal_le P.le_rightOrthogonal_leftOrthogonal

end ObjectProperty

namespace Abelian

/-- A torsion theory in an abelian category consists of two classes, `T` and `F`, of
torsion and torsion-free objects, respectively, such that `T` is the left orthogonal
of `F` and `F` is the right orthogonal of `T`. -/
structure TorsionTheory (T F : ObjectProperty C) : Prop where
  torsion_eq_leftOrthogonal : T = F.leftOrthogonal
  free_eq_rightOrthogonal : F = T.rightOrthogonal

/-- A property of objects is a torsion class if it is the torsion class of some torsion theory.

This is a typeclass, on the model of `Functor.IsLeftAdjoint`: every construction of a torsion
theory registers an instance for its torsion class, and the closure properties of torsion
classes are then available by instance search. See `IsTorsionClass.torsionTheory` for the
torsion theory itself. -/
class IsTorsionClass (P : ObjectProperty C) : Prop where
  exists_torsionFreeClass : ∃ F, TorsionTheory P F

/-- A property of objects is a torsion-free class if it is the torsion-free class of some
torsion theory. This is a typeclass; see `IsTorsionClass` for the design and
`IsTorsionFreeClass.torsionTheory` for the torsion theory itself. -/
class IsTorsionFreeClass (P : ObjectProperty C) : Prop where
  exists_torsionClass : ∃ T, TorsionTheory T P

namespace TorsionTheory

variable {T F : ObjectProperty C}

/-- An object of a torsion theory is torsion iff every morphism from it to a torsion-free
object vanishes. -/
lemma torsion_iff (hTF : TorsionTheory T F) (X : C) :
    T X ↔ ∀ ⦃Y : C⦄ (f : X ⟶ Y), F Y → f = 0 := by
  rw [hTF.torsion_eq_leftOrthogonal, ObjectProperty.leftOrthogonal_iff]

/-- An object of a torsion theory is torsion-free iff every morphism to it from a torsion
object vanishes. -/
lemma free_iff (hTF : TorsionTheory T F) (Y : C) :
    F Y ↔ ∀ ⦃X : C⦄ (f : X ⟶ Y), T X → f = 0 := by
  rw [hTF.free_eq_rightOrthogonal, ObjectProperty.rightOrthogonal_iff]

/-- The torsion theory generated by a property of objects `P`: the torsion-free class is the
right orthogonal of `P`, and the torsion class is the left orthogonal of that. -/
lemma generated_by (P : ObjectProperty C) :
    TorsionTheory P.rightOrthogonal.leftOrthogonal P.rightOrthogonal where
  torsion_eq_leftOrthogonal := rfl
  free_eq_rightOrthogonal :=
    (ObjectProperty.rightOrthogonal_leftOrthogonal_rightOrthogonal P).symm

/-- The torsion theory cogenerated by a property of objects `P`: the torsion class is the
left orthogonal of `P`, and the torsion-free class is the right orthogonal of that. -/
lemma cogenerated_by (P : ObjectProperty C) :
    TorsionTheory P.leftOrthogonal P.leftOrthogonal.rightOrthogonal where
  torsion_eq_leftOrthogonal :=
    (ObjectProperty.leftOrthogonal_rightOrthogonal_leftOrthogonal P).symm
  free_eq_rightOrthogonal := rfl

/-- A torsion theory on `C` induces a torsion theory on `Cᵒᵖ` with the roles of the
torsion and torsion-free classes exchanged. -/
lemma op (hTF : TorsionTheory T F) : TorsionTheory F.op T.op where
  torsion_eq_leftOrthogonal := by
    rw [ObjectProperty.leftOrthogonal_op, hTF.free_eq_rightOrthogonal]
  free_eq_rightOrthogonal := by
    rw [ObjectProperty.rightOrthogonal_op, hTF.torsion_eq_leftOrthogonal]

/-- A torsion theory on `Cᵒᵖ` induces a torsion theory on `C` with the roles of the
torsion and torsion-free classes exchanged. -/
lemma unop {T F : ObjectProperty Cᵒᵖ} (hTF : TorsionTheory T F) :
    TorsionTheory F.unop T.unop where
  torsion_eq_leftOrthogonal := by
    rw [ObjectProperty.leftOrthogonal_unop, hTF.free_eq_rightOrthogonal]
  free_eq_rightOrthogonal := by
    rw [ObjectProperty.rightOrthogonal_unop, hTF.torsion_eq_leftOrthogonal]

/-- The torsion class of a torsion theory is closed under quotients. -/
lemma torsion_isClosedUnderQuotients (hTF : TorsionTheory T F) : T.IsClosedUnderQuotients :=
  hTF.torsion_eq_leftOrthogonal ▸ inferInstance

/-- The torsion class of a torsion theory is closed under extensions. -/
lemma torsion_isClosedUnderExtensions (hTF : TorsionTheory T F) : T.IsClosedUnderExtensions :=
  hTF.torsion_eq_leftOrthogonal ▸ inferInstance

/-- The torsion class of a torsion theory is closed under coproducts. -/
lemma torsion_isClosedUnderCoproducts (hTF : TorsionTheory T F) (J : Type w) :
    T.IsClosedUnderColimitsOfShape (Discrete J) :=
  hTF.torsion_eq_leftOrthogonal ▸ inferInstance

/-- The torsion-free class of a torsion theory is closed under subobjects. -/
lemma free_isClosedUnderSubobjects (hTF : TorsionTheory T F) : F.IsClosedUnderSubobjects :=
  hTF.free_eq_rightOrthogonal ▸ inferInstance

/-- The torsion-free class of a torsion theory is closed under extensions. -/
lemma free_isClosedUnderExtensions (hTF : TorsionTheory T F) : F.IsClosedUnderExtensions :=
  hTF.free_eq_rightOrthogonal ▸ inferInstance

/-- The torsion-free class of a torsion theory is closed under products. -/
lemma free_isClosedUnderProducts (hTF : TorsionTheory T F) (J : Type w) :
    F.IsClosedUnderLimitsOfShape (Discrete J) :=
  hTF.free_eq_rightOrthogonal ▸ inferInstance

/-- A torsion theory exhibits its torsion class as a torsion class. -/
lemma isTorsionClass (hTF : TorsionTheory T F) : IsTorsionClass T := ⟨⟨F, hTF⟩⟩

/-- A torsion theory exhibits its torsion-free class as a torsion-free class. -/
lemma isTorsionFreeClass (hTF : TorsionTheory T F) : IsTorsionFreeClass F := ⟨⟨T, hTF⟩⟩

end TorsionTheory

/-- A left orthogonal is the torsion class of the torsion theory it cogenerates. -/
instance (P : ObjectProperty C) : IsTorsionClass P.leftOrthogonal :=
  (TorsionTheory.cogenerated_by P).isTorsionClass

/-- A right orthogonal is the torsion-free class of the torsion theory it generates. -/
instance (P : ObjectProperty C) : IsTorsionFreeClass P.rightOrthogonal :=
  (TorsionTheory.generated_by P).isTorsionFreeClass

/-- A property of objects is a torsion class iff it is the left orthogonal of its right
orthogonal. -/
lemma isTorsionClass_iff_rightOrthogonal_leftOrthogonal_eq (P : ObjectProperty C) :
    IsTorsionClass P ↔ P.rightOrthogonal.leftOrthogonal = P :=
  ⟨fun ⟨⟨F, h⟩⟩ ↦ by rw [← h.free_eq_rightOrthogonal, ← h.torsion_eq_leftOrthogonal],
    fun h ↦ ⟨⟨P.rightOrthogonal, ⟨h.symm, rfl⟩⟩⟩⟩

/-- A property of objects is a torsion-free class iff it is the right orthogonal of its left
orthogonal. -/
lemma isTorsionFreeClass_iff_leftOrthogonal_rightOrthogonal_eq (P : ObjectProperty C) :
    IsTorsionFreeClass P ↔ P.leftOrthogonal.rightOrthogonal = P :=
  ⟨fun ⟨⟨T, h⟩⟩ ↦ by rw [← h.torsion_eq_leftOrthogonal, ← h.free_eq_rightOrthogonal],
    fun h ↦ ⟨⟨P.leftOrthogonal, ⟨rfl, h.symm⟩⟩⟩⟩

namespace IsTorsionClass

variable (P : ObjectProperty C) [IsTorsionClass P]

/-- The torsion theory whose torsion class is `P`; its torsion-free class is necessarily
`P.rightOrthogonal`. -/
lemma torsionTheory : TorsionTheory P P.rightOrthogonal :=
  ⟨((isTorsionClass_iff_rightOrthogonal_leftOrthogonal_eq P).mp inferInstance).symm, rfl⟩

/-- A torsion class is closed under quotients. -/
instance : P.IsClosedUnderQuotients := (torsionTheory P).torsion_isClosedUnderQuotients

/-- A torsion class is closed under extensions. -/
instance : P.IsClosedUnderExtensions := (torsionTheory P).torsion_isClosedUnderExtensions

/-- A torsion class is closed under colimits of any shape, not only coproducts. -/
instance {J : Type u'} [Category.{v'} J] : P.IsClosedUnderColimitsOfShape J :=
  (torsionTheory P).torsion_eq_leftOrthogonal ▸ inferInstance

/-- The opposite of a torsion class is a torsion-free class. -/
instance : IsTorsionFreeClass P.op := (torsionTheory P).op.isTorsionFreeClass

end IsTorsionClass

namespace IsTorsionFreeClass

variable (P : ObjectProperty C) [IsTorsionFreeClass P]

/-- The torsion theory whose torsion-free class is `P`; its torsion class is necessarily
`P.leftOrthogonal`. -/
lemma torsionTheory : TorsionTheory P.leftOrthogonal P :=
  ⟨rfl, ((isTorsionFreeClass_iff_leftOrthogonal_rightOrthogonal_eq P).mp inferInstance).symm⟩

/-- A torsion-free class is closed under subobjects. -/
instance : P.IsClosedUnderSubobjects := (torsionTheory P).free_isClosedUnderSubobjects

/-- A torsion-free class is closed under extensions. -/
instance : P.IsClosedUnderExtensions := (torsionTheory P).free_isClosedUnderExtensions

/-- A torsion-free class is closed under limits of any shape, not only products. -/
instance {J : Type u'} [Category.{v'} J] : P.IsClosedUnderLimitsOfShape J :=
  (torsionTheory P).free_eq_rightOrthogonal ▸ inferInstance

/-- The opposite of a torsion-free class is a torsion class. -/
instance : IsTorsionClass P.op := (torsionTheory P).op.isTorsionClass

end IsTorsionFreeClass

/-- In a well-powered abelian category with coproducts, a property of objects `P` is a torsion
class if and only if it is closed under quotients, extensions, and coproducts. This is a
theorem of Dickson; see [Bo Stenström, *Rings of Quotients*][stenstrom1975], Chapter VI. -/
theorem isTorsionClass_iff (P : ObjectProperty C)
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    IsTorsionClass P ↔
      P.IsClosedUnderQuotients ∧ P.IsClosedUnderExtensions ∧
        ∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J) := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, fun _ ↦ inferInstance⟩, ?_⟩
  -- these hypotheses are consumed as instances by `rightOrthogonal_leftOrthogonal_eq_self`
  rintro ⟨hquot, hext, hcoprod⟩
  exact (isTorsionClass_iff_rightOrthogonal_leftOrthogonal_eq P).mpr
    P.rightOrthogonal_leftOrthogonal_eq_self

/-- A property of objects is a torsion-free class if and only if its opposite is a torsion
class in the opposite category. -/
lemma isTorsionFreeClass_iff_isTorsionClass_op (P : ObjectProperty C) :
    IsTorsionFreeClass P ↔ IsTorsionClass P.op :=
  ⟨fun _ ↦ inferInstance, fun ⟨⟨Q, hQ⟩⟩ ↦ ⟨⟨Q.unop, hQ.unop⟩⟩⟩

/-- In a well-copowered abelian category with products, a property of objects `P` is a
torsion-free class if and only if it is closed under subobjects, extensions, and products.
This is the dual of `isTorsionClass_iff`, obtained by transporting it through the
opposite category. -/
theorem isTorsionFreeClass_iff (P : ObjectProperty C)
    [LocallySmall.{w} C] [WellPowered.{w} Cᵒᵖ] [HasProducts.{w} C] :
    IsTorsionFreeClass P ↔
      P.IsClosedUnderSubobjects ∧ P.IsClosedUnderExtensions ∧
        ∀ J : Type w, P.IsClosedUnderLimitsOfShape (Discrete J) :=
  (isTorsionFreeClass_iff_isTorsionClass_op P).trans <|
    (isTorsionClass_iff P.op).trans <|
      and_congr (ObjectProperty.isClosedUnderQuotients_op_iff P) <|
        and_congr (ObjectProperty.isClosedUnderExtensions_op_iff P) <|
          forall_congr' fun J ↦
            ((P.isClosedUnderLimitsOfShape_iff_op (Discrete J)).trans
              (P.op.isClosedUnderColimitsOfShape_iff_of_equivalence (Discrete.opposite J))).symm

end Abelian

end CategoryTheory
