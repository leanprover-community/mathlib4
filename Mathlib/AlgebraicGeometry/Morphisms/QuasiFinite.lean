/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Quasi-finite morphisms

We say that a morphism `f : X ⟶ Y` is locally quasi finite if `Γ(Y, U) ⟶ Γ(X, V)` is
quasi-finite (in the mathlib sense) for every pair of affine opens that `f` maps one into the other.

This is equivalent to all the fibers `f⁻¹(x)` having an open cover of `κ(x)`-finite schemes.
Note that this does not require `f` to be quasi-compact nor locally of finite type.

We prove that this is stable under composition and base change, and is right cancellative.

## TODO (@erdOne):
- If `f` is quasi-compact,
  then `f` is locally quasi-finite iff all the fibers `f⁻¹(x)` are `κ(x)`-finite.
- If `f` is locally of finite type, then `f` is locally quasi-finite iff `f` has discrete fibers.
- If `f` is of finite type, then `f` is locally quasi-finite iff `f` has finite fibers.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open Scheme

/--
We say that a morphism `f : X ⟶ Y` is locally quasi finite if `Γ(Y, U) ⟶ Γ(X, V)` is
quasi-finite (in the mathlib sense) for every pair of affine opens that `f` maps one into the other.

This is equivalent to all the fibers `f⁻¹(x)` having an open cover of `κ(x)`-finite schemes.
Note that this does not require `f` to be quasi-compact nor locally of finite type.

TODO (@erdOne): prove the following
If one assumes quasi-compact, this is equivalent to all the fibers `f⁻¹(x)` being `κ(x)`-finite.
If one assumes locally of finite type, this is equivalent to `f` having discrete fibers.
If one assumes finite type, this is equivalent to `f` having finite fibers.
-/
@[mk_iff]
class LocallyQuasiFinite : Prop where
  quasiFinite_appLE :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.QuasiFinite

instance : HasRingHomProperty @LocallyQuasiFinite RingHom.QuasiFinite where
  isLocal_ringHomProperty := RingHom.QuasiFinite.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    simp [locallyQuasiFinite_iff, affineLocally_iff_affineOpens_le, affineOpens]

instance : MorphismProperty.IsStableUnderComposition @LocallyQuasiFinite :=
  HasRingHomProperty.stableUnderComposition RingHom.QuasiFinite.stableUnderComposition

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite f] [LocallyQuasiFinite g] : LocallyQuasiFinite (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹_› ‹_›

instance (priority := low) [IsFinite f] : LocallyQuasiFinite f := by
  rw [HasAffineProperty.eq_targetAffineLocally @IsFinite] at ‹IsFinite f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine ((targetAffineLocally_affineAnd_eq_affineLocally
    RingHom.QuasiFinite.propertyIsLocal).le f ?_).2
  exact targetAffineLocally_affineAnd_le (fun hf ↦ .of_finite hf) f ‹_›

instance (priority := low) [IsImmersion f] : LocallyQuasiFinite f := by
  rw [← f.liftCoborder_ι]
  have := HasRingHomProperty.of_isOpenImmersion (P := @LocallyQuasiFinite)
    RingHom.QuasiFinite.holdsForLocalizationAway.containsIdentities (f := f.coborderRange.ι)
  infer_instance

theorem LocallyQuasiFinite.of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite (f ≫ g)] : LocallyQuasiFinite f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.QuasiFinite.of_comp) ‹_›

instance : MorphismProperty.IsMultiplicative @LocallyQuasiFinite where
  id_mem _ := inferInstance

instance : MorphismProperty.IsStableUnderBaseChange @LocallyQuasiFinite :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.QuasiFinite.isStableUnderBaseChange

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite g] :
    LocallyQuasiFinite (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [LocallyQuasiFinite f] : LocallyQuasiFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

end AlgebraicGeometry
