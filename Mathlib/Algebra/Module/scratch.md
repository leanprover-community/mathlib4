Test object in higher universe:
```lean
class Module.Injective : Prop where
  out : ∀ ⦃X Y : Type max u v⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X →ₗ[R] Y) (_ : Function.Injective f) (g : X →ₗ[R] Q),
    ∃ h : Y →ₗ[R] Q, ∀ x, h (f x) = g x
```

```lean
theorem Module.injective_object_of_injective_module [inj : Module.Injective R Q] :
    CategoryTheory.Injective (ModuleCat.of R Q) where
  factors {X Y} g f m := by
    let f' : ULift.{max u v} X →ₗ[R] ULift.{max u v} Y :=
      ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap
    have hf' : Function.Injective f' := ULift.up_injective.comp <|
      (ModuleCat.mono_iff_injective _).mp m |>.comp ULift.down_injective
    let g' : ULift.{max u v} X →ₗ[R] Q := g ∘ₗ ULift.moduleEquiv.toLinearMap
    obtain ⟨l, h⟩ := inj.out f' hf' g'
    exact ⟨l ∘ₗ ULift.moduleEquiv.symm.toLinearMap, LinearMap.ext fun x ↦ by aesop⟩
```
is doable, but
```lean
theorem Module.injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R Q] :
    Module.Injective R Q where
  out X Y _ _ _ _ f hf g := by
    have H := @CategoryTheory.Injective.factors (self := inj)
    sorry
```
seems not to be possible because `X, Y` are in universe `max u v` but `H` want universe modules to be in universe `v`


----------

```lean
class Module.Injective : Prop where
  out : ∀ ⦃X Y : Type v⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X →ₗ[R] Y) (_ : Function.Injective f) (g : X →ₗ[R] Q),
    ∃ h : Y →ₗ[R] Q, ∀ x, h (f x) = g x
```
is fine up until `Module.Baer.of_injective` because ideals are in universe `u` and can't be transferred to `v`.
