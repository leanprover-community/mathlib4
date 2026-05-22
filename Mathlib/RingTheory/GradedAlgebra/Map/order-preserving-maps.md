
order preserving
order reflecting
⊓ meet (limit) preserving
⊔ join (colimit) preserving


Mathlib.Order.Hom.Lattice:
  SupHom : preserves ⊔
  InfHom : preserves ⊓
  LatticeHom: join & meet preserving

Mathlib.Order.Hom.BoundedLattice
  SupBotHom: preserves ⊔ and ⊥.
  InfTopHom: preserves ⊓ and ⊤.
  BoundedLatticeHom: preserves ⊤, ⊥, ⊔ and ⊓

Mathlib.Order.Hom.CompleteLattice
  sSupHom: preserves ⨆.
  sInfHom: preserves ⨅.
  FrameHom: preserves ⨆, ⊓ and ⊤.
  CompleteLatticeHom: preserves ⨆ and ⨅.


Mathlib does *not* bake `Monotone` into the definition of sup-preserving maps. The bundled
structures and the `Class` predicates carry only the operation-preservation hypothesis. The link to
order-preservation is then a theorem expressed as a typeclass instance:

```lean
instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β]
    [SupHomClass F α β] : OrderHomClass F α β
```
The same pattern is used uniformly:

- `LatticeHomClass extends SupHomClass, InfHomClass` — so it inherits `toOrderHomClass` for free
   through `SupHomClass`
- `BoundedLatticeHomClass extends LatticeHomClass`
- `sSupHomClass.toSupBotHomClass` feeds the chain `sSupHomClass →  SupBotHomClass → SupHomClass → OrderHomClass`
- `FrameHomClass extends InfTopHomClass` and `CompleteLatticeHomClass extends sInfHomClass,  sSupHomClass`
   likewise reach `OrderHomClass` transitively.

Similarly in the „opposite direction“: `OrderIsoClass` is defined directly via `map_le_map_iff`, and
the reverse instances `OrderIsoClass.toSupHomClass` / `.toLatticeHomClass` prove that order isos
automatically preserve ⊔ and ⊓ — again a theorem, not a definitional choice.


----

instances of AddSubmonoidClass:
  AddSubmonoid           (AddSubmonoid.instAddSubmonoidClass)
  Submodule              (Submodule.addSubmonoidClass)
  ClosedSubmodule        (ClosedSubmodule.instAddSubmonoidClass)
  SaturatedAddSubmonoid  (SaturatedAddSubmonoid.instAddSubmonoidClass)
  HomogeneousSubmodule   (instAddSubmonoidClassHomogeneousSubmodule)

But (Add)SubmonoidClass is also extended by other classes (found with grep):
  (Add)SubgroupClass           — Mathlib/Algebra/Group/Subgroup/Defs.lean:110,115
  SubsemiringClass /           — Mathlib/Algebra/Ring/Subsemiring/Defs.lean:28
  NonAssocSemiringClass-style  — Mathlib/Algebra/Ring/Subsemiring/Defs.lean:58
  NonUnitalSubsemiringClass    — Mathlib/RingTheory/NonUnitalSubsemiring/Defs.lean:54
  (Add)GroupConeClass          — Mathlib/Algebra/Order/Group/Cone.lean:27,33

And then these are extended by further classes, and so on …

For example, `AddSubgroup G` gets an `[AddSubmonoidClass (AddSubgroup G) G]` instance
                                 via `[AddSubgroupClass (AddSubgroup G) G]`.

``` lean
#check (inferInstance : AddSubmonoidClass (AddSubmonoid _) _)
#check (inferInstance : AddSubmonoidClass (AddSubgroup _) _)
#check @AddSubgroupClass.toAddSubmonoidClass
```
