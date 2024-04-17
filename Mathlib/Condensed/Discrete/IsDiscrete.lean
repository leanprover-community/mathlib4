import Mathlib.Condensed.Discrete.Colimit
import Mathlib.Condensed.Discrete.LocallyConstant

universe u

open CategoryTheory Limits Functor FintypeCat

namespace Condensed

variable {C : Type*} [Category C]
  [HasWeakSheafify (coherentTopology CompHaus) C] (X : Condensed C)

class IsDiscrete : Prop where
  isoDiscrete : ∃ (X' : C), Nonempty (X ≅ (discrete C).obj X')

end Condensed

namespace CondensedSet

open Condensed

variable (X : CondensedSet.{u})

theorem isDiscrete_iff_nonempty_iso_LC : IsDiscrete X ↔ ∃ X',
    Nonempty (X ≅ LocallyConstant.functor.obj X') := by
  constructor
  · intro h
    obtain ⟨X', ⟨i⟩⟩ := h.isoDiscrete
    exact ⟨X', ⟨i ≪≫ LocallyConstant.iso.symm.app X'⟩⟩
  · intro h
    obtain ⟨X', ⟨i⟩⟩ := h
    exact ⟨X', ⟨i ≪≫ LocallyConstant.iso.app X'⟩⟩

def SetOfDiscrete [IsDiscrete X] : Type (u+1) := (IsDiscrete.isoDiscrete (X := X)).choose

noncomputable
def isoSetOfDiscrete [IsDiscrete X] : X ≅ (discrete (Type (u+1))).obj (SetOfDiscrete X) :=
  (IsDiscrete.isoDiscrete (X := X)).choose_spec.some

noncomputable
def isoSetOfDiscrete' [IsDiscrete X] : X ≅ LocallyConstant.functor.obj (SetOfDiscrete X) :=
  isoSetOfDiscrete X ≪≫ LocallyConstant.iso.symm.app _

noncomputable
def isoSetOfDiscrete'_val [IsDiscrete X] :
    X.val ≅ (LocallyConstant.functor.obj (SetOfDiscrete X)).val where
  hom := (isoSetOfDiscrete' X).hom.val
  inv := (isoSetOfDiscrete' X).inv.val
  hom_inv_id := (Sheaf.Hom.ext_iff _ _).mp (isoSetOfDiscrete' X).hom_inv_id
  inv_hom_id := (Sheaf.Hom.ext_iff _ _).mp (isoSetOfDiscrete' X).inv_hom_id

noncomputable def isColimitLocallyConstantPresheaf (X' : Type (u+1)) (S : Profinite.{u}) :
    IsColimit ((profiniteToCompHaus.op ⋙ (LocallyConstant.functor.{u}.obj X').val).mapCocone
      S.asLimitCone.op) := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant S X')
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} _ S.asLimit f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (S.asLimitCone.π.app i) = fj.comap (S.asLimitCone.π.app j))
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp only [LocallyConstant.functor_obj_val, comp_obj, op_obj, Opposite.unop_op,
      profiniteToCompHaus_obj, LocallyConstant.functorToPresheaves_obj_obj,
      toProfinite_obj_toCompHaus_toTop_α, Functor.comp_map, op_map, Quiver.Hom.unop_op,
      profiniteToCompHaus_map, LocallyConstant.functorToPresheaves_obj_map]
    apply DFunLike.ext
    intro x'
    obtain ⟨x, hx⟩ := (k.proj_surjective : Function.Surjective (S.asLimitCone.π.app k)) x'
    rw [← hx]
    change fi ((S.asLimitCone.π.app k ≫ (S.fintypeDiagram ⋙ toProfinite).map ki) x) =
      fj ((S.asLimitCone.π.app k ≫ (S.fintypeDiagram ⋙ toProfinite).map kj) x)
    have h := LocallyConstant.congr_fun h x
    rwa [S.asLimitCone.w, S.asLimitCone.w]

theorem isDiscrete_of_isColimit_mapCone (h : ∀ S : Profinite.{u},
    IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op) :
    IsDiscrete X := by
  sorry
  -- Suffices to give an iso `X ≅ lanCondensedSet X(*)`.
  --

noncomputable def isColimitMapConeOfIsDiscrete [IsDiscrete X] (S : Profinite.{u}) :
    IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op :=
  IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op (isoSetOfDiscrete'_val X).symm)
    (isColimitLocallyConstantPresheaf (SetOfDiscrete X) S)
