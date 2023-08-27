import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.StructuredArrow

namespace CategoryTheory

namespace Functor

variable {C D H : Type _} [Category C] [Category D] [Category H]

--class IsKanExtension (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F) : Prop where
--    have := (@CostructuredArrow.mk _ _ _ _ _ _ ((whiskeringLeft C H D).obj L) α

end Functor

end CategoryTheory
