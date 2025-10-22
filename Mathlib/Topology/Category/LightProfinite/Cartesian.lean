import Mathlib.Topology.Category.CompHausLike.Cartesian
import Mathlib.Topology.Category.LightProfinite.Basic

universe u

open CategoryTheory Limits CompHausLike

namespace LightProfinite

noncomputable instance : CartesianMonoidalCategory LightProfinite.{u} :=
  cartesianMonoidalCategory

end LightProfinite
