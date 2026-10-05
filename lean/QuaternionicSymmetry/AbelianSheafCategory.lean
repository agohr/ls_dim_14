import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-! Expose the existing abelian-category structure through Mathlib's
`TopCat.Sheaf` wrapper, for sheaves of abelian groups. -/

namespace QuaternionicSymmetry.AbelianSheafCategory

open CategoryTheory TopologicalSpace
noncomputable section

universe u v

instance topCatSheafPreadditive (X : TopCat.{u}) :
    Preadditive (TopCat.Sheaf AddCommGrpCat.{v} X) := by
  change Preadditive (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})
  infer_instance

instance topCatSheafAbelian (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] :
    Abelian (TopCat.Sheaf AddCommGrpCat.{v} X) := by
  change Abelian (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})
  infer_instance

end
end QuaternionicSymmetry.AbelianSheafCategory
