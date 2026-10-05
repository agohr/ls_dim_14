import QuaternionicSymmetry.AbelianSheafCategory
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! Actual derived cohomology for small abelian sheaves on a topological
space. Sheafification and the standard Ext construction are supplied
internally by Mathlib, not left as additional geometric hypotheses. -/

namespace QuaternionicSymmetry.AbelianSheafCohomology

open CategoryTheory TopologicalSpace
noncomputable section

variable (B : Type) [TopologicalSpace B]

abbrev AbelianSheaves :=
  Sheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat.{0}

instance abelianSheavesHasExt : HasExt.{1} (AbelianSheaves B) :=
  HasExt.standard _

def integralSheaf : AbelianSheaves B :=
  (constantSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))

abbrev cohomology (A : AbelianSheaves B) (n : ℕ) : Type 1 := A.H n

end
end QuaternionicSymmetry.AbelianSheafCohomology
