import QuaternionicSymmetry.SheafComplexLinear
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! Canonical sheafification for small complex-module-valued presheaves. -/

namespace QuaternionicSymmetry.SheafComplexSheafification

open CategoryTheory TopologicalSpace

/-- Mathlib's plus-plus construction gives a left-exact sheafification
reflector for small complex-module-valued presheaves. -/
noncomputable def topCatHasSheafify (X : TopCat.{0}) :
    HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ) :=
  inferInstance

/-- Standard derived-category Ext for the corresponding sheaf category. -/
noncomputable def topCatHasExt (X : TopCat.{0}) :
    HasExt.{1} (TopCat.Sheaf (ModuleCat.{0} ℂ) X) := by
  letI := topCatHasSheafify X
  exact HasExt.standard _

end QuaternionicSymmetry.SheafComplexSheafification
