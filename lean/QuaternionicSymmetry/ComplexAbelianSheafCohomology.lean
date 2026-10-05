import QuaternionicSymmetry.ComplexificationConstantSheaf
import QuaternionicSymmetry.DerivedExactAdjunctionExt

/-! Actual derived cohomology of a small complex-module sheaf agrees with
the cohomology of its underlying abelian sheaf in every degree. The exact
coefficient adjunction and its constant-source comparison are proved,
not supplied as hypotheses. -/

namespace QuaternionicSymmetry.ComplexAbelianSheafCohomology

open CategoryTheory CategoryTheory.Abelian
open ComplexAbelianSheafAdjunction
noncomputable section

variable (X : TopCat.{0})

local instance : HasExt.{1} (complexSheaves X) := HasExt.standard _
local instance : HasExt.{1} (additiveSheaves X) := HasExt.standard _

abbrev complexCohomology (F : complexSheaves X) (n : ℕ) : Type 1 :=
  Ext.{1} ((constantSheaf (topology X) (ModuleCat.{0} ℂ)).obj
    (ModuleCat.of ℂ (ULift.{0} ℂ))) F n

def cohomologyAddEquiv (F : complexSheaves X) (n : ℕ) :
    complexCohomology X F n ≃+ ((forget X).obj F).H n := by
  letI := HasDerivedCategory.standard (C := complexSheaves X)
  letI := HasDerivedCategory.standard (C := additiveSheaves X)
  exact (((extFunctor n).mapIso
    (ComplexificationConstantSheaf.integralIso X).op).app F).addCommGroupIsoToAddEquiv.trans
      (DerivedExactAdjunctionExt.extAddEquiv (complexifyAdjunction X)
        ((constantSheaf (topology X) AddCommGrpCat).obj
          (AddCommGrpCat.of (ULift.{0} ℤ))) F n)

theorem cohomology_subsingleton (F : complexSheaves X) (n : ℕ)
    (h : Subsingleton (complexCohomology X F n)) :
    Subsingleton (((forget X).obj F).H n) := by
  letI := h
  exact (cohomologyAddEquiv X F n).symm.injective.subsingleton

end
end QuaternionicSymmetry.ComplexAbelianSheafCohomology
