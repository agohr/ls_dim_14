import QuaternionicSymmetry.ComplexAbelianSheafAdjunction
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Complexification takes the actual integral constant sheaf to the
actual rank-one complex constant sheaf. -/

namespace QuaternionicSymmetry.ComplexificationConstantSheaf

open CategoryTheory TopologicalSpace
open ComplexAbelianCoefficientAdjunction ComplexAbelianSheafAdjunction
noncomputable section

private def scalarUnitIso :
    (ModuleCat.extendScalars (Int.castRingHom ℂ)).obj (ModuleCat.of ℤ ℤ) ≅
      ModuleCat.of ℂ ℂ := by
  convert (TensorProduct.AlgebraTensorModule.rid ℤ ℂ ℂ).toModuleIso using 1
  dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
    ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
  congr 3 <;> first | exact Subsingleton.elim _ _ | exact proof_irrel_heq _ _

def coefficientUnitIso :
    complexification.obj (AddCommGrpCat.of (ULift.{0} ℤ)) ≅
      ModuleCat.of ℂ (ULift.{0} ℂ) :=
  (ModuleCat.extendScalars (Int.castRingHom ℂ)).mapIso
    ((integerEquivalence.unitIso.app (ModuleCat.of ℤ (ULift.{0} ℤ))).symm ≪≫
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso) ≪≫
    scalarUnitIso ≪≫
    (ULift.moduleEquiv : ULift.{0} ℂ ≃ₗ[ℂ] ℂ).symm.toModuleIso

def constantIso (X : TopCat.{0}) (A : AddCommGrpCat.{0}) :
    (complexify X).obj ((constantSheaf (topology X) AddCommGrpCat).obj A) ≅
      (constantSheaf (topology X) (ModuleCat.{0} ℂ)).obj
        (complexification.obj A) :=
  (presheafToSheafCompComposeAndSheafifyIso (topology X)
    complexification).app ((Functor.const (Opens X)ᵒᵖ).obj A) ≪≫
    (presheafToSheaf (topology X) (ModuleCat.{0} ℂ)).mapIso
      (Functor.constComp (Opens X)ᵒᵖ A complexification)

def integralIso (X : TopCat.{0}) :
    (complexify X).obj
        ((constantSheaf (topology X) AddCommGrpCat).obj
          (AddCommGrpCat.of (ULift.{0} ℤ))) ≅
      (constantSheaf (topology X) (ModuleCat.{0} ℂ)).obj
        (ModuleCat.of ℂ (ULift.{0} ℂ)) :=
  constantIso X _ ≪≫
    (constantSheaf (topology X) (ModuleCat.{0} ℂ)).mapIso coefficientUnitIso

end
end QuaternionicSymmetry.ComplexificationConstantSheaf
