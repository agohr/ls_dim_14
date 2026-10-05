import QuaternionicSymmetry.ComplexProjectiveActualConeAwayComplexAlgebra
import QuaternionicSymmetry.ComplexProjectiveActualConeComplexStructure

/-! Mathlib's actual homogeneous-localization chart iso is over `Spec ℂ`
for the canonical scalar structure induced from the whole cone Proj. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenComplexStructure

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeDegreeZeroScalars
noncomputable section

variable {d : ℕ}

theorem basicOpenIsoSpec_complexStructure
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i)))) =
    (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
      actualConeProjToSpecComplex A hA hNonempty := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  let e := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  rw [← cancel_epi e.inv]
  simp [e]
  rw [← Category.assoc, Proj.basicOpenIsoSpec_inv_ι, actualConeProjToSpecComplex]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenComplexStructure
