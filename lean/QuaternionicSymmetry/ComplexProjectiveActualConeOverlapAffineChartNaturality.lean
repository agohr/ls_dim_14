import QuaternionicSymmetry.CategoryPullbackProductOverlapAffineChart
import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenOverlapRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeBasicOpenComplexStructure
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductOverlapIso

/-! Actual cone-Proj specialization of the typed affine-overlap chart
restriction squares. Both chart maps and the overlap use the canonical
global `Spec ℂ` structure. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapAffineChartNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeBasicOpenComplexStructure
open ComplexProjectiveActualConeBasicOpenOverlapIso
open ComplexProjectiveActualConeBasicOpenOverlapRestriction
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeProjProductOverlapIso
open CategoryPullbackProductOverlapIso
open CategoryPullbackProductOverlapChartNaturality
open CategoryPullbackProductOverlapIsoTransport
open CategoryPullbackProductOverlapAffineChart
open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r d : ℕ}

theorem actual_overlap_left_affine_chart_natural
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
    let g := actualConeProjToSpecComplex A hA hNonempty
    let u := (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
    let v := (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι
    let e := actualBasicOpenCoordinateOverlapIso A hA hNonempty i j
    let k := (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).hom
    let b := Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i))))
    let β := Spec.map (CommRingCat.ofHom
      (overlapRestrictionLeft A hA hNonempty i j).toRingHom)
    (baseChangedOverlapIso f g u v ≪≫
      asIso (overlapAffineBaseChange f g u v e)).inv ≫
      pullback.fst (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
      leftChartBaseChange f g u k b
        (basicOpenIsoSpec_complexStructure A hA hNonempty i) =
    affineLeftChartBaseChange f g u v e k b
      (basicOpenIsoSpec_complexStructure A hA hNonempty i) β
      (actualBasicOpenOverlapIso_inv_left_spec A hA hNonempty i j).symm := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  exact affineOverlap_leftChart_natural _ _ _ _ _ _ _ _ _ _

theorem actual_overlap_right_affine_chart_natural
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
    let g := actualConeProjToSpecComplex A hA hNonempty
    let u := (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
    let v := (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι
    let e := actualBasicOpenCoordinateOverlapIso A hA hNonempty i j
    let k := (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A j)
      (coordinateClass_mem_degreeOne A j) (by omega)).hom
    let b := Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A j))))
    let β := Spec.map (CommRingCat.ofHom
      (overlapRestrictionRight A hA hNonempty i j).toRingHom)
    (baseChangedOverlapIso f g u v ≪≫
      asIso (overlapAffineBaseChange f g u v e)).inv ≫
      pullback.snd (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
      rightChartBaseChange f g v k b
        (basicOpenIsoSpec_complexStructure A hA hNonempty j) =
    affineRightChartBaseChange f g u v e k b
      (basicOpenIsoSpec_complexStructure A hA hNonempty j) β
      (actualBasicOpenOverlapIso_inv_right_spec A hA hNonempty i j).symm := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  exact affineOverlap_rightChart_natural _ _ _ _ _ _ _ _ _ _

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapAffineChartNaturality
