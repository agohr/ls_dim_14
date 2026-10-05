import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapAffineChartNaturality
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexStructure
import QuaternionicSymmetry.CategoryPullbackSpecTensorNaturality
import QuaternionicSymmetry.CategoryPullbackSecondFactorStructureTransport

/-! The actual affine overlap chart restriction, after the checked global
complex-structure equality, is the literal second-factor pullback map of
the homogeneous localization restriction. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapScalarTransport

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
open ComplexProjectiveActualConeOverlapComplexStructure
open CategoryPullbackProductOverlapIso
open CategoryPullbackProductOverlapIsoTransport
open CategoryPullbackSpecTensorNaturality
open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r d : ℕ}

theorem actual_overlap_left_scalar_transport
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
    (pullback.congrHom rfl
      (actualBasicOpenOverlap_complexStructure A hA hNonempty i j)).hom ≫
      secondFactorPullbackMap (overlapRestrictionLeft A hA hNonempty i j) =
    affineLeftChartBaseChange f g u v e k b
      (basicOpenIsoSpec_complexStructure A hA hNonempty i) β
      (actualBasicOpenOverlapIso_inv_left_spec A hA hNonempty i j).symm := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  apply pullback.hom_ext
  · simp [secondFactorPullbackMap, affineLeftChartBaseChange,
      pullback.congrHom, Category.assoc]
  · simp [secondFactorPullbackMap, affineLeftChartBaseChange,
      pullback.congrHom, Category.assoc]

theorem actual_overlap_right_scalar_transport
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
    (pullback.congrHom rfl
      (actualBasicOpenOverlap_complexStructure A hA hNonempty i j)).hom ≫
      secondFactorPullbackMap (overlapRestrictionRight A hA hNonempty i j) =
    affineRightChartBaseChange f g u v e k b
      (basicOpenIsoSpec_complexStructure A hA hNonempty j) β
      (actualBasicOpenOverlapIso_inv_right_spec A hA hNonempty i j).symm := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  apply pullback.hom_ext
  · simp [secondFactorPullbackMap, affineRightChartBaseChange,
      pullback.congrHom, Category.assoc]
  · simp [secondFactorPullbackMap, affineRightChartBaseChange,
      pullback.congrHom, Category.assoc]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapScalarTransport
