import QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapTensorRestriction

/-! Right-chart counterpart of the staged actual tensor-product overlap
restriction equality. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapTensorRestrictionRight

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeBasicOpenComplexStructure
open ComplexProjectiveActualConeBasicOpenOverlapIso
open ComplexProjectiveActualConeOverlapComplexMaps
open ComplexProjectiveActualConeOverlapComplexStructure
open ComplexProjectiveActualConeOverlapTensorMaps
open ComplexProjectiveActualConeOverlapAffineChartNaturality
open ComplexProjectiveActualConeOverlapScalarTransport
open CategoryPullbackProductOverlapIso
open CategoryPullbackProductOverlapChartNaturality
open CategoryPullbackProductOverlapIsoTransport
open CategoryPullbackSpecTensorNaturality
open ComplexProjectiveDiagonalAlgebraicCharts
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem actual_right_tensor_restriction_staged
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
    let h := basicOpenIsoSpec_complexStructure A hA hNonempty j
    let E := baseChangedOverlapIso f g u v ≪≫
      asIso (overlapAffineBaseChange f g u v e)
    let C := pullback.congrHom rfl
      (actualBasicOpenOverlap_complexStructure A hA hNonempty i j)
    let Pij := pullbackSpecIso ℂ (TorusCoordinateRing r)
      (HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j))
    let Pj := pullbackSpecIso ℂ (TorusCoordinateRing r)
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j))
    Pij.inv ≫ C.inv ≫ E.inv ≫
      pullback.snd (baseChangedOpenMap f g u) (baseChangedOpenMap f g v) ≫
      rightChartBaseChange f g v k b h ≫ Pj.hom =
    Spec.map (CommRingCat.ofHom
      (overlapTensorRestrictionRight (r := r) A hA hNonempty i j).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j)) := awayComplexAlgebra A hA hNonempty _
  let Pij := pullbackSpecIso ℂ (TorusCoordinateRing r)
    (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j))
  let Pj := pullbackSpecIso ℂ (TorusCoordinateRing r)
    (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j))
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r)))
  let g := actualConeProjToSpecComplex A hA hNonempty
  let u := (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
  let v := (Proj.basicOpen (quotientPiece A) (coordinateClass A j)).ι
  let e := actualBasicOpenCoordinateOverlapIso A hA hNonempty i j
  let C : pullback f (e.inv ≫ overlapToOriginal u v ≫ g) ≅
      pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i * coordinateClass A j))))) := pullback.congrHom rfl
    (actualBasicOpenOverlap_complexStructure A hA hNonempty i j)
  have h1 := actual_overlap_right_affine_chart_natural (r := r) A hA hNonempty i j
  have h1' := congrArg (fun q => Pij.inv ≫ C.inv ≫ q ≫ Pj.hom) h1
  simp only [Category.assoc] at h1'
  dsimp only
  rw [h1']
  rw [← actual_overlap_right_scalar_transport (r := r) A hA hNonempty i j]
  dsimp only [C]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hn := pullbackSpecIso_natural_second
    (S := TorusCoordinateRing r)
    (B := HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j))
    (B' := HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i * coordinateClass A j))
    (overlapRestrictionRight A hA hNonempty i j)
  simpa [Pij, Pj, overlapTensorRestrictionRight, Category.assoc] using
    congrArg (fun q => q ≫ (pullbackSpecIso ℂ (TorusCoordinateRing r)
      (HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j))).hom) hn

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProductOverlapTensorRestrictionRight
