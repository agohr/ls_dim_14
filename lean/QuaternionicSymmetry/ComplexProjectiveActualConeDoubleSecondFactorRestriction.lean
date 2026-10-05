import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalSecondFactorScheme

/-! The categorical second-torus projection on the global double product
restricts to the checked local tensor-ring second-parameter map. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleSecondFactorRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductCoverMap
open ComplexProjectiveActualConeDoubleProductCover
open ComplexProjectiveActualConeDoubleProductCoverMap
open ComplexProjectiveActualConeDoubleLocalSecondFactor
open ComplexProjectiveActualConeDoubleLocalSecondFactorScheme
open ComplexProjectiveActualConeDoubleProductIteratedAction
open CategoryPullbackProductOverlapIso
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem actualConeDoubleProductSecondFactor_restrict
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰₂ := actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty
    let 𝒰₁ := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    𝒰₂.f i ≫ actualConeDoubleProductSecondFactor r A hA hNonempty =
      directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫ 𝒰₁.f i := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let g := actualConeProjToSpecComplex A hA hNonempty
  let f₂ := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (DoubleTorusCoordinateRing r)))
  let f₁ := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (TorusCoordinateRing r)))
  let u := (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
  let 𝒰₂ := actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty
  let 𝒰₁ := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  have h₂f : 𝒰₂.f i ≫ pullback.fst f₂ g = pullback.fst f₂ (u ≫ g) := by
    rw [actualConeDoubleTorusProductCover_f_eq_baseChangedOpenMap
      (r := r) A hA hNonempty i]
    rw [baseChangedOpenMap, pullback.lift_fst]
  have h₂s : 𝒰₂.f i ≫ pullback.snd f₂ g = pullback.snd f₂ (u ≫ g) ≫ u := by
    rw [actualConeDoubleTorusProductCover_f_eq_baseChangedOpenMap
      (r := r) A hA hNonempty i]
    rw [baseChangedOpenMap, pullback.lift_snd]
  have h₁f : 𝒰₁.f i ≫ pullback.fst f₁ g = pullback.fst f₁ (u ≫ g) := by
    rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap
      (r := r) A hA hNonempty i]
    rw [baseChangedOpenMap, pullback.lift_fst]
  have h₁s : 𝒰₁.f i ≫ pullback.snd f₁ g = pullback.snd f₁ (u ≫ g) ≫ u := by
    rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap
      (r := r) A hA hNonempty i]
    rw [baseChangedOpenMap, pullback.lift_snd]
  have hMf : actualConeDoubleProductSecondFactor r A hA hNonempty ≫
      pullback.fst f₁ g = pullback.fst f₂ g ≫ doubleTorusSecondSpec r := by
    unfold actualConeDoubleProductSecondFactor
    rw [pullback.lift_fst]
  have hMs : actualConeDoubleProductSecondFactor r A hA hNonempty ≫
      pullback.snd f₁ g = pullback.snd f₂ g := by
    unfold actualConeDoubleProductSecondFactor
    rw [pullback.lift_snd]
  apply pullback.hom_ext
  · calc
      (𝒰₂.f i ≫ actualConeDoubleProductSecondFactor r A hA hNonempty) ≫
          pullback.fst f₁ g =
        (𝒰₂.f i ≫ pullback.fst f₂ g) ≫
          doubleTorusSecondSpec r := by
            simpa only [Category.assoc] using
              congrArg (fun q => 𝒰₂.f i ≫ q) hMf
      _ = pullback.fst f₂ (u ≫ g) ≫ doubleTorusSecondSpec r := by
        rw [h₂f]
      _ = directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
          pullback.fst f₁ (u ≫ g) :=
        (directBasicOpenDoubleSecondFactor_fst (r := r) A hA hNonempty i).symm
      _ = (directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
          𝒰₁.f i) ≫ pullback.fst f₁ g := by
        simp only [Category.assoc, h₁f]
  · calc
      (𝒰₂.f i ≫ actualConeDoubleProductSecondFactor r A hA hNonempty) ≫
          pullback.snd f₁ g =
        𝒰₂.f i ≫ pullback.snd f₂ g := by
          simpa only [Category.assoc] using
            congrArg (fun q => 𝒰₂.f i ≫ q) hMs
      _ = pullback.snd f₂ (u ≫ g) ≫ u := h₂s
      _ = (directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
          pullback.snd f₁ (u ≫ g)) ≫ u := by
        rw [directBasicOpenDoubleSecondFactor_snd]
      _ = (directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
          𝒰₁.f i) ≫ pullback.snd f₁ g := by
        simp only [Category.assoc, h₁s]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleSecondFactorRestriction
