import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalMultiplicationScheme

/-! The actual global torus-factor multiplication restricts on every
double-product coordinate chart to the checked affine tensor-comultiplication
Scheme map. The comparison is by both categorical pullback projections. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleMultiplicationRestriction

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
open ComplexProjectiveActualConeDoubleLocalMultiplication
open ComplexProjectiveActualConeDoubleLocalMultiplicationScheme
open ComplexProjectiveActualConeDoubleProductMultiplication
open CategoryPullbackProductOverlapIso
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem actualConeDoubleProductMultiplication_restrict
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰₂ := actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty
    let 𝒰₁ := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    𝒰₂.f i ≫ actualConeDoubleProductMultiplication r A hA hNonempty =
      directBasicOpenDoubleMultiplication (r := r) A hA hNonempty i ≫ 𝒰₁.f i := by
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
  have hMf : actualConeDoubleProductMultiplication r A hA hNonempty ≫
      pullback.fst f₁ g = pullback.fst f₂ g ≫ doubleTorusMultiplicationSpec r := by
    unfold actualConeDoubleProductMultiplication
    rw [pullback.lift_fst]
  have hMs : actualConeDoubleProductMultiplication r A hA hNonempty ≫
      pullback.snd f₁ g = pullback.snd f₂ g := by
    exact actualConeDoubleProductMultiplication_snd r A hA hNonempty
  apply pullback.hom_ext
  · calc
      (𝒰₂.f i ≫ actualConeDoubleProductMultiplication r A hA hNonempty) ≫
          pullback.fst f₁ g =
        (𝒰₂.f i ≫ pullback.fst f₂ g) ≫
          doubleTorusMultiplicationSpec r := by
            simpa only [Category.assoc] using
              congrArg (fun q => 𝒰₂.f i ≫ q) hMf
      _ = pullback.fst f₂ (u ≫ g) ≫ doubleTorusMultiplicationSpec r := by
        rw [h₂f]
      _ = directBasicOpenDoubleMultiplication (r := r) A hA hNonempty i ≫
          pullback.fst f₁ (u ≫ g) :=
        (directBasicOpenDoubleMultiplication_fst (r := r) A hA hNonempty i).symm
      _ = (directBasicOpenDoubleMultiplication (r := r) A hA hNonempty i ≫
          𝒰₁.f i) ≫ pullback.fst f₁ g := by
        simp only [Category.assoc, h₁f]
  · calc
      (𝒰₂.f i ≫ actualConeDoubleProductMultiplication r A hA hNonempty) ≫
          pullback.snd f₁ g =
        𝒰₂.f i ≫ pullback.snd f₂ g := by
          simpa only [Category.assoc] using
            congrArg (fun q => 𝒰₂.f i ≫ q) hMs
      _ = pullback.snd f₂ (u ≫ g) ≫ u := h₂s
      _ = (directBasicOpenDoubleMultiplication (r := r) A hA hNonempty i ≫
          pullback.snd f₁ (u ≫ g)) ≫ u := by
        rw [directBasicOpenDoubleMultiplication_snd]
      _ = (directBasicOpenDoubleMultiplication (r := r) A hA hNonempty i ≫
          𝒰₁.f i) ≫ pullback.snd f₁ g := by
        simp only [Category.assoc, h₁s]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleMultiplicationRestriction
