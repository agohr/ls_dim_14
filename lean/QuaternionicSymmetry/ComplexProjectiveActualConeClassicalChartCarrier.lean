import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointInjective
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapFractions

/-! The Proj-to-Spec localization of a classical quotient-Proj point detects
vanishing of each affine coordinate fraction exactly as expected. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalChartCarrier

open AlgebraicGeometry ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeOverlapFractions
open ComplexProjectiveActualConeClassicalPoint
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveLineProjPoint
noncomputable section

variable {d : ℕ}

theorem classical_coordinateFraction_mem_carrier_iff
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (x : A) (i j : Fin (d + 1))
    (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    let q : ProjectiveSpectrum (quotientPiece A) :=
      classicalPointToActualProjFixed A hA hNonempty x
    let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
        q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
      ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
    coordinateFraction A hA hNonempty i j ∈
      ProjIsoSpecTopComponent.ToSpec.carrier qᵢ ↔ x.1.rep j = 0 := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  let q : ProjectiveSpectrum (quotientPiece A) :=
    classicalPointToActualProjFixed A hA hNonempty x
  let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
      q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
    ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
  change HomogeneousLocalization.mk
      (⟨1, ⟨coordinateClass A j, coordinateClass_mem_degreeOne A j⟩,
        ⟨(coordinateClass A i) ^ 1,
          SetLike.pow_mem_graded 1 (coordinateClass_mem_degreeOne A i)⟩,
        ⟨1, rfl⟩⟩ : HomogeneousLocalization.NumDenSameDeg
          (quotientPiece A) (.powers (coordinateClass A i))) ∈
      ProjIsoSpecTopComponent.ToSpec.carrier qᵢ ↔ _
  rw [ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier]
  change coordinateClass A j ∈ quotientLineHomogeneousPrime A hA x.1 x.2 ↔ _
  constructor
  · intro h
    have hker : coordinateClass A j ∈ quotientLinePrime A x.1 x.2 :=
      (Ideal.toIdeal_homogeneousCore_le
        (𝒜 := quotientPiece A) (I := quotientLinePrime A x.1 x.2)) h
    have heval : quotientLineEval A x.1 x.2 (coordinateClass A j) = 0 :=
      (RingHom.mem_ker).mp hker
    simpa [coordinateClass, quotientLineEval, lineEval] using heval
  · intro hj
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      (show SetLike.IsHomogeneousElem (quotientPiece A) (coordinateClass A j) from
        ⟨1, coordinateClass_mem_degreeOne A j⟩)
    change quotientLineEval A x.1 x.2 (coordinateClass A j) = 0
    simp [coordinateClass, quotientLineEval, lineEval, hj]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalChartCarrier
