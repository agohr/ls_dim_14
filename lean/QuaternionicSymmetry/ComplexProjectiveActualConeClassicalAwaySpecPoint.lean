import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalChartIsoPoint
import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSchemeClassicalPoint

/-! The canonical Mathlib `Proj.basicOpenIsoSpec` itself sends a classical
quotient-Proj point to the actual Away-ring evaluation at its analytic chart
coordinates. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalAwaySpecPoint

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveActualConeClassicalCarrierChart
open ComplexProjectiveActualConeLocalizedSchemeClassicalPoint
open ComplexProjectiveActualConeSpecEvaluationNaturality
noncomputable section

variable {d : ℕ}

theorem basicOpenIsoSpec_classicalPoint
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (x : A) (i : Fin (d + 1))
    (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    let q : ProjectiveSpectrum (quotientPiece A) :=
      classicalPointToActualProjFixed A hA hNonempty x
    let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
        q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
      ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
    (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).hom qᵢ =
      specEvaluationPoint (actualChartEvaluation A hA hNonempty i
        (projectiveChart d i x.1)
        (projectiveChart_mem_chartLocus A x i hi)) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  let q : ProjectiveSpectrum (quotientPiece A) :=
    classicalPointToActualProjFixed A hA hNonempty x
  let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
      q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
    ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
  apply PrimeSpectrum.ext
  ext a
  simp only [Proj.basicOpenIsoSpec_hom]
  have hb : ((Proj.basicOpenToSpec (quotientPiece A) (coordinateClass A i)) qᵢ).asIdeal =
      ProjIsoSpecTopComponent.ToSpec.carrier qᵢ := by
    change ((ProjectiveSpectrum.Proj.toSpec (quotientPiece A)
      (coordinateClass A i)).base qᵢ).asIdeal = _
    rw [ProjectiveSpectrum.Proj.toSpec_base_apply_eq]
    rfl
  rw [hb]
  let e := standardOpenAlgEquiv A hA hNonempty i
  have hc := classicalCarrier_eq_projectiveChartEvalKernel A hA hNonempty x i hi
  change a ∈ ProjIsoSpecTopComponent.ToSpec.carrier qᵢ ↔
    a ∈ RingHom.ker (actualChartEvaluation A hA hNonempty i
      (projectiveChart d i x.1)
      (projectiveChart_mem_chartLocus A x i hi))
  have h := congrArg (fun J => e a ∈ J) hc
  have hmem : (e a ∈ Ideal.comap e.symm.toRingHom
      (ProjIsoSpecTopComponent.ToSpec.carrier qᵢ)) ↔
      a ∈ ProjIsoSpecTopComponent.ToSpec.carrier qᵢ := by
    change e.symm (e a) ∈ ProjIsoSpecTopComponent.ToSpec.carrier qᵢ ↔
      a ∈ ProjIsoSpecTopComponent.ToSpec.carrier qᵢ
    simp
  exact hmem.symm.trans (by
    simpa [actualChartEvaluation, e] using h.to_iff)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalAwaySpecPoint
