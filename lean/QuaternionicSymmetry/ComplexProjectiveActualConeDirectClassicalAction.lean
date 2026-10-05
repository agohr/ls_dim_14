import QuaternionicSymmetry.ComplexProjectiveActualConeDirectClassicalProductPoint
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFormula

/-! The literal regular action on a finite Proj product chart agrees on
classical points with the analytic diagonal action. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDirectClassicalAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveDiagonalHolomorphic
open ComplexProjectiveDiagonalChartFormula
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDirectClassicalProductPoint
open ComplexProjectiveActualConeLocalizedSchemeClassicalPoint
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeClassicalAwaySpecPoint
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveActualConeClassicalCarrierChart
open ComplexProjectiveTorusPreservation
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem directBasicOpenProductAction_classical
    (μ : Fin (d + 1) → Fin r → ℤ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (x : A) (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (directBasicOpenProductAction μ A hA hNonempty hCompact i)
      (directClassicalProductPoint A hA hNonempty i z x hi) =
      classicalPointToActualProjFixed A hA hNonempty
        ⟨projectiveAction μ z x.1,
          mapsTo_of_compact μ A hA hCompact z x.2⟩ := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  let y : A := ⟨projectiveAction μ z x.1,
    mapsTo_of_compact μ A hA hCompact z x.2⟩
  have hi' : y.1.rep i ≠ 0 :=
    (projectiveAction_mem_affineDomain_iff μ z i x.1).2 hi
  let eᵢ := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
      q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
    ⟨classicalPointToActualProjFixed A hA hNonempty y,
      (classicalPoint_mem_basicOpen_iff A hA y i).mpr hi'⟩
  have hspec : Spec.map (CommRingCat.ofHom
      (standardOpenCoaction μ A hA hNonempty hCompact i))
      (specEvaluationPoint (actualProductEvaluation A hA hNonempty i z
        (projectiveChart d i x.1) (projectiveChart_mem_chartLocus A x i hi))) =
      eᵢ.hom qᵢ := by
    rw [actualLocalSpecAction_classical]
    have hc := (chart_projectiveAction μ z i x.1 hi).symm
    have heval : actualChartEvaluation A hA hNonempty i
        (chartDiagonal μ z i (projectiveChart d i x.1))
        (chartDiagonal_maps_chartLocus μ z A
          (mapsTo_of_compact μ A hA hCompact z) i
          (projectiveChart_mem_chartLocus A x i hi)) =
        actualChartEvaluation A hA hNonempty i
          (projectiveChart d i y.1)
          (projectiveChart_mem_chartLocus A y i hi') := by
      congr 1
    rw [heval]
    simpa [eᵢ, qᵢ, y] using
      (basicOpenIsoSpec_classicalPoint A hA hNonempty y i hi').symm
  change ((directBasicOpenProductIso (r := r) A hA hNonempty i).hom ≫
    Spec.map (CommRingCat.ofHom
      (standardOpenCoaction μ A hA hNonempty hCompact i)) ≫
    eᵢ.inv ≫ (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι)
      (directClassicalProductPoint A hA hNonempty i z x hi) = _
  simp [directClassicalProductPoint, hspec, qᵢ, y, eᵢ]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDirectClassicalAction
