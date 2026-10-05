import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSpecializationTransport
import QuaternionicSymmetry.ComplexProjectiveActualConeChartClassicalSpecialization
import QuaternionicSymmetry.ComplexProjectiveTorusPreservation

/-! The actual regular action on every function of a homogeneous standard
open agrees, after specialization and classical evaluation, with pullback by
the analytic diagonal chart action. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedClassicalFunctions

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalHolomorphic
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalChartFamilySpecialization
open ComplexProjectiveTorusPreservation
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCounit
open ComplexProjectiveActualConeLocalizedSpecializationTransport
open ComplexProjectiveActualConeChartClassicalSpecialization
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localized_classical_function_action
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (z : ComplexTorus r)
    (w : Fin d → ℂ) (hw : w ∈ chartLocus A i)
    (a : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    chartPointEval A i w hw
      (standardOpenAlgEquiv A hA hNonempty i
        (specializeStandardOpen A hA hNonempty i z
          (standardOpenCoaction μ A hA hNonempty hCompact i a))) =
    chartPointEval A i (chartDiagonal μ z i w)
      (chartDiagonal_maps_chartLocus μ z A
        (mapsTo_of_compact μ A hA hCompact z) i hw)
      (standardOpenAlgEquiv A hA hNonempty i a) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  have htransport := congrArg (fun f :
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+*
        (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) => f a)
    (localized_specialization_transport μ A hA hNonempty hCompact i z)
  simp only [RingHom.comp_apply] at htransport
  have htransport' : chartPointEval A i w hw
      (standardOpenAlgEquiv A hA hNonempty i
        (specializeStandardOpen A hA hNonempty i z
          (standardOpenCoaction μ A hA hNonempty hCompact i a))) =
      chartPointEval A i w hw
        (specializeChartQuotient A i z
          (chartQuotientFamilyHom μ A hA hCompact i
            (standardOpenAlgEquiv A hA hNonempty i a))) := by
    exact congrArg (chartPointEval A i w hw) htransport
  rw [htransport']
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    (standardOpenAlgEquiv A hA hNonempty i a)
  rw [← hp]
  exact chart_family_classical_specialization μ A hA hCompact i z w hw p

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedClassicalFunctions
