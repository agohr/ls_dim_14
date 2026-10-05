import QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedClassicalAction

/-! The actual homogeneous-localization family and the polynomial affine
chart family have the same specialization, under the checked chart-ring
equivalence. This is an equality of ring homomorphisms. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSpecializationTransport

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalChartFamilySpecialization
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenCounit
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem localized_specialization_transport
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (z : ComplexTorus r) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (standardOpenAlgEquiv A hA hNonempty i).toRingHom.comp
      ((specializeStandardOpen A hA hNonempty i z).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i)) =
      (specializeChartQuotient A i z).comp
        ((chartQuotientFamilyHom μ A hA hCompact i).comp
          (standardOpenAlgEquiv A hA hNonempty i).toRingHom) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  apply RingHom.ext
  intro a
  change (standardOpenAlgEquiv A hA hNonempty i)
    ((standardOpenAlgEquiv A hA hNonempty i).symm
      (specializeChartQuotient A i z
        ((ComplexProjectiveActualConeBaseChangedChartRing.baseChangedStandardOpenFamilyEquiv
          (r := r) A hA hNonempty i)
          ((ComplexProjectiveActualConeBaseChangedChartRing.baseChangedStandardOpenFamilyEquiv
            (r := r) A hA hNonempty i).symm
            (chartQuotientFamilyHom μ A hA hCompact i
              (standardOpenAlgEquiv A hA hNonempty i a)))))) = _
  simp

end
end QuaternionicSymmetry.ComplexProjectiveActualConeLocalizedSpecializationTransport
