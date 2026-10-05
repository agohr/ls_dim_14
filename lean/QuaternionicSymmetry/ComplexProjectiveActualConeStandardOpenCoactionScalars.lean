import QuaternionicSymmetry.ComplexProjectiveDiagonalChartQuotientFamilyScalars
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyProductScalars
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoaction

/-! The actual regular standard-open coaction preserves the one canonical
global complex-scalar map. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoactionScalars

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartProductScheme
open ComplexProjectiveDiagonalChartFamilyProductScalars
open ComplexProjectiveDiagonalChartQuotientFamilyScalars
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenCoaction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem standardOpenCoaction_scalar
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    standardOpenCoaction μ A hA hNonempty hCompact i
      (algebraMap ℂ _ c) =
      (1 : TorusCoordinateRing r) ⊗ₜ[ℂ]
        (algebraMap ℂ (HomogeneousLocalization.Away (quotientPiece A)
          (coordinateClass A i)) c) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  have hstd : ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv
      A hA hNonempty i (algebraMap ℂ _ c) =
      Ideal.Quotient.mk (chartVanishingIdeal A i) (MvPolynomial.C c) := by
    change (standardOpenAlgEquiv A hA hNonempty i) (algebraMap ℂ _ c) =
      algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) c
    exact (standardOpenAlgEquiv A hA hNonempty i).commutes c
  apply (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  have hleft : baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
      (standardOpenCoaction μ A hA hNonempty hCompact i (algebraMap ℂ _ c)) =
      Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
        (MvPolynomial.C (algebraMap ℂ (TorusCoordinateRing r) c)) := by
    simp only [standardOpenCoaction, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    rw [hstd, chartQuotientFamilyHom_C]
  rw [hleft]
  apply (chartFamilyProductRingEquiv (r := r) A i).injective
  rw [chartFamilyProductRingEquiv_C]
  simp [baseChangedStandardOpenFamilyEquiv, baseChangedStandardOpenEquiv,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoactionScalars
