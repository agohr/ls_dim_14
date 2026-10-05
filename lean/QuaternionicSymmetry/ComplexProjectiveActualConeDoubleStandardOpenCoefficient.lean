import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorFormula
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenTensorFormula
import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistPolynomial

/-! The two transported chart twists have their literal, ordered Laurent
coefficient maps on the actual homogeneous standard-open tensor ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoefficient

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveDiagonalDoubleChartTwistPolynomial
open ComplexProjectiveDiagonalDoubleChartQuotientCoaction
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeDoubleStandardOpenRing
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenTensorFormula
open ComplexProjectiveActualConeDoubleStandardOpenTensorFormula
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem firstChartTwist_baseChanged
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) :
    firstChartTwist μ i (MvPolynomial.C t) =
      MvPolynomial.C (secondParameter t) := by
  simp [firstChartTwist]

theorem secondChartTwist_baseChanged
    (μ : Fin (d + 1) → Fin r → ℤ) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) :
    secondChartTwist μ i (MvPolynomial.C t) =
      MvPolynomial.C (firstParameter t) := by
  simp [secondChartTwist]

set_option maxRecDepth 2048 in
theorem firstStandardOpenTwist_tmul_one
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (t : TorusCoordinateRing r) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    firstStandardOpenTwist μ A hA hNonempty hCompact i (t ⊗ₜ[ℂ] 1) =
      (secondParameter t) ⊗ₜ[ℂ] 1 := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  simp only [firstStandardOpenTwist, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  have hone : (standardOpenEquiv A hA hNonempty i).symm
      (Ideal.Quotient.mk (chartVanishingIdeal A i) 1) = 1 := by simp
  rw [← hone]
  rw [baseChangedStandardOpenFamilyEquiv_tmul_rep,
    doubleBaseChangedStandardOpenFamilyEquiv_tmul_rep]
  change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (firstChartTwist μ i (t • MvPolynomial.map
        (algebraMap ℂ (TorusCoordinateRing r)) 1)) = _
  simp [MvPolynomial.smul_eq_C_mul, firstChartTwist_baseChanged]

set_option maxRecDepth 2048 in
theorem secondStandardOpenTwist_tmul_one
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) (t : TorusCoordinateRing r) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    secondStandardOpenTwist μ A hA hNonempty hCompact i (t ⊗ₜ[ℂ] 1) =
      (firstParameter t) ⊗ₜ[ℂ] 1 := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  simp only [secondStandardOpenTwist, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  have hone : (standardOpenEquiv A hA hNonempty i).symm
      (Ideal.Quotient.mk (chartVanishingIdeal A i) 1) = 1 := by simp
  rw [← hone]
  rw [baseChangedStandardOpenFamilyEquiv_tmul_rep,
    doubleBaseChangedStandardOpenFamilyEquiv_tmul_rep]
  change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (secondChartTwist μ i (t • MvPolynomial.map
        (algebraMap ℂ (TorusCoordinateRing r)) 1)) = _
  simp [MvPolynomial.smul_eq_C_mul, secondChartTwist_baseChanged]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoefficient
