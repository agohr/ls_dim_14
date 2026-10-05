import QuaternionicSymmetry.ComplexProjectiveActualConeBaseChangedChartRing
import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyTensorFormula

/-! Exact pure-tensor representative formula for the existing single-torus
comparison with an actual homogeneous standard-open ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorFormula

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartProductScheme
open ComplexProjectiveDiagonalChartFamilyTensorFormula
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem baseChangedStandardOpenFamilyEquiv_tmul_rep
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
      (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
    Ideal.Quotient.mk (extendedChartIdeal (r := r) A i)
      (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply (chartFamilyProductRingEquiv (r := r) A i).injective
  rw [chartFamilyProductRingEquiv_baseChanged]
  simp only [baseChangedStandardOpenFamilyEquiv, RingEquiv.trans_apply]
  have hcancel := (chartFamilyProductRingEquiv (r := r) A i).apply_symm_apply
      ((baseChangedStandardOpenEquiv (r := r) A hA hNonempty i).toRingEquiv
        (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p)))
  refine hcancel.trans ?_
  change baseChangedStandardOpenEquiv (r := r) A hA hNonempty i
      (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
      t ⊗ₜ[ℂ] Ideal.Quotient.mk (chartVanishingIdeal A i) p
  simp [baseChangedStandardOpenEquiv, standardOpenAlgEquiv,
    Algebra.TensorProduct.congr_apply]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorFormula
