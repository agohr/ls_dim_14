import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorFormula
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenTensorFormula

/-! The two ordered inclusions of the torus coordinate ring are exactly
tensoring the literal Laurent inclusions with the identity on each genuine
homogeneous standard-open ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenParameterTensor

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeDoubleStandardOpenRing
open ComplexProjectiveActualConeStandardOpenTensorFormula
open ComplexProjectiveActualConeDoubleStandardOpenTensorFormula
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def firstParameterStandardOpen
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) →+*
    (DoubleTorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm.toRingHom.comp
    ((firstChartQuotient (r := r) A i).comp
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).toRingHom)

def secondParameterStandardOpen
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) →+*
    (DoubleTorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm.toRingHom.comp
    ((secondChartQuotient (r := r) A i).comp
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).toRingHom)

theorem firstChartPolynomial_baseChanged
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    firstChartPolynomial
      (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) =
    (firstParameter t) •
      MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul]
  rw [show firstChartPolynomial (MvPolynomial.C t) =
      MvPolynomial.C (firstParameter t) by simp [firstChartPolynomial]]
  have hmap := congrArg (fun f : MvPolynomial (Fin d) ℂ →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) => f p)
    (firstChartPolynomial_comp_baseChange (r := r) (d := d))
  simp only [RingHom.comp_apply] at hmap
  have hmap' : firstChartPolynomial
      (MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) =
      MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p := by
    simpa [chartBaseChange, doubleChartBaseChange] using hmap
  rw [hmap', MvPolynomial.C_mul']

theorem secondChartPolynomial_baseChanged
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    secondChartPolynomial
      (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) =
    (secondParameter t) •
      MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul]
  rw [show secondChartPolynomial (MvPolynomial.C t) =
      MvPolynomial.C (secondParameter t) by simp [secondChartPolynomial]]
  have hmap := congrArg (fun f : MvPolynomial (Fin d) ℂ →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) => f p)
    (secondChartPolynomial_comp_baseChange (r := r) (d := d))
  simp only [RingHom.comp_apply] at hmap
  have hmap' : secondChartPolynomial
      (MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) =
      MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p := by
    simpa [chartBaseChange, doubleChartBaseChange] using hmap
  rw [hmap', MvPolynomial.C_mul']

set_option maxRecDepth 2048 in
theorem firstParameterStandardOpen_tmul_rep
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    firstParameterStandardOpen (r := r) A hA hNonempty i
      (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
    (firstParameter t) ⊗ₜ[ℂ]
      (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  simp only [firstParameterStandardOpen, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  change firstChartQuotient (r := r) A i
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
        (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))) =
    doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
      ((firstParameter t) ⊗ₜ[ℂ]
        (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))
  rw [baseChangedStandardOpenFamilyEquiv_tmul_rep,
    doubleBaseChangedStandardOpenFamilyEquiv_tmul_rep]
  change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (firstChartPolynomial
        (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p)) = _
  rw [firstChartPolynomial_baseChanged]

set_option maxRecDepth 2048 in
theorem secondParameterStandardOpen_tmul_rep
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    secondParameterStandardOpen (r := r) A hA hNonempty i
      (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
    (secondParameter t) ⊗ₜ[ℂ]
      (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  simp only [secondParameterStandardOpen, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  change secondChartQuotient (r := r) A i
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
        (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))) =
    doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
      ((secondParameter t) ⊗ₜ[ℂ]
        (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))
  rw [baseChangedStandardOpenFamilyEquiv_tmul_rep,
    doubleBaseChangedStandardOpenFamilyEquiv_tmul_rep]
  change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (secondChartPolynomial
        (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p)) = _
  rw [secondChartPolynomial_baseChanged]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenParameterTensor
