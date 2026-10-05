import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenTensorFormula
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenTensorFormula

/-! The transported two-torus coefficient comultiplication is literally
comultiplication on the Laurent factor and identity on each actual
homogeneous standard-open ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenComultiplicationFormula

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
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
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

theorem comultiplicationChartPolynomial_baseChanged
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    comultiplicationChartPolynomial
      (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) =
    (comultiplication t) •
      MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul]
  rw [show comultiplicationChartPolynomial (MvPolynomial.C t) =
      MvPolynomial.C (comultiplication t) by
        simp [comultiplicationChartPolynomial]]
  have hmap := congrArg (fun f : MvPolynomial (Fin d) ℂ →+*
      MvPolynomial (Fin d) (DoubleTorusCoordinateRing r) => f p)
    (comultiplicationChartPolynomial_comp_baseChange (r := r) (d := d))
  simp only [RingHom.comp_apply] at hmap
  have hmap' : comultiplicationChartPolynomial
      (MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) =
      MvPolynomial.map (algebraMap ℂ (DoubleTorusCoordinateRing r)) p := by
    simpa [chartBaseChange, doubleChartBaseChange] using hmap
  rw [hmap', MvPolynomial.C_mul']

set_option maxRecDepth 2048 in
theorem comultiplicationStandardOpen_tmul_rep
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (t : TorusCoordinateRing r) (p : MvPolynomial (Fin d) ℂ) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    comultiplicationStandardOpen (r := r) A hA hNonempty i
      (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p)) =
    (comultiplication t) ⊗ₜ[ℂ]
      (standardOpenEquiv A hA hNonempty i).symm
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  simp only [comultiplicationStandardOpen, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]
  change comultiplicationChartQuotient (r := r) A i
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
        (t ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))) =
    doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
      ((comultiplication t) ⊗ₜ[ℂ]
        (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))
  rw [baseChangedStandardOpenFamilyEquiv_tmul_rep,
    doubleBaseChangedStandardOpenFamilyEquiv_tmul_rep]
  change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (comultiplicationChartPolynomial
        (t • MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p)) = _
  rw [comultiplicationChartPolynomial_baseChanged]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenComultiplicationFormula
