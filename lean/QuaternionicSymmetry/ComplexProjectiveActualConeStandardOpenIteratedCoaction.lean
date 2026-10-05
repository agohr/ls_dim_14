import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenParameterTensor
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction
import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleChartTwistPolynomial

/-! The two actual standard-open twists on the geometric coordinate are
exactly the single coaction followed by the appropriate Laurent-parameter
inclusion. This is the local ring-level content of the two possible orders
of scheme action. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenIteratedCoaction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalAffineChartComorphism
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleChartBaseChange
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
open ComplexProjectiveDiagonalDoubleChartQuotientCoaction
open ComplexProjectiveDiagonalDoubleChartTwistPolynomial
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenRing
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveActualConeStandardOpenParameterTensor
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem firstStandardOpenTwist_coaction_coordinate
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1))
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    firstStandardOpenTwist μ A hA hNonempty hCompact i (1 ⊗ₜ[ℂ] x) =
      firstParameterStandardOpen (r := r) A hA hNonempty i
        (standardOpenCoaction μ A hA hNonempty hCompact i x) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    ((standardOpenEquiv A hA hNonempty i) x)
  have hx : x = (standardOpenEquiv A hA hNonempty i).symm
      (Ideal.Quotient.mk (chartVanishingIdeal A i) p) := by
    rw [hp]
    exact ((standardOpenEquiv A hA hNonempty i).symm_apply_apply x).symm
  rw [hx]
  apply (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  simp only [firstStandardOpenTwist, firstParameterStandardOpen,
    standardOpenCoaction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  change firstChartTwistQuotient μ A hA hCompact i
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
        (1 ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))) =
    firstChartQuotient (r := r) A i
      (chartQuotientFamilyHom μ A hA hCompact i
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p))
  rw [ComplexProjectiveActualConeStandardOpenTensorFormula.baseChangedStandardOpenFamilyEquiv_tmul_rep]
  change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (firstChartTwist μ i (1 • MvPolynomial.map
        (algebraMap ℂ (TorusCoordinateRing r)) p)) =
    Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (firstChartPolynomial (chartActionComorphism μ i p))
  simpa [chartBaseChange] using congrArg
    (Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i))
      (congrFun (congrArg (fun f : _ →+* _ => f.toFun)
        (firstChartTwist_comp_baseChange μ i)) p)

set_option maxRecDepth 2048 in
theorem secondStandardOpenTwist_coaction_coordinate
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1))
    (x : HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    secondStandardOpenTwist μ A hA hNonempty hCompact i (1 ⊗ₜ[ℂ] x) =
      secondParameterStandardOpen (r := r) A hA hNonempty i
        (standardOpenCoaction μ A hA hNonempty hCompact i x) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    ((standardOpenEquiv A hA hNonempty i) x)
  have hx : x = (standardOpenEquiv A hA hNonempty i).symm
      (Ideal.Quotient.mk (chartVanishingIdeal A i) p) := by
    rw [hp]
    exact ((standardOpenEquiv A hA hNonempty i).symm_apply_apply x).symm
  rw [hx]
  apply (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).injective
  simp only [secondStandardOpenTwist, secondParameterStandardOpen,
    standardOpenCoaction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  change secondChartTwistQuotient μ A hA hCompact i
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i
        (1 ⊗ₜ[ℂ] (standardOpenEquiv A hA hNonempty i).symm
          (Ideal.Quotient.mk (chartVanishingIdeal A i) p))) =
    secondChartQuotient (r := r) A i
      (chartQuotientFamilyHom μ A hA hCompact i
        (Ideal.Quotient.mk (chartVanishingIdeal A i) p))
  rw [ComplexProjectiveActualConeStandardOpenTensorFormula.baseChangedStandardOpenFamilyEquiv_tmul_rep]
  change Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (secondChartTwist μ i (1 • MvPolynomial.map
        (algebraMap ℂ (TorusCoordinateRing r)) p)) =
    Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i)
      (secondChartPolynomial (chartActionComorphism μ i p))
  simpa [chartBaseChange] using congrArg
    (Ideal.Quotient.mk (doubleExtendedChartIdeal (r := r) A i))
      (congrFun (congrArg (fun f : _ →+* _ => f.toFun)
        (secondChartTwist_comp_baseChange μ i)) p)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenIteratedCoaction
