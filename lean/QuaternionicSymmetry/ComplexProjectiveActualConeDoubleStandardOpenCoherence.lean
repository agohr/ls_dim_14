import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoaction

/-! Strict two-torus coaction identities on each actual homogeneous
standard-open tensor ring, transported from the checked chart quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoherence

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenCoaction
open ComplexProjectiveActualConeDoubleStandardOpenRing
open ComplexProjectiveActualConeDoubleStandardOpenCoaction
open ComplexProjectiveDiagonalDoubleChartQuotientCoaction
open ComplexProjectiveDiagonalDoubleChartQuotientMaps
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem standardOpen_comultiplication_first
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (comultiplicationStandardOpen (r := r) A hA hNonempty i).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i) =
      (firstStandardOpenTwist μ A hA hNonempty hCompact i).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro x
  change (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
      (comultiplicationChartQuotient (r := r) A i
        ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i)
          ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
            (chartQuotientFamilyHom μ A hA hCompact i
              (standardOpenEquiv A hA hNonempty i x))))) =
    (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
      (firstChartTwistQuotient μ A hA hCompact i
        ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i)
          ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
            (chartQuotientFamilyHom μ A hA hCompact i
              (standardOpenEquiv A hA hNonempty i x)))))
  rw [RingEquiv.apply_symm_apply]
  exact congrArg (fun y => (doubleBaseChangedStandardOpenFamilyEquiv
    (r := r) A hA hNonempty i).symm y)
    (congrArg (fun f : _ →+* _ => f (standardOpenEquiv A hA hNonempty i x))
      (chartFamily_comultiplication_first μ A hA hCompact i))

set_option maxRecDepth 2048 in
theorem standardOpen_comultiplication_second
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (comultiplicationStandardOpen (r := r) A hA hNonempty i).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i) =
      (secondStandardOpenTwist μ A hA hNonempty hCompact i).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro x
  change (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
      (comultiplicationChartQuotient (r := r) A i
        ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i)
          ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
            (chartQuotientFamilyHom μ A hA hCompact i
              (standardOpenEquiv A hA hNonempty i x))))) =
    (doubleBaseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
      (secondChartTwistQuotient μ A hA hCompact i
        ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i)
          ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
            (chartQuotientFamilyHom μ A hA hCompact i
              (standardOpenEquiv A hA hNonempty i x)))))
  rw [RingEquiv.apply_symm_apply]
  exact congrArg (fun y => (doubleBaseChangedStandardOpenFamilyEquiv
    (r := r) A hA hNonempty i).symm y)
    (congrArg (fun f : _ →+* _ => f (standardOpenEquiv A hA hNonempty i x))
      (chartFamily_comultiplication_second μ A hA hCompact i))

theorem standardOpen_twoParameter_coherence
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (firstStandardOpenTwist μ A hA hNonempty hCompact i).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i) =
      (secondStandardOpenTwist μ A hA hNonempty hCompact i).comp
        (standardOpenCoaction μ A hA hNonempty hCompact i) :=
  (standardOpen_comultiplication_first μ A hA hNonempty hCompact i).symm.trans
    (standardOpen_comultiplication_second μ A hA hNonempty hCompact i)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleStandardOpenCoherence
