import QuaternionicSymmetry.ComplexProjectiveDiagonalChartFamilyCounit
import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCoaction

/-! The actual homogeneous standard-open regular coaction satisfies the
counit law after transport through the proved chart/base-change ring
equivalences. A later pure-tensor formula identifies this transported
specialization with evaluation of the torus coordinate ring at one. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCounit

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveDiagonalChartIdealDescent
open ComplexProjectiveDiagonalChartQuotientFamily
open ComplexProjectiveDiagonalChartFamilySpecialization
open ComplexProjectiveDiagonalChartFamilyCounit
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeStandardOpenEquiv
open ComplexProjectiveActualConeBaseChangedChartRing
open ComplexProjectiveActualConeStandardOpenCoaction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def specializeStandardOpen (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) (z : ComplexTorus r) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (TorusCoordinateRing r ⊗[ℂ]
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)) →+*
      HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  exact (standardOpenEquiv A hA hNonempty i).symm.toRingHom.comp
    ((specializeChartQuotient A i z).comp
      (baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).toRingHom)

set_option maxRecDepth 2048 in
theorem standardOpenCoaction_counit
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
    (specializeStandardOpen (r := r) A hA hNonempty i 1).comp
      (standardOpenCoaction μ A hA hNonempty hCompact i) =
    RingHom.id (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away (quotientPiece A)
      (coordinateClass A i)) := awayComplexAlgebra A hA hNonempty _
  apply RingHom.ext
  intro x
  change (standardOpenEquiv A hA hNonempty i).symm
    (specializeChartQuotient A i 1
      ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i)
        ((baseChangedStandardOpenFamilyEquiv (r := r) A hA hNonempty i).symm
          (chartQuotientFamilyHom μ A hA hCompact i
            (standardOpenEquiv A hA hNonempty i x))))) = x
  rw [RingEquiv.apply_symm_apply]
  have h := congrArg (fun f : _ →+* _ => f (standardOpenEquiv A hA hNonempty i x))
    (chartFamily_counit μ A hA hCompact i)
  simpa only [RingHom.comp_apply, RingHom.id_apply, RingEquiv.symm_apply_apply] using
    congrArg (fun y => (standardOpenEquiv A hA hNonempty i).symm y) h

end
end QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenCounit
