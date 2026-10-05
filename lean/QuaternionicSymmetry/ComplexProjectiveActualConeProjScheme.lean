import QuaternionicSymmetry.ComplexProjectiveConeQuotientGrading
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! The literal `Proj` scheme of the actual homogeneous affine-cone
coordinate quotient. This is not yet identified with the analytic
projective cutout as a complex space or contact variety, nor equipped
with the torus action; those require standard-open localization and
gluing comparisons. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeProjScheme

open AlgebraicGeometry ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
noncomputable section

variable {d : ℕ}

def actualConeProj (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) : Scheme := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact Proj (quotientPiece A)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeProjScheme
