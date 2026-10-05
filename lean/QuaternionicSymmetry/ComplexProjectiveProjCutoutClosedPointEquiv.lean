import QuaternionicSymmetry.ComplexProjectiveProjClosedPointEquiv
import QuaternionicSymmetry.ComplexProjectiveProjCutoutComparison

/-! The analytic points of a nonempty homogeneous projective cutout are
exactly the closed points of its Proj zero locus, as sets. The ambient
equivalence is not asserted to be a homeomorphism or analytification. -/

namespace QuaternionicSymmetry.ComplexProjectiveProjCutoutClosedPointEquiv

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveLineProjPoint
open ComplexProjectiveProjClosedPointEquiv
open ComplexProjectiveProjCutoutComparison
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

abbrev ClosedCutoutPoint (A : Set (Space d)) :=
  {q : ClosedProjPoint d // q.1 ∈ ProjectiveSpectrum.zeroLocus
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ)
    (vanishingIdeal A : Set (MvPolynomial (Fin (d + 1)) ℂ))}

def cutoutClosedPointEquiv (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    A ≃ ClosedCutoutPoint A :=
  Equiv.subtypeEquiv (projectiveClosedPointEquiv (d := d))
    (fun x => mem_cutout_iff_mem_proj_zeroLocus A hA hNonempty x)

end
end QuaternionicSymmetry.ComplexProjectiveProjCutoutClosedPointEquiv
