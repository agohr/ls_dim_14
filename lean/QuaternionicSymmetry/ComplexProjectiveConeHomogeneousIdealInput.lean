import QuaternionicSymmetry.ComplexProjectiveAffineConeHomogeneousIdeal

/-! The actual affine-cone ideal is packaged as Mathlib's genuine
`HomogeneousIdeal`, so it can be used in `ProjectiveSpectrum` APIs. This
does not itself compare analytic projective points with Proj points. -/

namespace QuaternionicSymmetry.ComplexProjectiveConeHomogeneousIdealInput

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveAffineConeHomogeneousIdeal
noncomputable section

variable {d : ℕ}

local instance (d : ℕ) : GradedAlgebra
    (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  MvPolynomial.gradedAlgebra

def homogeneousConeIdeal (A : Set (Space d)) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) :=
  (vanishingIdeal A).homogeneousCore _

theorem homogeneousConeIdeal_toIdeal (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty) :
    (homogeneousConeIdeal A).toIdeal = vanishingIdeal A :=
  (vanishingIdeal_isHomogeneous A hA hNonempty).toIdeal_homogeneousCore_eq_self

end
end QuaternionicSymmetry.ComplexProjectiveConeHomogeneousIdealInput
