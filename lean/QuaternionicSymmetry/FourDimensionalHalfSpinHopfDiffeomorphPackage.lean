import QuaternionicSymmetry.FourDimensionalHalfSpinHopfDiffeomorph
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Package the checked explicit local Hopf formulas as an actual
real-smooth diffeomorphism of the independent CP¹ and round S² atlases. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfDiffeomorphPackage

open scoped Manifold ContDiff
open Manifold
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfDiffeomorph
open ManifoldTwistorCoefficientSphere

noncomputable section

def projectiveHopfGeometricDiffeomorph :
    Diffeomorph (𝓘(ℝ, Fin 1 → ℂ)) (𝓡 2)
      ProjectiveSpinor geometricSphere ∞ :=
  { toEquiv := projectiveHopfGeometricHomeomorph.toEquiv
    contMDiff_toFun := projectiveHopfGeometric_forward_contMDiff
    contMDiff_invFun := projectiveHopfGeometric_inverse_contMDiff }

@[simp] theorem projectiveHopfGeometricDiffeomorph_apply
    (p : ProjectiveSpinor) :
    projectiveHopfGeometricDiffeomorph p =
      projectiveHopfGeometric p := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfDiffeomorphPackage
