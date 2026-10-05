import QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthDerivative
import QuaternionicSymmetry.ManifoldTwistorVerticalComplex
import QuaternionicSymmetry.FourDimensionalTwistorHomogeneousFiber

/-! The actual north-affine Hopf derivative, viewed in the genuine tangent
plane of the quaternionic coefficient sphere, is anti-complex-linear for the
existing vertical twistor complex rotation. This is a certified convention
obstruction to identifying the current projective atlas with the AHS fiber
complex structure without conjugation/orientation adjustment. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthVerticalSign

open scoped Quaternion
open FourDimensionalHalfSpinHopfNorthDerivative
  FourDimensionalTwistorHomogeneousFiber
  ManifoldTwistorVerticalComplex

noncomputable section

def northTangent (w : ℂ) : verticalSubmodule north :=
  ⟨northDifferential w, by
    simp [verticalSubmodule, VerticalVector, north,
      northDifferential, dotProduct, Pi.basisFun_apply,
      Fin.sum_univ_succ]⟩

theorem northTangent_anti_complex (w : ℂ) :
    northTangent (Complex.I * w) =
      -verticalComplex north (northTangent w) := by
  apply Subtype.ext
  exact northDifferential_anti_complex w

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthVerticalSign
