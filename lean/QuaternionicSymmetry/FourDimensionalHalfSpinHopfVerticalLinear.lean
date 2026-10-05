import QuaternionicSymmetry.FourDimensionalHalfSpinHopfGraphAlgebra

/-! The corrected indexed Hopf mfderiv as a real-linear map from the
actual affine projective fiber tangent into the verified coefficient
plane of the actual round sphere. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalLinear

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfIndexedHorizontal
  FourDimensionalHalfSpinHopfHorizontalVertical
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinHopfSphere
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

private theorem cast_clm_apply {a b : geometricSphere} (h : a = b)
    (L : ℂ →L[ℝ] TangentSpace (𝓡 2) a) (w : ℂ) :
    (h ▸ L) w = h ▸ L w := by
  cases h
  rfl

def correctedVerticalLinear (z : ℂ) :
    ℂ →ₗ[ℝ] verticalSubmodule
      (antipodalCoefficient (hopfSphere ![1,z] (by simp))) :=
  let a := antipodalCoefficient (hopfSphere ![1,z] (by simp))
  let hpoint : indexedCorrectedHopf 0 z = coefficientSphereHomeomorph a :=
    indexedCorrectedHopf_zero_coefficient z
  (sphereTangentVerticalEquiv a).toLinearMap.comp
    (hpoint ▸ (mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
      (indexedCorrectedHopf 0) z)).toLinearMap

theorem correctedVerticalLinear_apply (z w : ℂ) :
    correctedVerticalLinear z w =
      let hpoint := indexedCorrectedHopf_zero_coefficient z
      sphereTangentVerticalEquiv
        (antipodalCoefficient (hopfSphere ![1,z] (by simp)))
        (hpoint ▸ mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
          (indexedCorrectedHopf 0) z w) := by
  unfold correctedVerticalLinear
  simp only [LinearMap.comp_apply]
  exact congrArg (sphereTangentVerticalEquiv
    (antipodalCoefficient (hopfSphere ![1,z] (by simp))))
      (cast_clm_apply (indexedCorrectedHopf_zero_coefficient z)
        (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z) w)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalLinear
