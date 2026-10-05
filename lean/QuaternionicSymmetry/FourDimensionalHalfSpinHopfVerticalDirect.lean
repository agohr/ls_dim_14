import QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedVerticalComplex

/-! A direct coefficient-plane expression for the indexed corrected Hopf
fiber derivative, with its coefficient written as the literal projective
Hopf value before replacing the homogeneous representative. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalDirect

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorVerticalComplex

noncomputable section

def projectiveVerticalDerivative (z : ℂ) :
    ℂ →ₗ[ℝ] verticalSubmodule
      (antipodalCoefficient (projectiveHopf (affineSpinorPoint z))) :=
  (sphereTangentVerticalEquiv
    (antipodalCoefficient (projectiveHopf (affineSpinorPoint z)))).toLinearMap.comp
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z).toLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

theorem projectiveVerticalDerivative_complex
    (S : QuaternionicStructure E) (z w : ℂ) :
    projectiveVerticalDerivative z (Complex.I * w) =
      verticalComplex
        (antipodalCoefficient (projectiveHopf (affineSpinorPoint z)))
        (projectiveVerticalDerivative z w) := by
  let a := antipodalCoefficient (projectiveHopf (affineSpinorPoint z))
  change sphereTangentVerticalEquiv a
      ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z)
        (Complex.I * w)) =
    verticalComplex a
      (sphereTangentVerticalEquiv a
        ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z) w))
  have hcomplex :=
    FourDimensionalHalfSpinHopfIndexedVerticalComplex.indexedCorrectedHopf_zero_mfderiv_complex
      S z w
  simp only [smul_eq_mul] at hcomplex
  rw [hcomplex]
  change (sphereTangentVerticalEquiv a)
      ((sphereTangentVerticalEquiv a).symm
        (verticalComplex a
          ((sphereTangentVerticalEquiv a)
            ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
              (indexedCorrectedHopf 0) z) w)))) = _
  rw [LinearEquiv.apply_symm_apply]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalDirect
