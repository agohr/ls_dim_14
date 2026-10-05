import QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfIndexedVerticalComplex

/-! The corrected fiber derivative is complex-linear as a map into the
literal coefficient tangent plane, using the independent round-sphere
vertical complex tensor. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalLinearComplex

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinHopfVerticalLinear
  FourDimensionalHalfSpinHopfHorizontalVertical
  FourDimensionalHalfSpinHopfIndexedVerticalComplex
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle
  ManifoldTwistorCoefficientSphere
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

theorem correctedVerticalLinear_complex (S : QuaternionicStructure E)
    (z w : ℂ) :
    correctedVerticalLinear z (Complex.I * w) =
      verticalComplex
        (antipodalCoefficient (hopfSphere ![1,z] (by simp)))
        (correctedVerticalLinear z w) := by
  let a := antipodalCoefficient (hopfSphere ![1,z] (by simp))
  let b := indexedCorrectedHopf 0 z
  have hpoint : b = coefficientSphereHomeomorph a :=
    indexedCorrectedHopf_zero_coefficient z
  have hcomplex := indexedCorrectedHopf_zero_mfderiv_complex S z w
  rw [affineSpinorPoint_hopf] at hcomplex
  rw [correctedVerticalLinear_apply, correctedVerticalLinear_apply]
  change sphereTangentVerticalEquiv a
      (hpoint ▸ (mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
        (indexedCorrectedHopf 0) z) (Complex.I * w)) =
    verticalComplex a
      (sphereTangentVerticalEquiv a
        (hpoint ▸ (mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
          (indexedCorrectedHopf 0) z) w))
  have hcast := congrArg (fun v : TangentSpace (𝓡 2) b => hpoint ▸ v) hcomplex
  rw [hcast]
  change sphereTangentVerticalEquiv a
      (hpoint ▸ sphereVerticalComplex a
        ((mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) z) w)) =
    verticalComplex a
      (sphereTangentVerticalEquiv a
        (hpoint ▸ (mfderiv 𝓘(ℝ,ℂ) (𝓡 2)
          (indexedCorrectedHopf 0) z) w))
  cases hpoint
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfVerticalLinearComplex
