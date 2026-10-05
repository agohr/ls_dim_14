import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondLocalTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative

/-! The actual full `mfderiv` of the second fixed corrected-Hopf chart
intertwines its independent local projective tensor with the genuine
sphere connection tensor after the true tangent/coefficient equivalence. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondLocalBlockTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinHopfSecondLocalTensor
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinHopfSecondVerticalDirect
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicMetric

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem fixedCorrectedHopf_secondLocalTensor_mfderiv
    (p : M) (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p 1)
    (uw : ℍ × ℂ) :
    let a := antipodalCoefficient
      (projectiveHopf (secondAffineSpinorPoint c.2))
    let H := mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf 1) c
    ((H (secondLocalActualProjectiveAHS Q D p c.1 c.2 uw)).1,
      (sphereTangentVerticalEquiv a)
        (H (secondLocalActualProjectiveAHS Q D p c.1 c.2 uw)).2) =
      localTwistorComplex Q D p c.1
        (fixedChartTarget_base Q p 1 c hc) a
        ((H uw).1,(sphereTangentVerticalEquiv a) (H uw).2) := by
  dsimp only
  have hblock (v : ℍ × ℂ) :
      mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ)) (𝓘(ℝ,ℍ).prod (𝓡 2))
        (fixedCorrectedHopf 1) c v =
        (v.1, mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 1) c.2 v.2) :=
    fixedCorrectedHopf_mfderiv Q p 1 c hc v.1 v.2
  rw [hblock, hblock]
  exact correctedHopf_secondLocalTensor_intertwining Q D p c.1
    (fixedChartTarget_base Q p 1 c hc) c.2 uw

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondLocalBlockTensor
