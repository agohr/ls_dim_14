import QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative

/-! The actual full corrected-Hopf `mfderiv`, not merely a synthetic
block map, intertwines the two independently constructed local tensors
after the true sphere-tangent/coefficient-plane identification. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalBlockTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinHopfLocalTensor
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  FourDimensionalHalfSpinHopfVerticalDirect
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

theorem fixedCorrectedHopf_localTensor_mfderiv
    (p : M) (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p 0)
    (uw : ℍ × ℂ) :
    let a := antipodalCoefficient
      (projectiveHopf (affineSpinorPoint c.2))
    let H := mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf 0) c
    ((H (localActualProjectiveAHS Q D p c.1 c.2 uw)).1,
      (sphereTangentVerticalEquiv a)
        (H (localActualProjectiveAHS Q D p c.1 c.2 uw)).2) =
      localTwistorComplex Q D p c.1
        (fixedChartTarget_base Q p 0 c hc) a
        ((H uw).1,(sphereTangentVerticalEquiv a) (H uw).2) := by
  dsimp only
  have hblock (v : ℍ × ℂ) :
      mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ)) (𝓘(ℝ,ℍ).prod (𝓡 2))
        (fixedCorrectedHopf 0) c v =
        (v.1, mfderiv 𝓘(ℝ,ℂ) (𝓡 2) (indexedCorrectedHopf 0) c.2 v.2) :=
    fixedCorrectedHopf_mfderiv Q p 0 c hc v.1 v.2
  rw [hblock, hblock]
  exact correctedHopf_localTensor_intertwining Q D p c.1
    (fixedChartTarget_base Q p 0 c hc) c.2 uw

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalBlockTensor
