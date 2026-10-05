import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondLocalBlockTensor
import QuaternionicSymmetry.ManifoldTwistorLocalComplexBundleSmooth

/-! The second fixed affine corrected Hopf derivative intertwines the
independent projective tensor and the true raw sphere tangent-bundle
complex chart, including the pole omitted by the first affine chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondRawTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinHopfSecondLocalBlockTensor
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorGlobalAlmostComplex
  ManifoldTwistorCorrectedHopf
  ManifoldQuaternionicMetric

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem fixedCorrectedHopf_secondRawTensor_mfderiv
    (p : M) (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p 1)
    (uw : ℍ × ℂ) :
    let H := mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf 1) c
    let s := indexedCorrectedHopf 1 c.2
    localComplexTrivialized Q D p
      ((c.1,(H uw).1),⟨s,(H uw).2⟩) =
      ((c.1,(H (secondLocalActualProjectiveAHS Q D p c.1 c.2 uw)).1),
        ⟨s,(H (secondLocalActualProjectiveAHS Q D p c.1 c.2 uw)).2⟩) := by
  dsimp only
  let a := antipodalCoefficient (projectiveHopf (secondAffineSpinorPoint c.2))
  have hs : indexedCorrectedHopf 1 c.2 = coefficientSphereHomeomorph a := by
    change correctedHopf (secondAffineSpinorPoint c.2) = coefficientSphereHomeomorph a
    exact correctedHopf_coefficient _
  let H := mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
    (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf 1) c
  have hblock := fixedCorrectedHopf_secondLocalTensor_mfderiv Q D p c hc uw
  dsimp only at hblock
  rw [hs]
  rw [localComplexTrivialized]
  rw [localComplexBundleMap_eq_local Q D p c.1
    (fixedChartTarget_base Q p 1 c hc) a (H uw).1 (H uw).2]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact (congrArg Prod.fst hblock).symm
  · apply Bundle.TotalSpace.ext
    · rfl
    · apply heq_of_eq
      apply (sphereTangentVerticalEquiv a).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (congrArg Prod.snd hblock).symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondRawTensor
