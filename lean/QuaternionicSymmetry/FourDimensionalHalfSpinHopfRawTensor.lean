import QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalBlockTensor
import QuaternionicSymmetry.ManifoldTwistorLocalComplexBundleSmooth

/-! The first affine corrected Hopf differential intertwines the genuine
raw sphere tangent-bundle complex chart, not just coefficient-plane algebra. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfRawTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinHopfLocalBlockTensor
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereBundle
  ManifoldTwistorVerticalComplex
  ManifoldTwistorCorrectedHopf
  ManifoldTwistorLocalAlmostComplex
  ManifoldTwistorGlobalAlmostComplex
  ManifoldQuaternionicMetric

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem fixedCorrectedHopf_rawTensor_mfderiv
    (p : M) (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p 0)
    (uw : ℍ × ℂ) :
    let H := mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf 0) c
    let s := indexedCorrectedHopf 0 c.2
    localComplexTrivialized Q D p
      ((c.1,(H uw).1),⟨s,(H uw).2⟩) =
      ((c.1,(H (localActualProjectiveAHS Q D p c.1 c.2 uw)).1),
        ⟨s,(H (localActualProjectiveAHS Q D p c.1 c.2 uw)).2⟩) := by
  dsimp only
  let a := antipodalCoefficient (projectiveHopf (affineSpinorPoint c.2))
  have hs : indexedCorrectedHopf 0 c.2 = coefficientSphereHomeomorph a := by
    change correctedHopf
      (affineSpinorPoint c.2) = coefficientSphereHomeomorph a
    exact correctedHopf_coefficient _
  let H := mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
    (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf 0) c
  have hblock := fixedCorrectedHopf_localTensor_mfderiv Q D p c hc uw
  dsimp only at hblock
  rw [hs]
  rw [localComplexTrivialized]
  rw [localComplexBundleMap_eq_local Q D p c.1
    (fixedChartTarget_base Q p 0 c hc) a (H uw).1 (H uw).2]
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
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfRawTensor
