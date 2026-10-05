import QuaternionicSymmetry.FourDimensionalHalfSpinHopfRawTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondRawTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap

/-! Both genuine affine charts of the independent projective atlas:
the corrected Hopf map's literal full derivative intertwines the
indexed projective tensor with the actual raw sphere tangent operator. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfAllRawTensor

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinHopfRawTensor
  FourDimensionalHalfSpinHopfSecondRawTensor
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveCorrectedBundleBlockDerivative
  FourDimensionalHalfSpinProjectiveCorrectedBundleChart
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  ManifoldTwistorGlobalAlmostComplex
  ManifoldQuaternionicMetric

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem fixedCorrectedHopf_allRawTensor_mfderiv
    (i : Fin 2) (p : M) (c : ℍ × ℂ)
    (hc : c ∈ fixedChartTarget Q p i) (uw : ℍ × ℂ) :
    let H := mfderiv (𝓘(ℝ,ℍ).prod 𝓘(ℝ,ℂ))
      (𝓘(ℝ,ℍ).prod (𝓡 2)) (fixedCorrectedHopf i) c
    let s := indexedCorrectedHopf i c.2
    localComplexTrivialized Q D p
      ((c.1,(H uw).1),⟨s,(H uw).2⟩) =
      ((c.1,(H (indexedLocalTensor Q D i p c.1 c.2 uw)).1),
        ⟨s,(H (indexedLocalTensor Q D i p c.1 c.2 uw)).2⟩) := by
  fin_cases i
  · simpa only [indexedLocalTensor, if_pos rfl] using
      fixedCorrectedHopf_rawTensor_mfderiv Q D p c hc uw
  · simpa only [indexedLocalTensor, if_neg (by decide : (1 : Fin 2) ≠ 0)] using
      fixedCorrectedHopf_secondRawTensor_mfderiv Q D p c hc uw

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfAllRawTensor
