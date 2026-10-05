import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPointwiseOverlap

/-! The differential of an actual fixed chart at a total-space point obeys
the genuine manifold chain rule through the literal fixed-chart transition.
This is stronger than pointwise covariance of an explicitly written core map. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentChain

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartSmooth
  FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth
  FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveScalarFiber

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem fixedChart_transition_smoothAt_actual
    (p q : M) (i j : Fin 2) (z : SpinorBundleTotal Q)
    (hp : z ∈ fixedChartSource Q p i)
    (hq : z ∈ fixedChartSource Q q j) :
    ContMDiffAt 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) ∞
      (fun t : ℍ × ℂ => fixedProjectiveChart Q q j
        (fixedProjectiveChartInv Q p i t))
      (fixedProjectiveChart Q p i z) := by
  have hpoint : fixedProjectiveChartInv Q p i
      (fixedProjectiveChart Q p i z) = z := by
    have hp0 : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source := by
      have hp' := ((FourDimensionalHalfSpinProjectiveCore.projectiveSpinorCore Q).mem_localTriv_source
        (achart ℍ p) z).mp hp.1
      rw [← (FourDimensionalHalfSpinProjectiveCore.projectiveSpinorCore Q).baseSet_at] at hp'
      simpa only [FourDimensionalHalfSpinProjectiveCore.projectiveSpinorCore,
        ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ, ℍ)] using hp'
    exact fixedProjectiveChartInv_left Q p i z hp0 hp.2
  have hInv := fixedProjectiveChartInv_smoothAt_actual Q p i z hp
  have hQ := fixedProjectiveChart_smoothAt Q q j z hq
  rw [← hpoint] at hQ
  exact hQ.comp (fixedProjectiveChart Q p i z) hInv

theorem fixedChart_mfderiv_transition_chain
    (p q : M) (i j : Fin 2) (z : SpinorBundleTotal Q)
    (hp : z ∈ fixedChartSource Q p i)
    (hq : z ∈ fixedChartSource Q q j) :
    let c := fixedProjectiveChart Q p i z
    let T := fun t : ℍ × ℂ => fixedProjectiveChart Q q j
      (fixedProjectiveChartInv Q p i t)
    mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
      (fixedProjectiveChart Q q j) z =
      (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T c).comp
        (mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
          (fixedProjectiveChart Q p i) z) := by
  dsimp
  have hT : MDifferentiableAt 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
      (fun t : ℍ × ℂ => fixedProjectiveChart Q q j
        (fixedProjectiveChartInv Q p i t))
      (fixedProjectiveChart Q p i z) :=
    (fixedChart_transition_smoothAt_actual Q p q i j z hp hq).mdifferentiableAt
      (by simp)
  have hP : MDifferentiableAt productModel 𝓘(ℝ, ℍ × ℂ)
      (fixedProjectiveChart Q p i) z :=
    (fixedProjectiveChart_smoothAt Q p i z hp).mdifferentiableAt (by simp)
  rw [(fixedProjectiveChart_transition_eventually_at_total Q p q i j z hp).mfderiv_eq]
  exact mfderiv_comp z hT hP

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentChain
