import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartDerivative

/-! The literal actual fixed-chart transition derivative is invertible at
every genuine overlap point, by the checked full tangent chain and the
invertibility of both independently constructed atlas-chart derivatives. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTransitionDerivative

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartTangentChain
  FourDimensionalHalfSpinProjectiveFixedChartDerivative
  FourDimensionalHalfSpinProjectiveManifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem fixedChart_transition_mfderiv_isInvertible
    (p q : M) (i j : Fin 2) (z : SpinorBundleTotal Q)
    (hp : z ∈ fixedChartSource Q p i)
    (hq : z ∈ fixedChartSource Q q j) :
    (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
      (fun t : ℍ × ℂ => fixedProjectiveChart Q q j
        (fixedProjectiveChartInv Q p i t))
      (fixedProjectiveChart Q p i z)).IsInvertible := by
  let A := mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
    (fixedProjectiveChart Q p i) z
  let B := mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
    (fixedProjectiveChart Q q j) z
  let T := mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ)
    (fun t : ℍ × ℂ => fixedProjectiveChart Q q j
      (fixedProjectiveChartInv Q p i t))
    (fixedProjectiveChart Q p i z)
  have hchain : B = T.comp A :=
    fixedChart_mfderiv_transition_chain Q p q i j z hp hq
  obtain ⟨eA, heA⟩ := fixedChart_mfderiv_isInvertible Q p i z hp
  obtain ⟨eB, heB⟩ := fixedChart_mfderiv_isInvertible Q q j z hq
  refine ⟨eA.symm.trans eB, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨u, rfl⟩ := eA.surjective v
  have hv := congrArg (fun L : TangentSpace productModel z →L[ℝ] (ℍ × ℂ) => L u) hchain
  have hv' : eB u = T (eA u) := by
    simpa only [A, B, T, ← heA, ← heB,
      ContinuousLinearMap.comp_apply] using hv
  change eB (eA.symm (eA u)) = T (eA u)
  simpa only [eA.symm_apply_apply] using hv'

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTransitionDerivative
