import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentChain

/-! The true differential of any fixed projective atlas chart is the
checked scalar-coordinate linear equivalence after the genuine extended
manifold chart differential. It is therefore invertible throughout its
source, not merely at a preferred center. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartDerivative

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartAsAtlas
  FourDimensionalHalfSpinProjectiveFixedChartAtlasSource
  FourDimensionalHalfSpinProjectiveFixedChartSmooth
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartPole
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem fixedChart_mfderiv_eq_comp (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i) :
    mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
      (fixedProjectiveChart Q p i) z =
      projectiveTangentModelEquiv.toContinuousLinearMap.comp
        (mfderiv productModel 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
          (extChartAt productModel (chartPole Q p i)) z) := by
  have hfun : fixedProjectiveChart Q p i =
      projectiveTangentModelEquiv ∘
        (extChartAt productModel (chartPole Q p i)) := by
    funext w
    exact fixedChart_eq_poleAtlas Q p i w
  rw [hfun]
  have hchartSmooth : ContMDiffAt productModel
      𝓘(ℝ, ℍ × (Fin 1 → ℂ)) ∞
      (extChartAt productModel (chartPole Q p i)) z := by
    apply (contMDiffOn_extChartAt (I := productModel)
      (x := chartPole Q p i)).contMDiffAt
    simpa only [extChartAt_source] using
      (isOpen_extChartAt_source (I := productModel)
        (x := chartPole Q p i)).mem_nhds
        ((fixedChartSource_eq_poleAtlas_source Q p i) ▸ hz)
  have hchart : MDifferentiableAt productModel
      𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      (extChartAt productModel (chartPole Q p i)) z :=
    hchartSmooth.mdifferentiableAt (by simp)
  have hlinSmooth : ContMDiffAt 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      𝓘(ℝ, ℍ × ℂ) ∞ projectiveTangentModelEquiv
      ((extChartAt productModel (chartPole Q p i)) z) :=
    projectiveTangentModelEquiv.contDiff.contMDiff.contMDiffAt
  have hlin : MDifferentiableAt 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      𝓘(ℝ, ℍ × ℂ) projectiveTangentModelEquiv
      ((extChartAt productModel (chartPole Q p i)) z) :=
    hlinSmooth.mdifferentiableAt (by simp)
  rw [mfderiv_comp z hlin hchart]
  simp only [mfderiv_eq_fderiv]
  rw [projectiveTangentModelEquiv.hasFDerivAt.fderiv]

theorem fixedChart_mfderiv_isInvertible (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i) :
    (mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
      (fixedProjectiveChart Q p i) z).IsInvertible := by
  rw [fixedChart_mfderiv_eq_comp Q p i z hz]
  obtain ⟨e, he⟩ := isInvertible_mfderiv_extChartAt
    ((fixedChartSource_eq_poleAtlas_source Q p i) ▸ hz)
  rw [← he]
  refine ⟨e.trans projectiveTangentModelEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartDerivative
