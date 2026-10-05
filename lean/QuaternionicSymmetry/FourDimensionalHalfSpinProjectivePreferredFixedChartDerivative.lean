import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredChartTangent

/-! The differential of the centered fixed scalar projective chart is
exactly the checked real-linear scalar-fiber equivalence on the genuine
total-space tangent model. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartDerivative

open scoped Quaternion Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectivePreferredFixedChart
  FourDimensionalHalfSpinProjectivePreferredChartTangent
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem preferred_fixedChart_mfderiv (z : SpinorBundleTotal Q) :
    mfderiv productModel 𝓘(ℝ, ℍ × ℂ)
      (fixedProjectiveChart Q z.1 (preferredProjectiveChartIndex z.2)) z =
      projectiveTangentModelEquiv.toContinuousLinearMap := by
  have hfun : fixedProjectiveChart Q z.1
      (preferredProjectiveChartIndex z.2) =
      projectiveTangentModelEquiv ∘ (extChartAt productModel z) := by
    funext w
    exact preferred_fixedChart_eq_extChartAt Q z w
  rw [hfun]
  have hchartSmooth : ContMDiffAt productModel
      𝓘(ℝ, ℍ × (Fin 1 → ℂ)) ∞
      (extChartAt productModel z) z := contMDiffAt_extChartAt
  have hchart : MDifferentiableAt productModel
      𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      (extChartAt productModel z) z :=
    hchartSmooth.mdifferentiableAt (by simp)
  have hlinSmooth : ContMDiffAt 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      𝓘(ℝ, ℍ × ℂ) ∞
      projectiveTangentModelEquiv ((extChartAt productModel z) z) :=
    projectiveTangentModelEquiv.contDiff.contMDiff.contMDiffAt
  have hlin : MDifferentiableAt 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      𝓘(ℝ, ℍ × ℂ)
      projectiveTangentModelEquiv ((extChartAt productModel z) z) :=
    hlinSmooth.mdifferentiableAt (by simp)
  rw [mfderiv_comp z hlin hchart]
  letI : NormedAddCommGroup (ModelProd ℍ (Fin 1 → ℂ)) :=
    inferInstanceAs (NormedAddCommGroup (ℍ × (Fin 1 → ℂ)))
  letI : NormedSpace ℝ (ModelProd ℍ (Fin 1 → ℂ)) :=
    inferInstanceAs (NormedSpace ℝ (ℍ × (Fin 1 → ℂ)))
  have hcenter : mfderiv productModel 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      (extChartAt productModel z) z =
        ContinuousLinearMap.id ℝ _ := by
    simp only [mfderiv, mfld_simps]
    have hmd : MDifferentiableAt productModel 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
        ((fun p : ℍ × (Fin 1 → ℂ) => (p.1, p.2)) ∘
          (chartAt (ModelProd ℍ (Fin 1 → ℂ)) z)) z := by
      simpa only [extChartAt, mfld_simps] using hchart
    rw [if_pos hmd]
    have hset : Set.range (Prod.map (id : ℍ → ℍ)
        (id : (Fin 1 → ℂ) → (Fin 1 → ℂ))) = Set.univ := by
      ext y
      simp
    rw [hset, fderivWithin_univ]
    change fderiv ℝ
      (fun y : ℍ × (Fin 1 → ℂ) =>
        ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z)
          ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z).symm y) :
          ℍ × (Fin 1 → ℂ)))
      (((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) z) : ℍ × (Fin 1 → ℂ)) =
        ContinuousLinearMap.id ℝ (ℍ × (Fin 1 → ℂ))
    have heq : (fun y : ℍ × (Fin 1 → ℂ) =>
        ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z)
          ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z).symm y) :
          ℍ × (Fin 1 → ℂ))) =ᶠ[
        𝓝 ((chartAt (ModelProd ℍ (Fin 1 → ℂ)) z) z)] id := by
      filter_upwards [(chartAt (ModelProd ℍ (Fin 1 → ℂ)) z).open_target.mem_nhds
        (mem_chart_target _ z)] with y hy
      exact (chartAt (ModelProd ℍ (Fin 1 → ℂ)) z).right_inv hy
    rw [heq.fderiv_eq]
    apply ContinuousLinearMap.ext
    intro v
    rw [fderiv_id]
    change v = v
    rfl
  rw [hcenter]
  simp only [ContinuousLinearMap.comp_id, mfderiv_eq_fderiv]
  exact projectiveTangentModelEquiv.hasFDerivAt.fderiv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartDerivative
