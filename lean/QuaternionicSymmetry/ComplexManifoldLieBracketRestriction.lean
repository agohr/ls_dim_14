import QuaternionicSymmetry.ManifoldChartRelatedFields
import QuaternionicSymmetry.ComplexManifoldDerivativeScalarRestriction

/-! The real and complex manifold brackets of holomorphic vector fields
agree on the same complex atlas. The proof compares the actual chart
representatives and restricts their actual derivatives. -/

namespace QuaternionicSymmetry.ComplexManifoldLieBracketRestriction

open ManifoldChartVectorField ManifoldChartRelatedFields
  ComplexManifoldDerivativeScalarRestriction VectorField
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ,E) ∞ M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartField_real_eventually_complex (V : M → E) (x : M) :
    chartField (𝕜 := ℝ) V x =ᶠ[𝓝 (extChartAt 𝓘(ℂ,E) x x)]
      chartField (𝕜 := ℂ) V x := by
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℂ,E)) x).mem_nhds
    (mem_extChartAt_target x)] with y hy
  have hyr : y ∈ (extChartAt 𝓘(ℝ,E) x).target := hy
  rw [chartField_apply_of_mem_target (𝕜 := ℝ) V x hyr,
    chartField_apply_of_mem_target (𝕜 := ℂ) V x hy]
  have hr : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℂ,E) x)
      ((extChartAt 𝓘(ℂ,E) x).symm y) :=
    mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,E) x).map_target hyr)
  have hc : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,E) (extChartAt 𝓘(ℂ,E) x)
      ((extChartAt 𝓘(ℂ,E) x).symm y) :=
    mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using (extChartAt 𝓘(ℂ,E) x).map_target hy)
  exact congrArg (fun A : E →L[ℝ] E => A (V ((extChartAt 𝓘(ℂ,E) x).symm y)))
    (mfderiv_real_eq_complex hr hc)

theorem mlieBracket_real_eq_complex
    (V W : (y : M) → TangentSpace 𝓘(ℂ,E) y) (x : M)
    (hV : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,E).tangent
      (fun y => (V y : TangentBundle 𝓘(ℂ,E) M)) x)
    (hW : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,E).tangent
      (fun y => (W y : TangentBundle 𝓘(ℂ,E) M)) x) :
    mlieBracket 𝓘(ℝ,E) V W x = mlieBracket 𝓘(ℂ,E) V W x := by
  rw [mlieBracket_eq_chart_lieBracket (𝕜 := ℝ),
    mlieBracket_eq_chart_lieBracket (𝕜 := ℂ)]
  change lieBracket ℝ (chartField (𝕜 := ℝ) V x) (chartField (𝕜 := ℝ) W x)
      (extChartAt 𝓘(ℂ,E) x x) =
    lieBracket ℂ (chartField (𝕜 := ℂ) V x) (chartField (𝕜 := ℂ) W x)
      (extChartAt 𝓘(ℂ,E) x x)
  rw [(chartField_real_eventually_complex V x).lieBracket_vectorField_eq
    (𝕜 := ℝ) (chartField_real_eventually_complex W x)]
  unfold lieBracket
  rw [(chartField_differentiableAt hW).fderiv_restrictScalars ℝ,
    (chartField_differentiableAt hV).fderiv_restrictScalars ℝ]
  rfl

end
end QuaternionicSymmetry.ComplexManifoldLieBracketRestriction
