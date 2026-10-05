import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-! Coordinate representatives of actual tangent vector fields in a
boundaryless manifold. The chosen chart and its inverse have identity
differential at the center in the genuine tangent model. -/

namespace QuaternionicSymmetry.ManifoldChartVectorField

open VectorField
open scoped Manifold ContDiff Topology
noncomputable section

variable {𝕜 E M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem chart_mfderiv_center (x : M) :
    mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x) x =
      ContinuousLinearMap.id 𝕜 E := by
  simp only [mfderiv, mfld_simps]
  have hs : ContMDiffAt 𝓘(𝕜,E) 𝓘(𝕜,E) ∞ (extChartAt 𝓘(𝕜,E) x) x :=
    contMDiffAt_extChartAt
  have hmd : MDifferentiableAt 𝓘(𝕜,E) 𝓘(𝕜,E) (chartAt E x) x := by
    simpa only [extChartAt, mfld_simps] using hs.mdifferentiableAt (by simp)
  rw [if_pos hmd, fderivWithin_univ]
  have heq : ((chartAt E x) ∘ (chartAt E x).symm) =ᶠ[𝓝 ((chartAt E x) x)] id := by
    filter_upwards [(chartAt E x).open_target.mem_nhds (mem_chart_target E x)] with y hy
    exact (chartAt E x).right_inv hy
  rw [heq.fderiv_eq]
  simp

variable [IsManifold 𝓘(𝕜,E) ∞ M] [CompleteSpace E]

theorem chart_symm_mfderiv_center (x : M) :
    mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x).symm
      (extChartAt 𝓘(𝕜,E) x x) = ContinuousLinearMap.id 𝕜 E := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    (I := 𝓘(𝕜,E)) (x := x) (mem_extChartAt_target x)
  rw [extChartAt_to_inv (I := 𝓘(𝕜,E)) x, chart_mfderiv_center,
    show Set.range 𝓘(𝕜,E) = Set.univ by simp,
    mfderivWithin_univ] at h
  ext v
  exact congrArg (fun F : E →L[𝕜] E => F v) h

def chartField (V : (x : M) → TangentSpace 𝓘(𝕜,E) x) (x : M) : E → E :=
  mpullbackWithin 𝓘(𝕜,E) 𝓘(𝕜,E) (extChartAt 𝓘(𝕜,E) x).symm V Set.univ

theorem chartField_center (V : (x : M) → TangentSpace 𝓘(𝕜,E) x) (x : M) :
    chartField V x (extChartAt 𝓘(𝕜,E) x x) = V x := by
  simp only [chartField, mpullbackWithin_apply, mfderivWithin_univ,
    chart_symm_mfderiv_center]
  change (ContinuousLinearMap.id 𝕜 E).inverse
    (V ((extChartAt 𝓘(𝕜,E) x).symm (extChartAt 𝓘(𝕜,E) x x))) = V x
  rw [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply,
    extChartAt_to_inv]

theorem mlieBracket_eq_chart_lieBracket
    (V W : (x : M) → TangentSpace 𝓘(𝕜,E) x) (x : M) :
    mlieBracket 𝓘(𝕜,E) V W x =
      lieBracket 𝕜 (chartField V x) (chartField W x) (extChartAt 𝓘(𝕜,E) x x) := by
  simp only [mlieBracket, mlieBracketWithin_apply, chart_mfderiv_center,
    show Set.range 𝓘(𝕜,E) = Set.univ by simp, Set.preimage_univ,
    Set.inter_univ, lieBracketWithin_univ, chartField]
  change (ContinuousLinearMap.id 𝕜 E).inverse _ = _
  rw [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]

theorem chartField_differentiableAt
    {V : (x : M) → TangentSpace 𝓘(𝕜,E) x} {x : M}
    (hV : MDifferentiableAt 𝓘(𝕜,E) 𝓘(𝕜,E).tangent
      (fun y => (V y : TangentBundle 𝓘(𝕜,E) M)) x) :
    DifferentiableAt 𝕜 (chartField V x) (extChartAt 𝓘(𝕜,E) x x) := by
  have h := hV.mdifferentiableWithinAt (s := Set.univ)
    |>.differentiableWithinAt_mpullbackWithin_vectorField
  simpa only [show Set.range 𝓘(𝕜,E) = Set.univ by simp,
    Set.preimage_univ, Set.inter_univ, differentiableWithinAt_univ, chartField] using h

end
end QuaternionicSymmetry.ManifoldChartVectorField
