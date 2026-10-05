import QuaternionicSymmetry.SmoothInverseChart

/-! Smooth boundaryless manifold charts centered at zero in the model space. -/
namespace QuaternionicSymmetry.BoundarylessCenteredChart
open Set
open scoped Manifold ContDiff
noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ M]

def extendedChart (x : M) : OpenPartialHomeomorph M E :=
  (chartAt H x).trans I.toHomeomorph.toOpenPartialHomeomorph

lemma extendedChart_source (x : M) : (extendedChart I x).source = (extChartAt I x).source := by
  simp [extendedChart,extChartAt_source]

lemma extendedChart_target (x : M) : (extendedChart I x).target = (extChartAt I x).target := by
  ext y
  simp [extendedChart,extChartAt_target,ModelWithCorners.range_eq_univ]

lemma extendedChart_smooth (x : M) :
    ContMDiffOn I 𝓘(ℝ,E) ∞ (extendedChart I x) (extendedChart I x).source := by
  have h := contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)
  simpa [extendedChart,extChartAt,OpenPartialHomeomorph.extend] using h

lemma extendedChart_symm_smooth (x : M) :
    ContMDiffOn 𝓘(ℝ,E) I ∞ (extendedChart I x).symm (extendedChart I x).target := by
  rw [extendedChart_target]
  exact contMDiffOn_extChartAt_symm x

lemma exists_centered_chart (x : M) :
    ∃ c : OpenPartialHomeomorph M E, x ∈ c.source ∧ c x = 0 ∧
      ContMDiffOn I 𝓘(ℝ,E) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,E) I ∞ c.symm c.target := by
  let e := extendedChart I x
  let t := (Homeomorph.subRight (e x)).toOpenPartialHomeomorph
  let c := e.trans t
  have hsource : c.source = e.source := by simp [c,t]
  have hto : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ t := contMDiff_id.sub contMDiff_const
  have hfrom : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ t.symm := contMDiff_id.add contMDiff_const
  refine ⟨c,?_,?_,?_,?_⟩
  · rw [hsource,extendedChart_source]
    exact mem_extChartAt_source x
  · change e x - e x = 0
    exact sub_self _
  · exact hto.comp_contMDiffOn ((extendedChart_smooth I x).mono inter_subset_left)
  · exact (extendedChart_symm_smooth I x).comp hfrom.contMDiffOn (fun y hy => hy.2)

end
end QuaternionicSymmetry.BoundarylessCenteredChart
