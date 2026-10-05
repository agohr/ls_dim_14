import QuaternionicSymmetry.SubmanifoldChartDimension

/-! Gluing smooth local subset charts and proving the inclusion is an immersion. -/
namespace QuaternionicSymmetry.SubmanifoldLocalChartAtlas
open Set Filter SubspaceSubmanifoldChart
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 500000

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  {S : Set M} {k : ℕ} (C : S → LocalChart (I := I) S k)
  (hC : ∀ x, x ∈ (C x).chart.source)

def charts : ChartedSpace (EuclideanSpace ℝ (Fin k)) S where
  atlas := range (fun x => (C x).chart)
  chartAt x := (C x).chart
  mem_chart_source := hC
  chart_mem_atlas x := ⟨x,rfl⟩

lemma manifold : letI := charts C hC
    IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ S := by
  letI := charts C hC
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,preimage_id,range_id,inter_univ]
    using transition_smooth (C x) (C y)

lemma inclusion_smooth : letI := charts C hC
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I ∞ (Subtype.val : S → M) := by
  letI := charts C hC
  intro x
  apply contMDiffAt_iff_source.mpr
  have h := ((C x).inverse_smooth.contMDiffAt
    ((C x).chart.open_target.mem_nhds ((C x).chart.map_source (hC x)))).contMDiffWithinAt
      (s := univ)
  simpa [extChartAt,charts,chartAt] using h

lemma inclusion_injective_derivative : letI := charts C hC
    ∀ x : S, Function.Injective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I (Subtype.val : S → M) x) := by
  letI := charts C hC
  letI := manifold C hC
  intro x
  have hi := (inclusion_smooth C hC x).mdifferentiableAt (by simp)
  have he := ((C x).extension_smooth.contMDiffAt
    ((C x).open_ambientSource.mem_nhds ((C x).source_subset x (hC x)))).mdifferentiableAt (by simp)
  have heq : (C x).extension ∘ (Subtype.val : S → M) =ᶠ[𝓝 x] (C x).chart := by
    filter_upwards [(C x).chart.open_source.mem_nhds (hC x)] with y hy
    exact ((C x).extension_eq y hy).symm
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin k)))
    (I' := 𝓘(ℝ,EuclideanSpace ℝ (Fin k)))
  rw [mfderiv_comp x he hi] at hd
  have hchart : Function.Injective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
        (C x).chart x) :=
    (mdifferentiable_chart (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin k))) x).mfderiv_injective
      (mem_chart_source _ x)
  intro u v huv
  apply hchart
  rw [← hd]
  change mfderiv I 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (C x).extension x.1
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I Subtype.val x u) = _
  rw [huv]
  rfl

end
end QuaternionicSymmetry.SubmanifoldLocalChartAtlas
