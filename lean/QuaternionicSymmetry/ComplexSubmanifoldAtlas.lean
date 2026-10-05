import QuaternionicSymmetry.ComplexSubmanifoldChart

/-! Gluing the constructed holomorphic graph charts, with compatibility
with the supplied real atlas. -/
namespace QuaternionicSymmetry.ComplexSubmanifoldAtlas
open ComplexSubmanifoldChart
open scoped Manifold ContDiff Topology
open Set
noncomputable section

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N B : Type} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℝ,E) ∞ N]
  [TopologicalSpace B] [ChartedSpace F B]
  [IsManifold 𝓘(ℝ,F) ∞ B] [IsManifold 𝓘(ℂ,F) ∞ B]
  {ι : N → B} {m : ℕ}
  (C : N → AdaptedChart (E := E) (F := F) ι m)
  (hC : ∀ x, x ∈ (C x).chart.source)

def charts : ChartedSpace (EuclideanSpace ℂ (Fin m)) N where
  atlas := Set.range (fun x => (C x).chart)
  chartAt x := (C x).chart
  mem_chart_source := hC
  chart_mem_atlas x := ⟨x,rfl⟩

theorem realManifold : letI := charts C hC
    IsManifold 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) ∞ N := by
  letI := charts C hC
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using
    ((C y).smooth_to.comp ((C x).smooth_inv.mono Set.inter_subset_left)
      (fun z hz => hz.2)).contDiffOn

theorem complexManifold : letI := charts C hC
    IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin m)) ∞ N := by
  letI := charts C hC
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩
  let U := ((C x).chart.symm.trans (C y).chart).source
  have hc : ContMDiffOn 𝓘(ℂ,EuclideanSpace ℂ (Fin m)) 𝓘(ℂ,F) ∞
      (chartAt F (C y).point ∘ ι ∘ (C x).chart.symm) U :=
    contMDiffOn_chart.comp ((C x).holomorphic_inv.mono Set.inter_subset_left)
      (fun z hz => (C y).source_in_chart _ hz.2)
  have hp := (C y).projection.contDiff.contMDiff.comp_contMDiffOn hc
  have hs : ContDiffOn ℂ ∞ ((C y).chart ∘ (C x).chart.symm) U := by
    apply hp.contDiffOn.congr
    intro z hz
    exact (C y).eq_projection hz.2
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using hs

theorem smoothToReal : letI := charts C hC
    ContMDiff 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) 𝓘(ℝ,E) ∞ (id : N → N) := by
  letI := charts C hC
  intro x
  apply contMDiffAt_iff_source.mpr
  have h := ((C x).smooth_inv.contMDiffAt
    ((C x).chart.open_target.mem_nhds ((C x).chart.map_source (hC x)))).contMDiffWithinAt
      (s := Set.univ)
  simpa [extChartAt, charts, chartAt] using h

theorem smoothFromReal : letI := charts C hC
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) ∞ (id : N → N) := by
  letI := charts C hC
  intro x
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuousAt_id,?_⟩
  have h := (C x).smooth_to.contMDiffAt ((C x).chart.open_source.mem_nhds (hC x))
  simpa [extChartAt, charts, chartAt] using h

theorem inclusion_holomorphic : letI := charts C hC
    ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin m)) 𝓘(ℂ,F) ∞ ι := by
  letI := charts C hC
  intro x
  apply contMDiffAt_iff_source.mpr
  have h := ((C x).holomorphic_inv.contMDiffAt
    ((C x).chart.open_target.mem_nhds ((C x).chart.map_source (hC x)))).contMDiffWithinAt
      (s := Set.univ)
  simpa [extChartAt, charts, chartAt] using h

end
end QuaternionicSymmetry.ComplexSubmanifoldAtlas
