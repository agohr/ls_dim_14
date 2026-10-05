import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! Restrict a selected smooth atlas pointwise to prescribed open
neighborhoods. This changes the preferred chart domains but not the
underlying topological space or manifold regularity. -/

namespace QuaternionicSymmetry.ManifoldChartRefinement

open Manifold
open scoped Manifold
noncomputable section

variable {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M]

def restrictedCharts (W : M → Set M)
    (hWopen : ∀ x, IsOpen (W x)) (hWmem : ∀ x, x ∈ W x) :
    ChartedSpace H M where
  atlas := Set.range (fun x => (chartAt H x).restr (W x))
  chartAt x := (chartAt H x).restr (W x)
  mem_chart_source x := by
    rw [(chartAt H x).restr_source' (W x) (hWopen x)]
    exact ⟨mem_chart_source H x, hWmem x⟩
  chart_mem_atlas x := ⟨x, rfl⟩

theorem restrictedCharts_isManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    [IsManifold I n M]
    (W : M → Set M) (hWopen : ∀ x, IsOpen (W x))
    (hWmem : ∀ x, x ∈ W x) :
    @IsManifold ℝ _ E _ _ H _ I n M _
      (restrictedCharts (H := H) W hWopen hWmem) := by
  let oldChart (x : M) := chartAt H x
  have hOldCompat (x y : M) :
      (oldChart x).symm.trans (oldChart y) ∈ contDiffGroupoid n I :=
    HasGroupoid.compatible (chart_mem_atlas H x) (chart_mem_atlas H y)
  letI := restrictedCharts (H := H) W hWopen hWmem
  let G := contDiffGroupoid n I
  haveI hG : HasGroupoid M G := by
    refine ⟨?_⟩
    rintro c d ⟨x, rfl⟩ ⟨y, rfl⟩
    let e := oldChart x
    let f := oldChart y
    have hOld : e.symm.trans f ∈ G := hOldCompat x y
    have hV : IsOpen (e.target ∩ e.symm ⁻¹' W y) := by
      rw [← e.image_source_inter_eq']
      exact e.isOpen_image_source_inter (hWopen y)
    have hRight : e.symm.trans (f.restr (W y)) ∈ G := by
      exact G.mem_of_eqOnSource (closedUnderRestriction' hOld hV)
        (f.symm_trans_restr e (hWopen y))
    let U := e.source ∩ W x
    have hU : IsOpen U := e.open_source.inter (hWopen x)
    have hImage : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU Set.inter_subset_left
    have hLeft : (e.restr U).symm.trans (f.restr (W y)) ∈ G := by
      exact G.mem_of_eqOnSource (closedUnderRestriction' hRight hImage)
        (e.restr_symm_trans hU hImage Set.inter_subset_left)
    simpa only [U, e.restr_source_inter (W x)] using hLeft
  exact IsManifold.mk' I n M

end
end QuaternionicSymmetry.ManifoldChartRefinement
