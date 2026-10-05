import QuaternionicSymmetry.ManifoldQuaternionicReduction

/-! Smooth fixed-chart representatives of the three actual quaternionic
tangent generators. These provide the local Q-sections whose reflected
averages are needed in the point-symmetry parallelism argument. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicLocalGeneratorField

open Manifold ManifoldQuaternionicReduction
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothAlmostQuaternionicTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def localChartGeneratorField (p : M) (t : Fin 3) (y : E) : E →L[ℝ] E :=
  Q.chartGenerator (achart E p) t ((extChartAt 𝓘(ℝ,E) p).symm y)

theorem localChartGeneratorField_mem_span (p : M) (t : Fin 3) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localChartGeneratorField Q p t y ∈
      Q.chartSpan (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  have hx : (extChartAt 𝓘(ℝ,E) p).symm y ∈
      (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy
  exact Submodule.subset_span (Set.mem_range_self t)

theorem localChartGeneratorField_contDiffAt_center (p : M) (t : Fin 3) :
    ContDiffAt ℝ ∞ (localChartGeneratorField Q p t)
      (extChartAt 𝓘(ℝ,E) p p) := by
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hp : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hbase : p ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) :=
    (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at p
  have hσ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p).symm y₀ :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y₀ hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hA : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.chartGenerator (achart E p) t) p :=
    (Q.smooth_chartGenerator (achart E p) t).contMDiffAt
      ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet _ |>.mem_nhds hbase)
  have hA' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.chartGenerator (achart E p) t)
      ((extChartAt 𝓘(ℝ,E) p).symm y₀) := by
    simpa only [hp] using hA
  have h := hA'.comp y₀ hσ
  exact h.contDiffAt

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalGeneratorField
