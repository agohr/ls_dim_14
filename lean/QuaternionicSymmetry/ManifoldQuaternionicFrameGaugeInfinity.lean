import QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection

/-! The actual adapted tangent gauge and its inverse are smooth to all
orders on every valid preferred chart, not merely twice differentiable. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFrameGaugeInfinity

open Manifold ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem coordinateInverse_contDiffAt_infinity (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ContDiffAt ℝ ∞ (coordinateInverse Q p) y := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hx : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
    simpa only [x, tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hframe : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.frames.fromFrame (achart E p)) x :=
    (Q.frames.smooth_from (achart E p)).contMDiffAt
      (((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet _).mem_nhds hx)
  have hsymm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  exact (hframe.comp y hsymm).contDiffAt

theorem solder_contDiffAt_infinity (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ContDiffAt ℝ ∞ (solder Q p) y := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hx : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
    simpa only [x, tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hframe : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.frames.toFrame (achart E p)) x :=
    (Q.frames.smooth_to (achart E p)).contMDiffAt
      (((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet _).mem_nhds hx)
  have hsymm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  exact ((hframe.comp y hsymm).contDiffAt).congr_of_eventuallyEq (by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact solder_eq_toFrame Q p z hz)

end
end QuaternionicSymmetry.ManifoldQuaternionicFrameGaugeInfinity
