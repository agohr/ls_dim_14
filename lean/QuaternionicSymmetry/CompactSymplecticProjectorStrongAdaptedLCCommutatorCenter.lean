import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicLeviCivitaParallel
import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCommutatorCenter
import QuaternionicSymmetry.CompactSymplecticProjectorCarrierConnected

/-! On the actual projector model, the gauge-transformed ordinary LC form
has the quaternionic commutator property at every preferred chart center.
Global all-chart-coordinate compatibility is a separate overlap step. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongAdaptedLCCommutatorCenter

open Filter Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicLeviCivitaParallel
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLeviCivitaCommutatorCenter
open ManifoldQuaternionicLocalGeneratorField
open GeneralLeviCivitaReflectedPlaneParallel
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_adaptedLeviCivita_commutator_center
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn))
      (x : ProjectiveCarrier n) (t : Fin 3) (u : EModel q),
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
      let J := quaternionicGenerator (Q.reduction.Q (achart (EModel q) x)) t
      (adaptedLeviCivitaForm Q
          (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
          D x y₀ u).comp J -
        J.comp (adaptedLeviCivitaForm Q
          (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
          D x y₀ u) ∈ quaternionicSpan
          (Q.reduction.Q (achart (EModel q) x)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : ConnectedSpace (ProjectiveCarrier n) := projectiveCarrier_connectedSpace n
  intro D x t u
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  let S := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent x t
  have hS : DifferentiableAt ℝ S y₀ :=
    (localChartGeneratorField_contDiffAt_center Q.toSmoothAlmostQuaternionicTangent
      x t).differentiableAt (by norm_num)
  have hQ : ∀ᶠ y in 𝓝 y₀,
      S y ∈ Q.chartSpan (achart (EModel q) x)
        ((extChartAt 𝓘(ℝ,EModel q) x).symm y) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds
      ((extChartAt 𝓘(ℝ,EModel q) x).map_source (by simp))]
      with y hy
    exact localChartGeneratorField_mem_span Q.toSmoothAlmostQuaternionicTangent
      x t y hy
  have hraw := actual_leviCivita_preserves_quaternionic_plane_at_center
    hLee hDesc hImm n d e q g a hq hn D x S hS hQ u
  exact adaptedLeviCivitaForm_commutator_center Q
    (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
    D x t u hraw

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongAdaptedLCCommutatorCenter
