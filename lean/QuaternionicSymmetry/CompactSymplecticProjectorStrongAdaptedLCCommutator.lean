import QuaternionicSymmetry.CompactSymplecticProjectorStrongAdaptedLCCommutatorCenter
import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLCSpanOverlap

/-! The actual projector Levi-Civita connection preserves its genuine
adapted quaternionic span at every coordinate of every preferred chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongAdaptedLCCommutator

open Manifold GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongAdaptedLCCommutatorCenter
open CompactSymplecticProjectorCarrierConnected
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLCSpanOverlap
open VectorBundleFrameTransitions
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_adaptedLeviCivita_commutator
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
      (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (t : Fin 3) (u : EModel q),
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let Γ := adaptedLeviCivitaForm Q
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
        D p y u
      let J := quaternionicGenerator (Q.reduction.Q (achart (EModel q) p)) t
      Γ * J - J * Γ ∈ quaternionicSpan
        (Q.reduction.Q (achart (EModel q) p)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : ConnectedSpace (ProjectiveCarrier n) := projectiveCarrier_connectedSpace n
  intro D p y hy t u
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let x : ProjectiveCarrier n := (extChartAt 𝓘(ℝ,EModel q) p).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,EModel q) x).source := by
    simp
  have hpx : y ∈ chartOverlap (I := 𝓘(ℝ,EModel q)) p x := ⟨hy, hx⟩
  have hcenter := actual_adaptedLeviCivita_commutator_center
    hLee hDesc hImm n d e q g a hq hn D
  have hcommx : ∀ (s : Fin 3) (v : EModel q),
      let Λ := adaptedLeviCivitaForm Q
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
        D x (ManifoldQuaternionicConnection.chartTransition
          (I := 𝓘(ℝ,EModel q)) p x y) v
      let J := quaternionicGenerator (Q.reduction.Q (achart (EModel q) x)) s
      Λ * J - J * Λ ∈ quaternionicSpan
        (Q.reduction.Q (achart (EModel q) x)) := by
    intro s v
    simpa only [ManifoldQuaternionicConnection.chartTransition, x] using hcenter x s v
  exact adaptedLeviCivitaForm_commutator_overlap Q
    (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
    D p x y hpx hcommx t u

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongAdaptedLCCommutator
