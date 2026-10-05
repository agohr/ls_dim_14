import QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedQuaternionicSpan
import QuaternionicSymmetry.GeneralLeviCivitaCovariantFieldAddition

/-! At every actual projector point, each displayed Q-generator has a
local Q-plane section through twice that generator with zero ordinary
Levi-Civita covariant first jet. This is the source-free point-symmetry
parallelism mechanism; no Q-compatible connection is assumed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongParallelQuaternionicFrameJet

open Filter Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongReflectedQuaternionicField
open CompactSymplecticProjectorStrongReflectedQuaternionicSpan
open CompactSymplecticProjectorStrongQuaternionicCovariantCancellation
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicLocalGeneratorField
open GeneralSmoothReflectedEndomorphismField
open GeneralLeviCivitaReflectionEndomorphismCancellation
open GeneralLeviCivitaCovariantFieldAddition
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_parallelQuaternionicFrameJet
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
      (x : ProjectiveCarrier n) (t : Fin 3),
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
      let F := localIsometryChartMap Q f x
      let A := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent x t
      let B := reflectedField F A
      let C := fun y => A y + B y
      let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
      DifferentiableAt ℝ C y₀ ∧
        C y₀ = A y₀ + A y₀ ∧
        (∀ᶠ y in 𝓝 y₀,
          C y ∈ Q.chartSpan (achart (EModel q) x)
            ((extChartAt 𝓘(ℝ,EModel q) x).symm y)) ∧
        ∀ u v : EModel q,
          covariantEndomorphismJet (D.form x y₀) C y₀ u v = 0 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D x t
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let F := localIsometryChartMap Q f x
  let A := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent x t
  let B := reflectedField F A
  let C := fun y => A y + B y
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  have hpacket := actual_reflectedGenerator_smooth_and_intertwines
    hLee hDesc hImm n d e q g a hq hn x t
  have hA : DifferentiableAt ℝ A y₀ :=
    (localChartGeneratorField_contDiffAt_center Q.toSmoothAlmostQuaternionicTangent
      x t).differentiableAt (by norm_num)
  have hB : DifferentiableAt ℝ B y₀ := hpacket.1
  refine ⟨hA.add hB, ?_, ?_, ?_⟩
  · change A y₀ + B y₀ = A y₀ + A y₀
    have hBA : B y₀ = A y₀ := hpacket.2.1
    rw [hBA]
  · have hAspan : ∀ᶠ y in 𝓝 y₀,
        A y ∈ Q.chartSpan (achart (EModel q) x)
          ((extChartAt 𝓘(ℝ,EModel q) x).symm y) := by
      filter_upwards [(isOpen_extChartAt_target x).mem_nhds
        ((extChartAt 𝓘(ℝ,EModel q) x).map_source (by simp))]
        with y hy
      exact localChartGeneratorField_mem_span Q.toSmoothAlmostQuaternionicTangent
        x t y hy
    filter_upwards [hAspan,
      actual_reflectedGenerator_mem_chartSpan_eventually
        hLee hDesc hImm n d e q g a hq hn x t]
      with y hAy hBy
    exact Submodule.add_mem _ hAy hBy
  · intro u v
    rw [covariantEndomorphismJet_add _ A B y₀ u v hA hB]
    exact actual_localGenerator_reflected_covariant_jets_cancel
      hLee hDesc hImm n d e q g a hq hn D x t u v

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongParallelQuaternionicFrameJet
