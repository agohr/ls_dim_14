import QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedSpanSection
import QuaternionicSymmetry.ManifoldQuaternionicChartProjectionSmooth
import QuaternionicSymmetry.GeneralLeviCivitaReflectedPlaneParallel
import QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaSymmetryJet

/-! The ordinary Levi-Civita connection of the actual projector metric
preserves its actual smooth quaternionic three-plane. This conclusion is
proved internally from point symmetry, not supplied by BG-R5. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicLeviCivitaParallel

open Filter Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongSymmetryChartInvolution
open CompactSymplecticProjectorStrongSymmetryChartDerivativeInverse
open CompactSymplecticProjectorStrongLeviCivitaSymmetryJet
open CompactSymplecticProjectorStrongReflectedSpanSection
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryChartFields
open ManifoldQuaternionicChartProjection
open ManifoldQuaternionicChartProjectionSmooth
open GeneralSmoothReflectedEndomorphismField
open GeneralLeviCivitaReflectionEndomorphismCancellation
open GeneralLeviCivitaReflectedPlaneParallel
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_leviCivita_preserves_quaternionic_plane_at_center
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
      (x : ProjectiveCarrier n)
      (S : EModel q → EModel q →L[ℝ] EModel q)
      (hS : DifferentiableAt ℝ S (extChartAt 𝓘(ℝ,EModel q) x x))
      (hQ : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,EModel q) x x),
        S y ∈ (strongQuaternionicHermitianTangent
          hLee hDesc hImm n d e q g a hq hn).chartSpan
          (achart (EModel q) x)
          ((extChartAt 𝓘(ℝ,EModel q) x).symm y))
      (u : EModel q),
      let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
      covariantEndomorphismMap (D.form x y₀) S y₀ u ∈
        (strongQuaternionicHermitianTangent
          hLee hDesc hImm n d e q g a hq hn).chartSpan
          (achart (EModel q) x) x := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D x S hS hQ u
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let F := localIsometryChartMap Q f x
  let B := reflectedField F S
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  let σ := (extChartAt 𝓘(ℝ,EModel q) x).symm
  let P := fun y : EModel q => chartProjection Q (achart (EModel q) x) (σ y)
  let K := Q.chartSpan (achart (EModel q) x) x
  have hfix : f • x = x := by
    change pointSymmetry n x x = x
    exact pointSymmetry_fixed n x
  have hcenter : F y₀ = y₀ := by
    change localIsometryChartMap Q f x (extChartAt 𝓘(ℝ,EModel q) x x) = y₀
    rw [ManifoldQuaternionicIsometryTotalHorizontal.localIsometryChartMap_center Q f x,
      hfix]
  have hF : ContDiffAt ℝ 2 F y₀ := localIsometryChartMap_contDiffAt_center Q f x
  have hB : DifferentiableAt ℝ B y₀ :=
    reflectedField_differentiableAt_center F S y₀ hF hcenter hS
  have hneg (v : EModel q) : fderiv ℝ F y₀ v = -v :=
    actual_pointSymmetry_chart_derivative_neg hLee hDesc hImm n d e q g a hq hn x v
  have hBA : B y₀ = S y₀ := reflectedField_eq_self_center F S y₀ hcenter hneg
  have hBq : ∀ᶠ y in 𝓝 y₀,
      B y ∈ Q.chartSpan (achart (EModel q) x) (σ y) :=
    actual_reflectedSection_mem_chartSpan_eventually
      hLee hDesc hImm n d e q g a hq hn x S hQ
  have hPdiff : DifferentiableAt ℝ P y₀ :=
    chartProjection_differentiableAt_center Q x
  have hσp : σ y₀ = x := (extChartAt 𝓘(ℝ,EModel q) x).left_inv (by simp)
  have hPrange (T : EModel q →L[ℝ] EModel q) : P y₀ T ∈ K := by
    simpa only [P, K, hσp] using
      chartProjection_mem Q (achart (EModel q) x) x T
  have hPfix : ∀ᶠ y in 𝓝 y₀, P y (S y - B y) = S y - B y := by
    filter_upwards [hQ, hBq, localIsometryChart_overlap_eventually Q f x]
      with y hSy hBy hOverlap
    have hbase : σ y ∈
        (tangentBundleCore 𝓘(ℝ,EModel q) (ProjectiveCarrier n)).baseSet
          (achart (EModel q) x) := hOverlap.2.1
    exact chartProjection_fixed Q (achart (EModel q) x) (σ y)
      hbase (S y - B y) (Submodule.sub_mem _ hSy hBy)
  have hsecond (r s : EModel q) :
      fderiv ℝ (fderiv ℝ F) y₀ r s =
        -(D.form x y₀ r s + D.form x y₀ r s) :=
    actual_pointSymmetry_second_jet_eq_christoffel
      hLee hDesc hImm n d e q g a hq hn D x r s
  have hinter : ∀ᶠ z in 𝓝 y₀, ∀ v : EModel q,
      B (F z) ((fderiv ℝ F z) v) = (fderiv ℝ F z) (S z v) :=
    reflectedField_intertwines_eventually F S y₀
      (actual_pointSymmetry_chart_involutive_eventually
        hLee hDesc hImm n d e q g a hq hn x)
      (actual_pointSymmetry_chart_derivative_inverse_eventually
        hLee hDesc hImm n d e q g a hq hn x)
  have hcancel (v : EModel q) :
      covariantEndomorphismJet (D.form x y₀) S y₀ u v +
        covariantEndomorphismJet (D.form x y₀) B y₀ u v = 0 := by
    exact reflected_covariantEndomorphismJet_neg F S B (D.form x y₀)
      y₀ u v hF hS (by simpa only [hcenter] using hB)
      (hinter.mono (fun z hz => hz v)) hcenter hneg hsecond hBA
  exact covariantEndomorphismMap_mem_of_reflected_cancellation
    (D.form x y₀) S B P K y₀ u hS hB hPdiff hBA.symm hPfix hPrange hcancel

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicLeviCivitaParallel
