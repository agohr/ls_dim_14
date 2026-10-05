import QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedQuaternionicSpan
import QuaternionicSymmetry.ManifoldQuaternionicReflectedSpanSection

/-! The actual point reflection preserves any local Q-plane-valued
endomorphism field on a neighborhood, not just fixed generators. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedSpanSection

open Filter Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongSymmetryChartInvolution
open CompactSymplecticProjectorStrongSymmetryChartDerivativeInverse
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryChartFields
open GeneralSmoothReflectedEndomorphismField
open ManifoldQuaternionicReflectedSpanSection
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_reflectedSection_mem_chartSpan_eventually
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (S : EModel q → EModel q →L[ℝ] EModel q),
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
      let F := localIsometryChartMap Q f x
      let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
      (∀ᶠ y in 𝓝 y₀,
        S y ∈ Q.chartSpan (achart (EModel q) x)
          ((extChartAt 𝓘(ℝ,EModel q) x).symm y)) →
      (∀ᶠ y in 𝓝 y₀,
        reflectedField F S y ∈ Q.chartSpan (achart (EModel q) x)
          ((extChartAt 𝓘(ℝ,EModel q) x).symm y)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro S
  dsimp only
  intro hS
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let F := localIsometryChartMap Q f x
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  let σ := (extChartAt 𝓘(ℝ,EModel q) x).symm
  have hfix : f • x = x := by
    change pointSymmetry n x x = x
    exact pointSymmetry_fixed n x
  have hcenter : F y₀ = y₀ := by
    change localIsometryChartMap Q f x (extChartAt 𝓘(ℝ,EModel q) x x) = y₀
    rw [ManifoldQuaternionicIsometryTotalHorizontal.localIsometryChartMap_center Q f x,
      hfix]
  have hFcont : ContinuousAt F y₀ :=
    (localIsometryChartMap_contDiffAt_center Q f x).continuousAt
  have hO := localIsometryChart_overlap_eventually Q f x
  have hOF : ∀ᶠ y in 𝓝 y₀,
      F y ∈ (extChartAt 𝓘(ℝ,EModel q) x).target ∧
      σ (F y) ∈ (chartAt (EModel q) x).source ∧
      f • σ (F y) ∈ (chartAt (EModel q) (f • x)).source := by
    have hO' : ∀ᶠ z in 𝓝 (F y₀),
        z ∈ (extChartAt 𝓘(ℝ,EModel q) x).target ∧
        σ z ∈ (chartAt (EModel q) x).source ∧
        f • σ z ∈ (chartAt (EModel q) (f • x)).source := by
      simpa only [hcenter, y₀, σ] using hO
    exact hFcont.eventually hO'
  have hSF : ∀ᶠ y in 𝓝 y₀,
      S (F y) ∈ Q.chartSpan (achart (EModel q) x) (σ (F y)) := by
    have hS' : ∀ᶠ z in 𝓝 (F y₀),
        S z ∈ Q.chartSpan (achart (EModel q) x) (σ z) := by
      simpa only [hcenter, σ] using hS
    exact hFcont.eventually hS'
  filter_upwards [hO, hOF, hSF,
    actual_pointSymmetry_chart_involutive_eventually
      hLee hDesc hImm n d e q g a hq hn x,
    actual_pointSymmetry_chart_derivative_inverse_eventually
      hLee hDesc hImm n d e q g a hq hn x]
    with y hy hFy hSy hF2 hRinv
  have hreturn : f • σ (F y) = σ y := by
    have hleft : σ (F (F y)) = f • σ (F y) := by
      change (extChartAt 𝓘(ℝ,EModel q) x).symm
        (extChartAt 𝓘(ℝ,EModel q) (f • x) (f • σ (F y))) = _
      rw [hfix]
      exact (extChartAt 𝓘(ℝ,EModel q) x).left_inv
        (by simpa only [extChartAt_source, hfix] using hFy.2.2)
    change F (F y) = y at hF2
    rw [← hleft, hF2]
  have hchart : extChartAt 𝓘(ℝ,EModel q) x (σ (F y)) = F y :=
    (extChartAt 𝓘(ℝ,EModel q) x).right_inv hFy.1
  exact reflectedField_mem_chartSpan_of_chart_inverse Q f x
    (σ (F y)) S y hfix hFy.2.1
    (by simpa only [hfix] using hFy.2.2)
    hchart hreturn hSy hRinv

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongReflectedSpanSection
