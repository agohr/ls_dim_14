import QuaternionicSymmetry.CompactSymplecticProjectorStrongQuaternionicPointIsometry
import QuaternionicSymmetry.ManifoldQuaternionicIsometryChartFields

/-! The actual point symmetry, expressed in one fixed strong quotient
chart, is involutive on a genuine neighborhood of its center. This local
identity permits differentiation and construction of reflected Q-fields. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongSymmetryChartInvolution

open Filter Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicIsometryChartFields
open ManifoldQuaternionicConnectionIsometrySolder
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_pointSymmetry_chart_involutive_eventually
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
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
    let F := localIsometryChartMap Q f x
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,EModel q) x x), F (F y) = y := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let F := localIsometryChartMap Q f x
  have hfix : f • x = x := by
    change pointSymmetry n x x = x
    exact pointSymmetry_fixed n x
  filter_upwards [localIsometryChart_overlap_eventually Q f x] with y hy
  let z := (extChartAt 𝓘(ℝ,EModel q) x).symm y
  have hz : z ∈ (extChartAt 𝓘(ℝ,EModel q) x).source :=
    (extChartAt 𝓘(ℝ,EModel q) x).map_target hy.1
  have hfy : f • z ∈ (extChartAt 𝓘(ℝ,EModel q) x).source := by
    simpa only [extChartAt_source, hfix, z] using hy.2.2
  have hleft : (extChartAt 𝓘(ℝ,EModel q) x).symm (F y) = f • z := by
    change (extChartAt 𝓘(ℝ,EModel q) x).symm
      (extChartAt 𝓘(ℝ,EModel q) (f • x) (f • z)) = f • z
    rw [hfix]
    exact (extChartAt 𝓘(ℝ,EModel q) x).left_inv hfy
  have hright : extChartAt 𝓘(ℝ,EModel q) x z = y :=
    (extChartAt 𝓘(ℝ,EModel q) x).right_inv hy.1
  change extChartAt 𝓘(ℝ,EModel q) (f • x)
    (f • ((extChartAt 𝓘(ℝ,EModel q) x).symm (F y))) = y
  rw [hfix, hleft]
  change extChartAt 𝓘(ℝ,EModel q) x
    (pointSymmetry n x (pointSymmetry n x z)) = y
  rw [pointSymmetry_involutive n x z]
  exact hright

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongSymmetryChartInvolution
