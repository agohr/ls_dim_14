import QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentRange
import QuaternionicSymmetry.GeneralImmersionChartDerivativeRange

/-! Exact ambient quaternionic-Hermitian Peirce tangent matrices are
derivatives of the actual projector immersion in every strong chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongChartTangentRange

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongTangentRange
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open GeneralImmersionChartDerivativeRange
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_chartDerivative_covers_quaternionicHermitian_tangent
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
    ∀ (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (X : Mat n),
      let x := (extChartAt 𝓘(ℝ,EModel q) p).symm y
      Xᴴ = X →
      quotientOrbitProjector n x * X + X * quotientOrbitProjector n x = X →
      X * CompactSymplecticHaar.standardJ (n + 1) =
        CompactSymplecticHaar.standardJ (n + 1) * X.map star →
      ∃ u : EModel q,
        fderiv ℝ (quotientOrbitProjector n ∘
          (extChartAt 𝓘(ℝ,EModel q) p).symm) y u = X := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy X
  dsimp only
  intro hSelf hPeirce hQuat
  let x := (extChartAt 𝓘(ℝ,EModel q) p).symm y
  obtain ⟨w, hw⟩ := actual_quaternionicHermitian_tangent_surjective_strong
    hLee hDesc hImm n d e q g a hq hn x X hSelf hPeirce hQuat
  obtain ⟨u, hu⟩ := chart_derivative_covers_manifold_differential
    (quotientOrbitProjector n)
    (smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn) p y hy w
  exact ⟨u, hu.trans hw⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongChartTangentRange
