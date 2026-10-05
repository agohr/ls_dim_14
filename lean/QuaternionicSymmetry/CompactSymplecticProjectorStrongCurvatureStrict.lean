import QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureNonnegative

/-! The actual sectional-curvature numerator is strictly positive whenever
the two genuine projector tangent matrices fail to commute. The remaining
rank-one rigidity assertion is an explicit tangent-block algebra problem,
not an additional curvature or geometry premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureStrict

open Matrix Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongCurvatureNonnegative
open CompactSymplecticProjectorAmbientMetric
open ProjectorPeirceCurvatureBracket
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_leviCivita_curvature_pairing_pos_of_noncommuting
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
      (u v : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      commutator (fderiv ℝ F y u) (fderiv ℝ F y v) ≠ 0 →
      0 < chartMetric
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
        p y (LocalConnection.curvature (D.form p) y u v v) u := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D p y hy u v
  change commutator
      (fderiv ℝ (quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm) y u)
      (fderiv ℝ (quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm) y v) ≠ 0 → _
  intro hcomm
  rw [actual_leviCivita_curvature_pairing_eq_commutator_square
    hLee hDesc hImm n d e q g a hq hn D p y hy u v]
  simpa only [frobeniusCLM_apply] using frobeniusCLM_pos n _ hcomm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureStrict
