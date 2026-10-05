import QuaternionicSymmetry.ProjectorQuaternionicNoncommutingBaseTangent
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartTangentRange
import QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureStrict

/-! A genuine positively curved tangent two-plane at the identity coset,
for the actual Frobenius metric and ordinary Levi-Civita connection. The
plane is obtained from explicit quaternionic off-diagonal blocks via the
proved actual tangent range, not posited as model curvature data. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBasePositivePlane

open Matrix Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorTangentConstraints
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongChartTangentRange
open CompactSymplecticProjectorStrongCurvatureStrict
open ProjectorQuaternionicNoncommutingBaseTangent
open ProjectorPeirceCurvatureBracket
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_base_strong_positive_plane
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
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)),
      let p := baseCoset n
      let y := extChartAt 𝓘(ℝ,EModel q) p p
      ∃ u v : EModel q,
        0 < chartMetric
          (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn)
          p y (LocalConnection.curvature (D.form p) y u v v) u := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  obtain ⟨v₀, w₀, hcomm⟩ :=
    actual_base_tangent_noncommuting hDesc hImm n d e q g a hq hn
  let X : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
    (quotientOrbitProjector n) (baseCoset n) v₀
  let Y : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
    (quotientOrbitProjector n) (baseCoset n) w₀
  have hXself : Xᴴ = X :=
    tangent_projector_selfAdjoint hDesc n d e q g a (baseCoset n) v₀
  have hYself : Yᴴ = Y :=
    tangent_projector_selfAdjoint hDesc n d e q g a (baseCoset n) w₀
  have hXpeirce : quotientOrbitProjector n (baseCoset n) * X +
      X * quotientOrbitProjector n (baseCoset n) = X :=
    tangent_projector_offDiagonal hDesc n d e q g a (baseCoset n) v₀
  have hYpeirce : quotientOrbitProjector n (baseCoset n) * Y +
      Y * quotientOrbitProjector n (baseCoset n) = Y :=
    tangent_projector_offDiagonal hDesc n d e q g a (baseCoset n) w₀
  have hXquat : X * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * X.map star :=
    tangent_projector_commutes_quaternionicJ hDesc n d e q g a (baseCoset n) v₀
  have hYquat : Y * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * Y.map star :=
    tangent_projector_commutes_quaternionicJ hDesc n d e q g a (baseCoset n) w₀
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D
  let p := baseCoset n
  let y := extChartAt 𝓘(ℝ,EModel q) p p
  have hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target :=
    (extChartAt 𝓘(ℝ,EModel q) p).map_source (by simp)
  have hxy : (extChartAt 𝓘(ℝ,EModel q) p).symm y = p :=
    (extChartAt 𝓘(ℝ,EModel q) p).left_inv (by simp)
  obtain ⟨u, hu⟩ := actual_chartDerivative_covers_quaternionicHermitian_tangent
    hLee hDesc hImm n d e q g a hq hn p y hy X hXself
      (by simpa only [hxy] using hXpeirce) hXquat
  obtain ⟨v, hv⟩ := actual_chartDerivative_covers_quaternionicHermitian_tangent
    hLee hDesc hImm n d e q g a hq hn p y hy Y hYself
      (by simpa only [hxy] using hYpeirce) hYquat
  refine ⟨u, v, ?_⟩
  apply actual_leviCivita_curvature_pairing_pos_of_noncommuting
    hLee hDesc hImm n d e q g a hq hn D p y hy u v
  rw [hu, hv]
  exact hcomm

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBasePositivePlane
