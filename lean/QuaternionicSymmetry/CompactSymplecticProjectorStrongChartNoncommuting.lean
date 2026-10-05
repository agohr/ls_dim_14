import QuaternionicSymmetry.CompactSymplecticProjectorNoncommutingEverywhere
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartTangentRange

/-! Every genuine strong quotient chart contains two first derivatives of
the actual projector immersion whose matrices do not commute. The witness
is transported through proved atlas equivalence and the exact tangent
range theorem, never inserted as a model-geometric assumption. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongChartNoncommuting

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorTangentConstraints
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongChartTangentRange
open CompactSymplecticProjectorNoncommutingEverywhere
open ProjectorPeirceCurvatureBracket
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_chartDerivative_noncommuting_everywhere
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
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      ∃ u v : EModel q,
        ProjectorPeirceCurvatureBracket.commutator
          (fderiv ℝ F y u) (fderiv ℝ F y v) ≠ 0 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy
  let x := (extChartAt 𝓘(ℝ,EModel q) p).symm y
  have hdata : ∃ X Y : Mat n,
      Xᴴ = X ∧ Yᴴ = Y ∧
      quotientOrbitProjector n x * X + X * quotientOrbitProjector n x = X ∧
      quotientOrbitProjector n x * Y + Y * quotientOrbitProjector n x = Y ∧
      X * CompactSymplecticHaar.standardJ (n + 1) =
        CompactSymplecticHaar.standardJ (n + 1) * X.map star ∧
      Y * CompactSymplecticHaar.standardJ (n + 1) =
        CompactSymplecticHaar.standardJ (n + 1) * Y.map star ∧
      ProjectorPeirceCurvatureBracket.commutator X Y ≠ 0 := by
    letI := a.quotientCharts
    obtain ⟨v, w, hcomm⟩ :=
      actual_tangent_noncommuting_everywhere hDesc hImm n d e q g a hq hn x
    let X : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
      (quotientOrbitProjector n) x v
    let Y : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
      (quotientOrbitProjector n) x w
    exact ⟨X, Y,
      tangent_projector_selfAdjoint hDesc n d e q g a x v,
      tangent_projector_selfAdjoint hDesc n d e q g a x w,
      tangent_projector_offDiagonal hDesc n d e q g a x v,
      tangent_projector_offDiagonal hDesc n d e q g a x w,
      tangent_projector_commutes_quaternionicJ hDesc n d e q g a x v,
      tangent_projector_commutes_quaternionicJ hDesc n d e q g a x w,
      hcomm⟩
  obtain ⟨X, Y, hXself, hYself, hXpeirce, hYpeirce,
    hXquat, hYquat, hcomm⟩ := hdata
  obtain ⟨u, hu⟩ := actual_chartDerivative_covers_quaternionicHermitian_tangent
    hLee hDesc hImm n d e q g a hq hn p y hy X hXself hXpeirce hXquat
  obtain ⟨v, hv⟩ := actual_chartDerivative_covers_quaternionicHermitian_tangent
    hLee hDesc hImm n d e q g a hq hn p y hy Y hYself hYpeirce hYquat
  exact ⟨u, v, by rw [hu, hv]; exact hcomm⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongChartNoncommuting
