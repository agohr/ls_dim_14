import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseScalarPositive

/-! Pointwise intrinsic scalar positivity from a concrete noncommuting pair
in the actual projector derivative range. The premise is only a first-order
matrix witness; the scalar-curvature conclusion is calculated internally
from the genuine Levi-Civita curvature trace. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarPosOfChartPair

open Matrix Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicScalarCurvature
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongCompatibleConnection
open CompactSymplecticProjectorStrongScalarTraceFormula
open CompactSymplecticProjectorAmbientMetric
open ProjectorCommutatorPositiveTrace
open ProjectorPeirceCurvatureBracket
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_scalar_pos_of_chart_noncommuting_pair
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
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      (∃ u v : EModel q,
        commutator (fderiv ℝ F y u) (fderiv ℝ F y v) ≠ 0) →
      0 < localScalarCurvature
        (strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn)
        (actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D)
        p y hy := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  letI : ConnectedSpace (ProjectiveCarrier n) :=
    CompactSymplecticProjectorCarrierConnected.projectiveCarrier_connectedSpace n
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  intro D p y hy
  dsimp only
  rintro ⟨u, v, hcomm⟩
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let Da := actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D
  let F := quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm
  let Tlin : EModel q →ₗ[ℝ] Mat n :=
    (fderiv ℝ F y).toLinearMap.comp (coordinateInverse Q p y).toLinearMap
  have hinv (w : EModel q) :
      coordinateInverse Q p y (solder Q p y w) = w := by
    have h := congrArg (fun A : EModel q →L[ℝ] EModel q => A w)
      (coordinateInverse_left Q p y hy)
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using h
  have hT (w : EModel q) : Tlin (solder Q p y w) = fderiv ℝ F y w := by
    simp only [Tlin, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hinv]
  have hnonzero : ∃ U V : EModel q, commutator (Tlin U) (Tlin V) ≠ 0 := by
    exact ⟨solder Q p y u, solder Q p y v, by simpa only [hT] using hcomm⟩
  have hsum := commutator_square_double_sum_pos n Tlin
    (stdOrthonormalBasis ℝ (EModel q)).toBasis hnonzero
  have hscalar := actual_scalar_eq_projector_commutator_squares
    hLee hDesc hImm n d e q g a hq hn D p y hy
  change 0 < localScalarCurvature Q Da p y hy
  rw [hscalar]
  simpa only [Tlin, LinearMap.comp_apply] using hsum

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarPosOfChartPair
