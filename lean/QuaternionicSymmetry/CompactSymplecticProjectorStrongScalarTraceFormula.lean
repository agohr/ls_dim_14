import QuaternionicSymmetry.CompactSymplecticProjectorStrongCompatibleConnection
import QuaternionicSymmetry.CompactSymplecticProjectorStrongCurvatureNonnegative
import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaCurvaturePairing

/-! The intrinsic scalar contraction of the actual quaternionic-compatible
Levi-Civita connection is the finite sum of genuine projector-derivative
commutator squares in the actual orthonormal tangent frame. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarTraceFormula

open Matrix Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLeviCivitaCurvaturePairing
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongCompatibleConnection
open CompactSymplecticProjectorStrongCurvatureNonnegative
open CompactSymplecticProjectorAmbientMetric
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

theorem actual_scalar_eq_projector_commutator_squares
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
      let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
      let Da := actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let T := fun k : Fin (Module.finrank ℝ (EModel q)) =>
        fderiv ℝ F y
          (coordinateInverse Q p y (stdOrthonormalBasis ℝ (EModel q) k))
      localScalarCurvature Q Da p y hy =
        ∑ i : Fin (Module.finrank ℝ (EModel q)),
          ∑ j : Fin (Module.finrank ℝ (EModel q)),
            frobeniusPairing n (commutator (T i) (T j))
              (commutator (T i) (T j)) := by
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
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let metric := smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn
  let Da := actualCompatibleTangentConnection hLee hDesc hImm n d e q g a hq hn D
  let F := quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm
  let b := stdOrthonormalBasis ℝ (EModel q)
  let T := fun k : Fin (Module.finrank ℝ (EModel q)) =>
    fderiv ℝ F y (coordinateInverse Q p y (b k))
  have hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,EModel q) x),
      metric.inner x v w = Q.tangentMetricForm x v w := by
    intro x v w
    exact (strongQuaternionicHermitianTangent_metric_eq_projector
      hLee hDesc hImm n d e q g a hq hn x v w).symm
  change localScalarCurvature Q Da p y hy =
    ∑ i, ∑ j, frobeniusPairing n (commutator (T i) (T j))
      (commutator (T i) (T j))
  simp only [localScalarCurvature, localRicci]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let ui := coordinateInverse Q p y (b i)
  let vj := coordinateInverse Q p y (b j)
  have hpair := adaptedLeviCivita_curvature_inner_eq_chartMetric
    Q metric D hmetric p y hy vj ui (b i) (b j)
  have hcoord (k : Fin (Module.finrank ℝ (EModel q))) :
      (solderEquiv Q p y hy).symm (b k) = coordinateInverse Q p y (b k) := by
    change unsolder Q p y (b k) = coordinateInverse Q p y (b k)
    rw [unsolder_eq_fromFrame Q p y hy]
    rfl
  have hDa : Da.form p = adaptedLeviCivitaForm Q metric D p := rfl
  have hinner : inner ℝ (adaptedCurvature Q Da p y hy (b j) (b i) (b i))
      (b j) = chartMetric metric p y
        (LocalConnection.curvature (D.form p) y vj ui ui) vj := by
    change inner ℝ
      (LocalConnection.curvature (Da.form p) y
        ((solderEquiv Q p y hy).symm (b j))
        ((solderEquiv Q p y hy).symm (b i)) (b i)) (b j) = _
    rw [hDa, hcoord, hcoord]
    exact hpair
  rw [hinner]
  have hsquare := actual_leviCivita_curvature_pairing_eq_commutator_square
    hLee hDesc hImm n d e q g a hq hn D p y hy vj ui
  rw [hsquare]
  have hflip : commutator (T j) (T i) = -commutator (T i) (T j) := by
    simp only [ProjectorPeirceCurvatureBracket.commutator]
    abel
  change frobeniusPairing n (commutator (T j) (T i))
    (commutator (T j) (T i)) = _
  rw [hflip]
  simp [frobeniusPairing]

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongScalarTraceFormula
