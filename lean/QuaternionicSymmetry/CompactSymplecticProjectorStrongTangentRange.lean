import QuaternionicSymmetry.CompactSymplecticProjectorTangentRangeEverywhere
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeMetricTransport

/-! Exact quaternionic-Hermitian tangent range survives the proved
original→Euclidean→strong atlas change; no rank assertion is imported
as a model-geometric premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentRange

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorTangentRangeEverywhere
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanMetricTransport
open CompactSymplecticProjectorEuclideanSelfModelMetricTransport
open CompactSymplecticProjectorEuclideanModelTangentFormula
open CompactSymplecticProjectorEuclideanChartBridgeTangent
open CompactSymplecticProjectorEuclideanSelfModelPlane
open CompactSymplecticProjectorEuclideanSelfModelOrbit
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementDifferential
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_quaternionicHermitian_tangent_surjective_strong
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) (X : Mat n)
    (hSelf : Xᴴ = X)
    (hPeirce : quotientOrbitProjector n x * X + X * quotientOrbitProjector n x = X)
    (hQuat : X * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * X.map star) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∃ v : TangentSpace 𝓘(ℝ,EModel q) x,
      mfderiv 𝓘(ℝ,EModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) x v = X := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := euclideanModel_isManifold n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  letI := euclideanQuotientCharts_isManifold n d e q g a
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  obtain ⟨v, hv⟩ := actual_quaternionicHermitian_tangent_surjective
    hDesc hImm n d e q g a hq x X hSelf hPeirce hQuat
  refine ⟨euclideanModelEquiv q v, ?_⟩
  have hStrong :
      mfderiv 𝓘(ℝ,EModel q) 𝓘(ℝ,Mat n) (quotientOrbitProjector n) x =
      (letI := euclideanQuotientCharts n d e q g a
       mfderiv 𝓘(ℝ,EModel q) 𝓘(ℝ,Mat n) (quotientOrbitProjector n) x) := by
    letI := euclideanQuotientCharts n d e q g a
    exact mfderiv_restrictedCharts_eq (I := 𝓘(ℝ,EModel q))
      (J := 𝓘(ℝ,Mat n))
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
      (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
      (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
      (quotientOrbitProjector n) x
      ((smooth_quotientOrbitProjector_selfModel hDesc n d e q g a).mdifferentiableAt
        (by simp))
  have hSelfModel := quotientOrbitProjector_mfderiv_selfModelChange
    hDesc n d e q g a x
  have hEuclidean := quotientOrbitProjector_mfderiv_modelChange
    hDesc n d e q g a x
  rw [hStrong]
  rw [hEuclidean, hSelfModel] at hv
  simpa only [euclideanTangentEquiv_eq_coordinateEquiv,
    selfModelTangentEquiv_eq_refl,
    ContinuousLinearEquiv.refl_apply,
    ContinuousLinearMap.comp_apply] using hv

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTangentRange
