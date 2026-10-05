import QuaternionicSymmetry.ManifoldQuaternionicFullSphereJointLocalSmooth

/-! BG-R3 yields a jointly continuous spatial tangent family for the
genuine sphere-valued full-isometry local extension. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullSphereLocalTangent

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFullSphereJointLocalSmooth
open ManifoldJointSpatialTangentContinuousAt
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicRiemannianDistance
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open MetricIsometryCompactness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem continuousAt_fullSphereLocalSpatialTangent
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hLie :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (f₀ : QuaternionicIsometries Q) (z₀ : SphereBundleTotal Q)
    (v₀ : TangentBundle (𝓘(ℝ,E).prod (𝓡 2)) (M × geometricSphere))
    (hv : v₀.1 =
      (z₀.1,((sphereCore Q).localTriv (achart E z₀.1) z₀).2)) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContinuousAt (fun p : (M ≃ᵢ M) ×
      TangentBundle (𝓘(ℝ,E).prod (𝓡 2)) (M × geometricSphere) =>
      tangentMap (𝓘(ℝ,E).prod (𝓡 2)) (𝓘(ℝ,E).prod (𝓡 2))
        (fun q => fullSphereJointLocalAction Q hChart hManifold
          (toFullMetricIsometry Q f₀) z₀.1
          ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
            (sphereTotalMap Q f₀ z₀)).2 (p.1,q)) p.2)
      (toFullMetricIsometry Q f₀,v₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  have hF := contMDiffAt_fullSphereJointLocalAction_at_actual Q hChart
    hManifold hLie hAction f₀ z₀
  have hF' : ContMDiffAt
      (𝓘(ℝ,V).prod (𝓘(ℝ,E).prod (𝓡 2)))
      (𝓘(ℝ,E).prod (𝓡 2)) 1
      (fullSphereJointLocalAction Q hChart hManifold
        (toFullMetricIsometry Q f₀) z₀.1
        ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
          (sphereTotalMap Q f₀ z₀)).2)
      (toFullMetricIsometry Q f₀,v₀.1) := by
    rw [hv]
    exact hF.of_le (by simp)
  exact continuousAt_spatialTangentFamily hF'

end
end QuaternionicSymmetry.ManifoldQuaternionicFullSphereLocalTangent
