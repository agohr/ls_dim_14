import QuaternionicSymmetry.ManifoldQuaternionicFullSphereActualSmooth
import QuaternionicSymmetry.ManifoldJointSpatialTangentContinuousAt

/-! The genuine sphere-valued full-isometry local extension, with its
moving base, is C∞ jointly in the full BG-R3 Lie parameter and sphere chart. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullSphereJointLocalSmooth

open Manifold
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFullSphereNormalizedSmooth
open ManifoldQuaternionicFullSphereActualSmooth
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

def fullSphereJointLocalAction
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
    (g₀ : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ : M) (uTarget : geometricSphere)
    (p : (letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M) ×
      (M × geometricSphere)) : M × geometricSphere :=
  (p.1 p.2.1,
    fullNormalizedSphereAction Q hChart hManifold g₀ x₀ uTarget
      ((p.1,p.2.1),p.2.2))

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem contMDiffAt_fullSphereJointLocalAction_at_actual
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
    (f₀ : QuaternionicIsometries Q) (z₀ : SphereBundleTotal Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContMDiffAt (𝓘(ℝ,V).prod (𝓘(ℝ,E).prod (𝓡 2)))
      (𝓘(ℝ,E).prod (𝓡 2)) ∞
      (fullSphereJointLocalAction Q hChart hManifold
        (toFullMetricIsometry Q f₀) z₀.1
        ((sphereCore Q).localTriv (achart E (f₀ • z₀.1))
          (sphereTotalMap Q f₀ z₀)).2)
      (toFullMetricIsometry Q f₀,
        (z₀.1,((sphereCore Q).localTriv (achart E z₀.1) z₀).2)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  let J := 𝓘(ℝ,V).prod (𝓘(ℝ,E).prod (𝓡 2))
  let center : (M ≃ᵢ M) × (M × geometricSphere) :=
    (toFullMetricIsometry Q f₀,
      (z₀.1,((sphereCore Q).localTriv (achart E z₀.1) z₀).2))
  have hg : ContMDiffAt J 𝓘(ℝ,V) ∞
      (fun p : (M ≃ᵢ M) × (M × geometricSphere) => p.1) center :=
    contMDiffAt_fst
  have hxu : ContMDiffAt J (𝓘(ℝ,E).prod (𝓡 2)) ∞
      (fun p : (M ≃ᵢ M) × (M × geometricSphere) => p.2) center :=
    contMDiffAt_snd
  have hx : ContMDiffAt J 𝓘(ℝ,E) ∞
      (fun p : (M ≃ᵢ M) × (M × geometricSphere) => p.2.1) center :=
    ContMDiffAt.comp (f := Prod.snd) center contMDiffAt_fst hxu
  have hu : ContMDiffAt J (𝓡 2) ∞
      (fun p : (M ≃ᵢ M) × (M × geometricSphere) => p.2.2) center :=
    ContMDiffAt.comp (f := Prod.snd) center contMDiffAt_snd hxu
  have hgx : ContMDiffAt J (𝓘(ℝ,V).prod 𝓘(ℝ,E)) ∞
      (fun p : (M ≃ᵢ M) × (M × geometricSphere) => (p.1,p.2.1)) center :=
    hg.prodMk hx
  have hreassoc : ContMDiffAt J
      ((𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod (𝓡 2)) ∞
      (fun p : (M ≃ᵢ M) × (M × geometricSphere) => ((p.1,p.2.1),p.2.2)) center :=
    hgx.prodMk hu
  have hbase : ContMDiffAt J 𝓘(ℝ,E) ∞
      (fun p : (M ≃ᵢ M) × (M × geometricSphere) => p.1 p.2.1) center :=
    ContMDiffAt.comp (f := fun p : (M ≃ᵢ M) × (M × geometricSphere) =>
      (p.1,p.2.1)) center hAction.contMDiffAt hgx
  have hsphere := (contMDiffAt_fullNormalizedSphereAction_at_actual Q
    hChart hManifold hLie hAction f₀ z₀).comp
      (f := fun p : (M ≃ᵢ M) × (M × geometricSphere) =>
        ((p.1,p.2.1),p.2.2)) center hreassoc
  exact hbase.prodMk hsphere

end
end QuaternionicSymmetry.ManifoldQuaternionicFullSphereJointLocalSmooth
