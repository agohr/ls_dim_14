import QuaternionicSymmetry.ManifoldQuaternionicFullMovingComparison
import QuaternionicSymmetry.ManifoldQuaternionicSphereSmoothAt

/-! A smooth full-isometry Lie-family Euclidean extension of the local
twistor sphere action. Off the quaternionic subgroup its values need not
lie on the unit sphere. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullSphereAmbientSmooth

open Manifold
open ManifoldQuaternionicFullMovingCoefficientSmooth
open ManifoldQuaternionicFullMovingComparison
open ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicSphereSmoothAt
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
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

def fullMovingSphereAmbient
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
    (x₀ : M)
    (p : ((letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M) × M) ×
      geometricSphere) : EuclideanThree :=
  toEuclidean (fullMovingCoefficientRotation Q hChart hManifold g₀ x₀
    (p.1, EuclideanSpace.equiv (Fin 3) ℝ (p.2 : EuclideanThree)))

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem contMDiffAt_fullMovingSphereAmbient
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
    (g₀ : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ : M) (u : geometricSphere) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContMDiffAt ((𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod (𝓡 2))
      𝓘(ℝ,EuclideanThree) ∞
      (fullMovingSphereAmbient Q hChart hManifold g₀ x₀) ((g₀,x₀),u) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  let J := (𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod (𝓡 2)
  have hsnd : ContMDiffAt J (𝓡 2) ∞
      (fun p : ((M ≃ᵢ M) × M) × geometricSphere => p.2)
      ((g₀,x₀),u) := contMDiffAt_snd
  have hcoe : ContMDiffAt J 𝓘(ℝ,EuclideanThree) ∞
      (fun p : ((M ≃ᵢ M) × M) × geometricSphere =>
        (p.2 : EuclideanThree)) ((g₀,x₀),u) :=
    (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)).contMDiffAt.comp
      ((g₀,x₀),u) hsnd
  have hcoeff : ContMDiffAt J 𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun p : ((M ≃ᵢ M) × M) × geometricSphere =>
        EuclideanSpace.equiv (Fin 3) ℝ (p.2 : EuclideanThree))
      ((g₀,x₀),u) :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).contMDiffAt.comp
      ((g₀,x₀),u) hcoe
  have hpair : ContMDiffAt J
      ((𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ)) ∞
      (fun p : ((M ≃ᵢ M) × M) × geometricSphere =>
        (p.1, EuclideanSpace.equiv (Fin 3) ℝ (p.2 : EuclideanThree)))
      ((g₀,x₀),u) := contMDiffAt_fst.prodMk hcoeff
  have hrot := (contMDiffAt_fullMovingCoefficientRotation Q hChart hManifold
    hLie hAction g₀ x₀
    (EuclideanSpace.equiv (Fin 3) ℝ (u : EuclideanThree))).comp
      ((g₀,x₀),u) hpair
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff).contMDiffAt.comp
    ((g₀,x₀),u) hrot

end
end QuaternionicSymmetry.ManifoldQuaternionicFullSphereAmbientSmooth
