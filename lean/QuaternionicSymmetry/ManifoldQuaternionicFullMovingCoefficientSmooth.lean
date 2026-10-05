import QuaternionicSymmetry.ManifoldQuaternionicFullMovingAdaptedSmooth

/-! The full-isometry Lie family supplies a smooth ambient extension of
the actual quaternionic coefficient rotation near each quaternionic
isometry, even though non-quaternionic full isometries need not preserve
the rank-three sphere. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFullMovingCoefficientSmooth

open Manifold
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicFullMovingAdaptedSmooth
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def fullMovingInverseDerivative
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
    (p : (letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M) × M) :
    E →L[ℝ] E :=
  fullMovingAdaptedDerivative Q hChart hManifold g₀⁻¹ (g₀ x₀)
    (p.1⁻¹,p.1 p.2)

theorem contMDiffAt_fullMovingInverseDerivative
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
    (x₀ : M) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fullMovingInverseDerivative Q hChart hManifold g₀ x₀) (g₀,x₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  have hpair : ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E))
      (𝓘(ℝ,V).prod 𝓘(ℝ,E)) ∞
      (fun p : (M ≃ᵢ M) × M => (p.1⁻¹,p.1 p.2)) (g₀,x₀) :=
    (contMDiffAt_fst.inv).prodMk (hAction.contMDiffAt (x := (g₀,x₀)))
  have hD := contMDiffAt_fullMovingAdaptedDerivative Q hChart hManifold hAction
    g₀⁻¹ (g₀ x₀)
  have h := hD.comp (g₀,x₀) (by simpa only [IsometryEquiv.symm_apply_apply] using hpair)
  exact h

/-- The smooth ambient rank-three coefficient formula. Away from the
quaternionic subgroup it need not preserve the coefficient sphere. -/
def fullMovingCoefficientRotation
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
      (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  coeff (Q.reduction.Q (achart E (g₀ x₀)))
    ((fullMovingAdaptedDerivative Q hChart hManifold g₀ x₀ p.1).comp
      ((synth (Q.reduction.Q (achart E x₀)) p.2).comp
        (fullMovingInverseDerivative Q hChart hManifold g₀ x₀ p.1)))

theorem contMDiffAt_fullMovingCoefficientRotation
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
    (x₀ : M) (a₀ : Fin 3 → ℝ) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContMDiffAt ((𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      𝓘(ℝ,Fin 3 → ℝ) ∞
      (fullMovingCoefficientRotation Q hChart hManifold g₀ x₀)
      ((g₀,x₀),a₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  let J := (𝓘(ℝ,V).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ)
  have hforward : ContMDiffAt J 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p : ((M ≃ᵢ M) × M) × (Fin 3 → ℝ) =>
        fullMovingAdaptedDerivative Q hChart hManifold g₀ x₀ p.1)
      ((g₀,x₀),a₀) :=
    (contMDiffAt_fullMovingAdaptedDerivative Q hChart hManifold hAction g₀ x₀).comp
      ((g₀,x₀),a₀) contMDiffAt_fst
  have hbackward : ContMDiffAt J 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p : ((M ≃ᵢ M) × M) × (Fin 3 → ℝ) =>
        fullMovingInverseDerivative Q hChart hManifold g₀ x₀ p.1)
      ((g₀,x₀),a₀) := by
    have hbase : ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,E))
        𝓘(ℝ,E →L[ℝ] E) ∞
        (fullMovingInverseDerivative Q hChart hManifold g₀ x₀) (g₀,x₀) :=
      contMDiffAt_fullMovingInverseDerivative Q hChart hManifold hLie hAction g₀ x₀
    exact ContMDiffAt.comp
      (f := fun p : ((M ≃ᵢ M) × M) × (Fin 3 → ℝ) => p.1)
      (g := fullMovingInverseDerivative Q hChart hManifold g₀ x₀)
      ((g₀,x₀),a₀) hbase contMDiffAt_fst
  have hsynth : ContMDiffAt J 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p : ((M ≃ᵢ M) × M) × (Fin 3 → ℝ) =>
        synth (Q.reduction.Q (achart E x₀)) p.2)
      ((g₀,x₀),a₀) :=
    (synth (Q.reduction.Q (achart E x₀))).contMDiff.contMDiffAt.comp
      ((g₀,x₀),a₀) contMDiffAt_snd
  have hconj : ContMDiffAt J 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun p : ((M ≃ᵢ M) × M) × (Fin 3 → ℝ) =>
        (fullMovingAdaptedDerivative Q hChart hManifold g₀ x₀ p.1).comp
          ((synth (Q.reduction.Q (achart E x₀)) p.2).comp
            (fullMovingInverseDerivative Q hChart hManifold g₀ x₀ p.1)))
      ((g₀,x₀),a₀) := hforward.clm_comp (hsynth.clm_comp hbackward)
  exact (coeff (Q.reduction.Q (achart E (g₀ x₀)))).contMDiff.contMDiffAt.comp
    ((g₀,x₀),a₀) hconj

end
end QuaternionicSymmetry.ManifoldQuaternionicFullMovingCoefficientSmooth
