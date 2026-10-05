import QuaternionicSymmetry.ManifoldMetricHomothety
import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

/-! The metric-recognition direction of LeBrun 1995, Corollary 3.4,
author PDF pp.17–18. The scalar normalization is that of Theorem 2.1.
The source compares two actual positive quaternionic-Kähler manifolds
whose genuine twistor spaces are biholomorphic; it does not assert that
either manifold is homogeneous or belongs to a model catalog. -/

namespace QuaternionicSymmetry.ManifoldTwistorMetricRecognitionInput

open ManifoldMetricHomothety ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicScalarCurvature
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

/-- Literal normalized metric recognition. The output includes an actual
base diffeomorphism and its pullback-metric equation with factor one.
The supplied biholomorphism need not be the lift of that diffeomorphism. -/
def NormalizedTwistorMetricRecognition : Prop :=
  ∀ {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [Nontrivial F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [Nonempty N]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (R : CompactConnectedPositiveQuaternionicKahlerGeometry (E := F) (M := N))
    (n : ℕ) (_hn : 2 ≤ n)
    (_hDimP : Module.finrank ℝ E = 4*n)
    (_hDimR : Module.finrank ℝ F = 4*n)
    (_hScalarP : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    (_hScalarR : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target),
      localScalarCurvature R.tangent R.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (B : CompatibleComplexAtlas R.tangent R.connection n),
    letI := A.charts
    letI := B.charts
    Nonempty (Diffeomorph 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal P.tangent) (SphereBundleTotal R.tangent) ∞) →
      ∃ f : MetricHomothety P.tangent R.tangent, f.scale = 1

variable {E F M N : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [Nontrivial F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [Nonempty N]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

/-- Matching the actual normalized twistor spaces produces a homothety
of the original metrics, after internally composing the two explicit
identity rescalings. No homogeneity or classification assertion is used. -/
theorem homothety_of_normalized_twistor_biholomorphism
    (hRecognition : NormalizedTwistorMetricRecognition)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (R : CompactConnectedPositiveQuaternionicKahlerGeometry (E := F) (M := N))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (n : ℕ) (hn : 2 ≤ n)
    (hDimP : Module.finrank ℝ E = 4*n)
    (hDimR : Module.finrank ℝ F = 4*n)
    (hScalarP : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature (rescaleCompact P s hs).tangent
        (rescaleCompact P s hs).connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    (hScalarR : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target),
      localScalarCurvature (rescaleCompact R t ht).tangent
        (rescaleCompact R t ht).connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    (A : CompatibleComplexAtlas (rescaleCompact P s hs).tangent
      (rescaleCompact P s hs).connection n)
    (B : CompatibleComplexAtlas (rescaleCompact R t ht).tangent
      (rescaleCompact R t ht).connection n) :
    letI := A.charts
    letI := B.charts
    Nonempty (Diffeomorph 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal (rescaleCompact P s hs).tangent)
      (SphereBundleTotal (rescaleCompact R t ht).tangent) ∞) →
      ∃ f : MetricHomothety P.tangent R.tangent,
        f.scale = (t ^ 2)⁻¹ * s ^ 2 := by
  letI := A.charts
  letI := B.charts
  intro hBiholo
  obtain ⟨f,hf⟩ := hRecognition (rescaleCompact P s hs)
    (rescaleCompact R t ht) n hn hDimP hDimR hScalarP hScalarR A B hBiholo
  let left := homothety_of_rescaled_source P.tangent
    (rescaleCompact R t ht).tangent s hs f
  let right := MetricHomothety.symm R.tangent
    (rescaleCompact R t ht).tangent (rescaleHomothety R.tangent t ht)
  refine ⟨MetricHomothety.trans P.tangent
    (rescaleCompact R t ht).tangent R.tangent left right, ?_⟩
  change (t ^ 2)⁻¹ * (f.scale * s ^ 2) = _
  rw [hf, one_mul]

end
end QuaternionicSymmetry.ManifoldTwistorMetricRecognitionInput
