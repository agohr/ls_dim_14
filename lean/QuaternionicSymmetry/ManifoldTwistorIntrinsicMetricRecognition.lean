import QuaternionicSymmetry.ManifoldRiemannianSymmetryTransport
import QuaternionicSymmetry.ManifoldTwistorMetricRecognitionInput

/-! Recognition of intrinsic Riemannian symmetry from a biholomorphism of
genuine twistors.  The comparison positive quaternionic-Kähler geometry and
its symmetry are explicit hypotheses; no model catalogue or opaque `IsWolf`
predicate is hidden in the conclusion. -/

namespace QuaternionicSymmetry.ManifoldTwistorIntrinsicMetricRecognition

open ManifoldMetricHomothety ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicScalarCurvature
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorMetricRecognitionInput
open ManifoldRiemannianIntrinsicSymmetry
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [Nontrivial F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [Nonempty N]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

/-- LeBrun's normalized twistor metric recognition transfers genuine
Riemannian point symmetries from the comparison geometry to the original.
The comparison geometry must actually be symmetric; this theorem does not
manufacture it from an adjoint-variety name. -/
theorem intrinsicSymmetric_of_normalized_twistor_biholomorphism
    (hRecognition : NormalizedTwistorMetricRecognition)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (R : CompactConnectedPositiveQuaternionicKahlerGeometry (E := F) (M := N))
    (n : ℕ) (hn : 2 ≤ n)
    (hDimP : Module.finrank ℝ E = 4*n)
    (hDimR : Module.finrank ℝ F = 4*n)
    (hScalarP : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    (hScalarR : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target),
      localScalarCurvature R.tangent R.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (B : CompatibleComplexAtlas R.tangent R.connection n)
    (hBiholo : letI := A.charts
      letI := B.charts
      Nonempty (Diffeomorph 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,ComplexTwistorModel n)
        (SphereBundleTotal P.tangent) (SphereBundleTotal R.tangent) ∞))
    (hR : IsRiemannianSymmetric R.tangent) :
    IsRiemannianSymmetric P.tangent := by
  obtain ⟨f, _⟩ := hRecognition P R n hn hDimP hDimR
    hScalarP hScalarR A B hBiholo
  exact (isRiemannianSymmetric_iff_metricHomothety f).2 hR

/-- The unnormalized version retains both positive scalar normalization
factors; its actual homothety has scale `s²/t²`, which does not affect
intrinsic Riemannian symmetry. -/
theorem intrinsicSymmetric_of_twistor_biholomorphism
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
      (rescaleCompact R t ht).connection n)
    (hBiholo : letI := A.charts
      letI := B.charts
      Nonempty (Diffeomorph 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,ComplexTwistorModel n)
        (SphereBundleTotal (rescaleCompact P s hs).tangent)
        (SphereBundleTotal (rescaleCompact R t ht).tangent) ∞))
    (hR : IsRiemannianSymmetric R.tangent) :
    IsRiemannianSymmetric P.tangent := by
  obtain ⟨f, _⟩ := homothety_of_normalized_twistor_biholomorphism
    hRecognition P R s t hs ht n hn hDimP hDimR
    hScalarP hScalarR A B hBiholo
  exact (isRiemannianSymmetric_iff_metricHomothety f).2 hR

end
end QuaternionicSymmetry.ManifoldTwistorIntrinsicMetricRecognition
