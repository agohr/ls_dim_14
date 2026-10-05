import QuaternionicSymmetry.Stage2ActualInduction
import QuaternionicSymmetry.Stage2IntrinsicGeometry
import QuaternionicSymmetry.ManifoldFourDerdzinskiIntrinsicSymmetry

/-! Metric recognition after actual normalized contact homogeneity, including
the separate four-dimensional geometric input. No symmetry is inferred from
generation alone. The induction result must discharge homogeneity before a
source-only endpoint can apply this lemma. -/

namespace QuaternionicSymmetry.Stage2IntrinsicMetricApplication

open Stage2ActualInduction Stage2IntrinsicGeometry
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicScalarCurvature
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorPositiveAnticanonicalSimplyConnected
open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldTwistorHomogeneousContactSymmetrySource
open ManifoldTwistorSphereCore ManifoldRiemannianIntrinsicSymmetry
open ManifoldMetricHomothety ManifoldFourDerdzinskiIntrinsicSymmetry
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem intrinsicSymmetric_of_normalizedContactHomogeneity
    (n : ℕ) (hn : 2 ≤ n) (hHom : NormalizedContactHomogeneity n)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 4*n)
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hWolfLeBrun : HomogeneousContactTwistorSymmetryCorollary) :
    IsRiemannianSymmetric P.tangent := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  let S := P.tangent.reduction.Q (achart E (Classical.choice ‹Nonempty M›))
  have hSn : S.quaternionicDimension = n := by
    have hS := S.real_finrank
    omega
  obtain ⟨s,hs,hScalar⟩ := exists_normalized_scalar S P heq38 (by omega)
  let R := rescaleCompact P s hs
  have hScalar' : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature R.tangent R.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2) := by
    simpa only [hSn] using hScalar
  obtain ⟨A,C,hContact⟩ := hHom R hDim hScalar'
  have hSC := normalized_twistor_simplyConnected
    hBallmann hT1 R n hn hDim hScalar'
  have hSym := intrinsicSymmetric_of_contactAutomorphisms_transitive
    hWolfLeBrun R n hn hDim A C hSC hContact
  change IsRiemannianSymmetric
    (ManifoldQuaternionicHomothetyReduction.rescaleMetric
      P.tangent s (ne_of_gt hs)) at hSym
  exact (isRiemannianSymmetric_iff_metricHomothety
    (rescaleHomothety P.tangent s hs)).mpr hSym

/-- Both dimension branches concern exactly the metric in the input. -/
theorem intrinsicSymmetric_through_bound
    (limit : ℕ)
    (hHom : ∀ n, 2 ≤ n → n ≤ limit → NormalizedContactHomogeneity n)
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hWolfLeBrun : HomogeneousContactTwistorSymmetryCorollary)
    (hFour : DerdzinskiFourSymmetrySource)
    {n : ℕ} (P : CompactConnectedPositiveTwistorGeometry (E := E) (M := M) n)
    (hLimit : n ≤ limit) : IsRiemannianSymmetric P.tangent := by
  by_cases hn : n = 1
  · subst n
    exact symmetric_of_derdzinskiFour hFour (toFour P)
  · have hn2 : 2 ≤ n := by have := P.positiveDimension; omega
    exact intrinsicSymmetric_of_normalizedContactHomogeneity n hn2
      (hHom n hn2 hLimit) P.toCompactConnectedPositiveQuaternionicKahlerGeometry
      P.realDimension heq38 hT1 hBallmann hWolfLeBrun

end
end QuaternionicSymmetry.Stage2IntrinsicMetricApplication
