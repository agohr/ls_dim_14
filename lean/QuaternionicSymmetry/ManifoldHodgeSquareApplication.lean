import QuaternionicSymmetry.ManifoldIntegratedRecoveredCertificates

/-!
Application of the generalized intersection inequality to the actual H2
witness classes. The square factors are genuine degree-twelve de Rham classes;
their surrounding powers have degrees twenty-eight and thirty-two.

Amann, Partial Classification Results for Positive Quaternion Kähler
Manifolds, arXiv:0911.4587v1, Theorem 1.2, p. 6, states the signed generalized
intersection theorem for
`u = -c₂(H)`, with orientation `u^n`. In degree `4*m` its sign is positive.
https://arxiv.org/pdf/0911.4587v1
This inspected preprint was accepted by the user as authoritative on
28 September 2026; no inspection of the final journal PDF is claimed.

The inequality below is an explicit interface, not an assertion of that
source theorem for an arbitrary class. Applying the literature theorem still
requires identification of its canonical class with the analytic quarter
class. This module proves the internal witness application independently of
that remaining normalization boundary.
-/

namespace QuaternionicSymmetry.ManifoldHodgeSquareApplication

open ManifoldEvenCharacteristicAlgebra ManifoldIntegratedDensityCertificates
  ManifoldIntegratedRecoveredCertificates ManifoldRecoveredCharacteristicCertificates
  ManifoldSevenVariableGradedEvaluation ManifoldSevenVariableWeightedDensity
  ManifoldTangentTraceRootCandidates ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Extract the actual top-degree de Rham component and integrate it. -/
def topIntegral (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E) :
    Total (E := E) (M := M) →ₗ[ℝ] ℝ :=
  (integrateGrade Q k hdim).comp
    (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (k + 1))

/-- The nonnegative degree-`4*m` part of the generalized intersection
inequality, on the constructed de Rham algebra and canonical integral. -/
def GeneralizedSquareNonnegative (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (u : Grade (E := E) (M := M) 1) : Prop :=
  ∀ m : ℕ, 2 * m ≤ k + 1 → ∀ a : Grade (E := E) (M := M) m,
    0 ≤ topIntegral Q k hdim
      ((DirectSum.of _ m a) ^ 2 * (DirectSum.of _ 1 u) ^ (k + 1 - 2 * m))

variable (D : CompatibleTangentConnection Q) (qdim : ℕ)

/-- Weighted homogeneity supplies the actual cohomological degree needed
by the generalized intersection theorem. -/
theorem weighted_square_nonnegative (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (hHodge : GeneralizedSquareNonnegative Q k hdim (quarterUClass Q D))
    (m : ℕ) (hm : 2 * m ≤ k + 1)
    (p : DimensionThirteenFourteenDensity.P)
    (hp : MvPolynomial.IsWeightedHomogeneous slotGrade p m) :
    0 ≤ sevenCandidateNumber Q D qdim k hdim
      (p ^ 2 * DimensionThirteenFourteenDensity.u ^ (k + 1 - 2 * m)) := by
  obtain ⟨a, ha⟩ := pureGrade_of_weighted (candidateGenerators Q D qdim) hp
  have hu : evaluateSeven Q D qdim DimensionThirteenFourteenDensity.u =
      DirectSum.of (Grade (E := E) (M := M)) 1 (quarterUClass Q D) := by
    simp [evaluateSeven, evaluate, DimensionThirteenFourteenDensity.u,
      generatorValues, candidateGenerators]
  change 0 ≤ topIntegral Q k hdim
    (evaluateSeven Q D qdim
      (p ^ 2 * DimensionThirteenFourteenDensity.u ^ (k + 1 - 2 * m)))
  rw [map_mul, map_pow, map_pow, hu]
  change evaluateSeven Q D qdim p = _ at ha
  rw [ha]
  exact hHodge m hm a

theorem witness13_square_nonnegative (hdim : 52 = Module.finrank ℝ E)
    (hHodge : GeneralizedSquareNonnegative Q 12 hdim (quarterUClass Q D)) :
    0 ≤ sevenCandidateNumber Q D 13 12 hdim
      (H2WitnessThirteen.factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 7) := by
  exact weighted_square_nonnegative Q D 13 12 hdim hHodge 3 (by norm_num)
    H2WitnessThirteen.factor factor13_weighted

theorem witness14_square_nonnegative (hdim : 56 = Module.finrank ℝ E)
    (hHodge : GeneralizedSquareNonnegative Q 13 hdim (quarterUClass Q D)) :
    0 ≤ sevenCandidateNumber Q D 14 13 hdim
      (H2WitnessFourteen.factor ^ 2 * DimensionThirteenFourteenDensity.u ^ 8) := by
  exact weighted_square_nonnegative Q D 14 13 hdim hHodge 3 (by norm_num)
    H2WitnessFourteen.factor factor14_weighted

end
end QuaternionicSymmetry.ManifoldHodgeSquareApplication
