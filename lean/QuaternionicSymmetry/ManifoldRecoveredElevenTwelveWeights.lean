import QuaternionicSymmetry.ManifoldRecoveredCharacteristicCertificates

/-! Exact H⁴⁴ and H⁴⁸ purity of the older printed certificates after the
six-to-seven-variable lift, for arbitrary genuine graded class generators. -/

namespace QuaternionicSymmetry.ManifoldRecoveredElevenTwelveWeights

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation
  QuaternionicSymmetry.ManifoldSevenVariableWeightedDensity
  QuaternionicSymmetry.ManifoldRecoveredCharacteristicCertificates
  QuaternionicSymmetry.ManifoldTangentTraceRootCandidates
open scoped Manifold ContDiff Topology

private def coefficient11 : Fin 30 → ℚ := ![288, (4965304 / 51975), (35416 / 2835), (154736 / 93555), (33772 / 42525), (16052 / 42525), (18848 / 467775), ((4 / 1403325) * 8470), ((4 / 1403325) * 9207), ((4 / 1403325) * 825), ((4 / 1403325) * 2882), ((4 / 1403325) * 450), ((8192 / 11496038400) * 385), ((8192 / 11496038400) * 770), ((8192 / 11496038400) * 440), ((8192 / 11496038400) * 231), ((8192 / 11496038400) * 198), ((8192 / 11496038400) * 88), ((8192 / 11496038400) * 48), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def coefficient12 : Fin 30 → ℚ := ![336, (6101552 / 51975), (33368 / 2025), (962072 / 467775), (49064 / 42525), (22408 / 42525), (22384 / 467775), (146 / 3645), (604 / 14175), (158 / 42525), (1616 / 127575), (268 / 155925), ((16384 / 11496038400) * 385), ((16384 / 11496038400) * 770), ((16384 / 11496038400) * 440), ((16384 / 11496038400) * 231), ((16384 / 11496038400) * 198), ((16384 / 11496038400) * 88), ((16384 / 11496038400) * 48), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxHeartbeats 2000000

private theorem lift_printed11_eq_pattern :
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift
      QuaternionicSymmetry.DimensionElevenTwelveDensity.printed11 =
        pattern 5 coefficient11 := by
  apply MvPolynomial.funext
  intro v
  simp [QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.printed11,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.q11,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.f5,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.u,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p1,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p2,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p3,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p4,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p5,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.u,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p1,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p2,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p3,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p4,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p5,
    pattern, coefficient11]
  ring

theorem lifted_density11_weighted :
    MvPolynomial.IsWeightedHomogeneous slotGrade
      (QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift
        QuaternionicSymmetry.DimensionElevenTwelveDensity.density11) 11 := by
  rw [QuaternionicSymmetry.DimensionElevenTwelveDensity.density11_printed,
    lift_printed11_eq_pattern]
  simpa using pattern_weighted 5 coefficient11

private theorem lift_printed12_eq_pattern :
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift
      QuaternionicSymmetry.DimensionElevenTwelveDensity.printed12 =
        pattern 6 coefficient12 := by
  apply MvPolynomial.funext
  intro v
  simp [QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.printed12,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.q12,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.f5,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.u,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p1,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p2,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p3,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p4,
    QuaternionicSymmetry.DimensionElevenTwelveDensity.p5,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.u,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p1,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p2,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p3,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p4,
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.p5,
    pattern, coefficient12]
  ring

theorem lifted_density12_weighted :
    MvPolynomial.IsWeightedHomogeneous slotGrade
      (QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift
        QuaternionicSymmetry.DimensionElevenTwelveDensity.density12) 12 := by
  rw [QuaternionicSymmetry.DimensionElevenTwelveDensity.density12_printed,
    lift_printed12_eq_pattern]
  simpa using pattern_weighted 6 coefficient12

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
variable (qdim : ℕ)

theorem density11_pure_grade :
    ∃ a : Grade (E := E) (M := M) 11,
      evaluateSix Q D qdim QuaternionicSymmetry.DimensionElevenTwelveDensity.density11 =
        DirectSum.of (Grade (E := E) (M := M)) 11 a := by
  obtain ⟨a, ha⟩ := pureGrade_of_weighted (candidateGenerators Q D qdim)
    lifted_density11_weighted
  change evaluateSeven Q D qdim
    (QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift
      QuaternionicSymmetry.DimensionElevenTwelveDensity.density11) = _ at ha
  rw [evaluateSeven_lift Q D qdim] at ha
  exact ⟨a, ha⟩

theorem density12_pure_grade :
    ∃ a : Grade (E := E) (M := M) 12,
      evaluateSix Q D qdim QuaternionicSymmetry.DimensionElevenTwelveDensity.density12 =
        DirectSum.of (Grade (E := E) (M := M)) 12 a := by
  obtain ⟨a, ha⟩ := pureGrade_of_weighted (candidateGenerators Q D qdim)
    lifted_density12_weighted
  change evaluateSeven Q D qdim
    (QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift
      QuaternionicSymmetry.DimensionElevenTwelveDensity.density12) = _ at ha
  rw [evaluateSeven_lift Q D qdim] at ha
  exact ⟨a, ha⟩

end QuaternionicSymmetry.ManifoldRecoveredElevenTwelveWeights
