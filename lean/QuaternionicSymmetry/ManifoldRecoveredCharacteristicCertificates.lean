import QuaternionicSymmetry.ManifoldTangentTraceRootCandidates
import QuaternionicSymmetry.DimensionElevenTwelveDensity

/-!
The already checked exact density and H² certificates, evaluated with the
analytic characteristic candidates recovered from normalized tangent
curvature traces and `u=p₁(Q)/4`. Their identification with the corrected
standard-bundle Chern–Weil forms remains a separate geometric comparison.
-/

namespace QuaternionicSymmetry.ManifoldRecoveredCharacteristicCertificates

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation
  QuaternionicSymmetry.ManifoldTangentTraceRootCandidates
  QuaternionicSymmetry.ManifoldSevenVariableWeightedDensity
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
variable (qdim : ℕ)

noncomputable def evaluateSeven :
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.P →+*
      Total (E := E) (M := M) :=
  ManifoldSevenVariableGradedEvaluation.evaluate (candidateGenerators Q D qdim)

noncomputable def evaluateSix :
    QuaternionicSymmetry.DimensionElevenTwelveDensity.P →+*
      Total (E := E) (M := M) :=
  MvPolynomial.eval₂Hom rationalConstants
    ![DirectSum.of _ 1 (quarterUClass Q D),
      DirectSum.of _ 1 (candidatePowerClass Q D qdim 1),
      DirectSum.of _ 2 (candidatePowerClass Q D qdim 2),
      DirectSum.of _ 3 (candidatePowerClass Q D qdim 3),
      DirectSum.of _ 4 (candidatePowerClass Q D qdim 4),
      DirectSum.of _ 5 (candidatePowerClass Q D qdim 5)]

theorem density13_printed :
    evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.density13 =
      evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.printed13 :=
  congrArg (evaluateSeven Q D qdim)
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.density13_printed

theorem density14_printed :
    evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.density14 =
      evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.printed14 :=
  congrArg (evaluateSeven Q D qdim)
    QuaternionicSymmetry.DimensionThirteenFourteenDensity.density14_printed

theorem density13_witness :
    evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.density13 =
      evaluateSeven Q D qdim QuaternionicSymmetry.H2WitnessThirteen.witness :=
  congrArg (evaluateSeven Q D qdim)
    QuaternionicSymmetry.H2WitnessThirteen.density13_witness

theorem density14_witness :
    evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.density14 =
      evaluateSeven Q D qdim QuaternionicSymmetry.H2WitnessFourteen.witness :=
  congrArg (evaluateSeven Q D qdim)
    QuaternionicSymmetry.H2WitnessFourteen.density14_witness

theorem density13_pure_grade :
    ∃ a : Grade (E := E) (M := M) 13,
      evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.density13 =
        DirectSum.of (Grade (E := E) (M := M)) 13 a :=
  pureGrade_of_weighted (candidateGenerators Q D qdim) density13_weighted

theorem density14_pure_grade :
    ∃ a : Grade (E := E) (M := M) 14,
      evaluateSeven Q D qdim QuaternionicSymmetry.DimensionThirteenFourteenDensity.density14 =
        DirectSum.of (Grade (E := E) (M := M)) 14 a :=
  pureGrade_of_weighted (candidateGenerators Q D qdim) density14_weighted

theorem density11_printed :
    evaluateSix Q D qdim QuaternionicSymmetry.DimensionElevenTwelveDensity.density11 =
      evaluateSix Q D qdim QuaternionicSymmetry.DimensionElevenTwelveDensity.printed11 :=
  congrArg (evaluateSix Q D qdim)
    QuaternionicSymmetry.DimensionElevenTwelveDensity.density11_printed

theorem density12_printed :
    evaluateSix Q D qdim QuaternionicSymmetry.DimensionElevenTwelveDensity.density12 =
      evaluateSix Q D qdim QuaternionicSymmetry.DimensionElevenTwelveDensity.printed12 :=
  congrArg (evaluateSix Q D qdim)
    QuaternionicSymmetry.DimensionElevenTwelveDensity.density12_printed

/-- The six-variable evaluator is the restriction of the seven-variable
evaluator along the checked polynomial lift; the older and newer
certificate semantics therefore agree exactly. -/
theorem evaluateSeven_lift
    (p : QuaternionicSymmetry.DimensionElevenTwelveDensity.P) :
    evaluateSeven Q D qdim (QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift p) =
      evaluateSix Q D qdim p := by
  letI : Algebra ℚ (Total (E := E) (M := M)) := rationalAlgebra (E := E) (M := M)
  change MvPolynomial.aeval
      (generatorValues (candidateGenerators Q D qdim))
        (QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift p) =
      MvPolynomial.aeval
        ![DirectSum.of _ 1 (quarterUClass Q D),
          DirectSum.of _ 1 (candidatePowerClass Q D qdim 1),
          DirectSum.of _ 2 (candidatePowerClass Q D qdim 2),
          DirectSum.of _ 3 (candidatePowerClass Q D qdim 3),
          DirectSum.of _ 4 (candidatePowerClass Q D qdim 4),
          DirectSum.of _ 5 (candidatePowerClass Q D qdim 5)] p
  unfold QuaternionicSymmetry.DimensionThirteenFourteenDensity.lift
  rw [MvPolynomial.comp_aeval_apply]
  have hv : (fun i : Fin 6 =>
      (MvPolynomial.aeval (generatorValues (candidateGenerators Q D qdim)))
        (![QuaternionicSymmetry.DimensionThirteenFourteenDensity.u,
          QuaternionicSymmetry.DimensionThirteenFourteenDensity.p1,
          QuaternionicSymmetry.DimensionThirteenFourteenDensity.p2,
          QuaternionicSymmetry.DimensionThirteenFourteenDensity.p3,
          QuaternionicSymmetry.DimensionThirteenFourteenDensity.p4,
          QuaternionicSymmetry.DimensionThirteenFourteenDensity.p5] i)) =
      ![DirectSum.of _ 1 (quarterUClass Q D),
        DirectSum.of _ 1 (candidatePowerClass Q D qdim 1),
        DirectSum.of _ 2 (candidatePowerClass Q D qdim 2),
        DirectSum.of _ 3 (candidatePowerClass Q D qdim 3),
        DirectSum.of _ 4 (candidatePowerClass Q D qdim 4),
        DirectSum.of _ 5 (candidatePowerClass Q D qdim 5)] := by
    funext i
    fin_cases i <;>
      simp [QuaternionicSymmetry.DimensionThirteenFourteenDensity.u,
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.p1,
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.p2,
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.p3,
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.p4,
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.p5,
        generatorValues, candidateGenerators]
  rw [hv]

theorem evaluateSeven_connection_independent
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (p : QuaternionicSymmetry.DimensionThirteenFourteenDensity.P) :
    evaluateSeven Q D' qdim p = evaluateSeven Q D qdim p := by
  simp [evaluateSeven, candidateGenerators_connection_independent Q D qdim D']

theorem evaluateSix_connection_independent
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (p : QuaternionicSymmetry.DimensionElevenTwelveDensity.P) :
    evaluateSix Q D' qdim p = evaluateSix Q D qdim p := by
  simp [evaluateSix, quarterUClass_connection_independent Q D D',
    candidatePowerClass_connection_independent Q D qdim 1 D',
    candidatePowerClass_connection_independent Q D qdim 2 D',
    candidatePowerClass_connection_independent Q D qdim 3 D',
    candidatePowerClass_connection_independent Q D qdim 4 D',
    candidatePowerClass_connection_independent Q D qdim 5 D']

end QuaternionicSymmetry.ManifoldRecoveredCharacteristicCertificates
