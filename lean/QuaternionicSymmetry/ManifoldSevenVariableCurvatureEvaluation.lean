import QuaternionicSymmetry.ManifoldSevenVariableWeightedDensity
import QuaternionicSymmetry.ManifoldSixVariableDensityEvaluation
import QuaternionicSymmetry.H2WitnessThirteen
import QuaternionicSymmetry.H2WitnessFourteen

/-!
The seven printed H² certificates evaluated on actual smooth-manifold de Rham
classes. `u` is the induced rank-three raw trace square and `p_j` is a raw
odd tangent trace class; independently chosen real scalars permit later
normalizations. No topological Pontryagin or Hodge-sign identification is
asserted here.
-/

namespace QuaternionicSymmetry.ManifoldSevenVariableCurvatureEvaluation

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldSixVariableDensityEvaluation
  QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation
  QuaternionicSymmetry.ManifoldSevenVariableWeightedDensity
  QuaternionicSymmetry.DimensionThirteenFourteenDensity
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- The raw smooth-manifold curvature assignment, now including `p₆`. -/
noncomputable def rawGenerators : Generators (E := E) (M := M) where
  u := rawU Q D
  p1 := rawPowerSum Q D 0
  p2 := rawPowerSum Q D 1
  p3 := rawPowerSum Q D 2
  p4 := rawPowerSum Q D 3
  p5 := rawPowerSum Q D 4
  p6 := rawPowerSum Q D 5

/-- Independent real renormalizations of all seven raw curvature classes. -/
noncomputable def scaledGenerators (s : Fin 7 → ℝ) : Generators (E := E) (M := M) where
  u := s 0 • rawU Q D
  p1 := s 1 • rawPowerSum Q D 0
  p2 := s 2 • rawPowerSum Q D 1
  p3 := s 3 • rawPowerSum Q D 2
  p4 := s 4 • rawPowerSum Q D 3
  p5 := s 5 • rawPowerSum Q D 4
  p6 := s 6 • rawPowerSum Q D 5

noncomputable def evaluateScaled (s : Fin 7 → ℝ) : P →+* Total (E := E) (M := M) :=
  evaluate (scaledGenerators Q D s)

noncomputable def homogeneousScaledClass (s : Fin 7 → ℝ) (n : ℕ) (p : P) :
    Grade (E := E) (M := M) n :=
  homogeneousClass (scaledGenerators Q D s) n p

theorem density13_printed_total (s : Fin 7 → ℝ) :
    evaluateScaled Q D s density13 = evaluateScaled Q D s printed13 :=
  congrArg (evaluateScaled Q D s) density13_printed

theorem density14_printed_total (s : Fin 7 → ℝ) :
    evaluateScaled Q D s density14 = evaluateScaled Q D s printed14 :=
  congrArg (evaluateScaled Q D s) density14_printed

theorem density13_witness_total (s : Fin 7 → ℝ) :
    evaluateScaled Q D s density13 =
      evaluateScaled Q D s H2WitnessThirteen.witness :=
  congrArg (evaluateScaled Q D s) H2WitnessThirteen.density13_witness

theorem density14_witness_total (s : Fin 7 → ℝ) :
    evaluateScaled Q D s density14 =
      evaluateScaled Q D s H2WitnessFourteen.witness :=
  congrArg (evaluateScaled Q D s) H2WitnessFourteen.density14_witness

/-- The full printed and H² certificate identities in actual H⁵². -/
theorem density13_printed_class (s : Fin 7 → ℝ) :
    homogeneousScaledClass Q D s 13 density13 =
      homogeneousScaledClass Q D s 13 printed13 := by
  exact congrArg (ManifoldSevenVariableGradedEvaluation.homogeneousClass
    (scaledGenerators Q D s) 13) density13_printed

theorem density13_witness_class (s : Fin 7 → ℝ) :
    homogeneousScaledClass Q D s 13 density13 =
      homogeneousScaledClass Q D s 13 H2WitnessThirteen.witness := by
  exact congrArg (ManifoldSevenVariableGradedEvaluation.homogeneousClass
    (scaledGenerators Q D s) 13) H2WitnessThirteen.density13_witness

/-- The full printed and H² certificate identities in actual H⁵⁶. -/
theorem density14_printed_class (s : Fin 7 → ℝ) :
    homogeneousScaledClass Q D s 14 density14 =
      homogeneousScaledClass Q D s 14 printed14 := by
  exact congrArg (ManifoldSevenVariableGradedEvaluation.homogeneousClass
    (scaledGenerators Q D s) 14) density14_printed

theorem density14_witness_class (s : Fin 7 → ℝ) :
    homogeneousScaledClass Q D s 14 density14 =
      homogeneousScaledClass Q D s 14 H2WitnessFourteen.witness := by
  exact congrArg (ManifoldSevenVariableGradedEvaluation.homogeneousClass
    (scaledGenerators Q D s) 14) H2WitnessFourteen.density14_witness

theorem density13_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 13,
      evaluateScaled Q D s density13 =
        DirectSum.of (Grade (E := E) (M := M)) 13 a :=
  pureGrade_of_weighted (scaledGenerators Q D s) density13_weighted

theorem density14_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 14,
      evaluateScaled Q D s density14 =
        DirectSum.of (Grade (E := E) (M := M)) 14 a :=
  pureGrade_of_weighted (scaledGenerators Q D s) density14_weighted

/-- Each H² witness factor evaluates to an actual degree-12 class. -/
theorem factor13_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 3,
      evaluateScaled Q D s H2WitnessThirteen.factor =
        DirectSum.of (Grade (E := E) (M := M)) 3 a :=
  pureGrade_of_weighted (scaledGenerators Q D s) factor13_weighted

theorem factor14_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 3,
      evaluateScaled Q D s H2WitnessFourteen.factor =
        DirectSum.of (Grade (E := E) (M := M)) 3 a :=
  pureGrade_of_weighted (scaledGenerators Q D s) factor14_weighted

/-- The squared factor is an actual degree-24 class before multiplying by
`u⁷` or `u⁸`. -/
theorem factor13_square_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 6,
      evaluateScaled Q D s (H2WitnessThirteen.factor ^ 2) =
        DirectSum.of (Grade (E := E) (M := M)) 6 a := by
  apply pureGrade_of_weighted (scaledGenerators Q D s)
  simpa using factor13_weighted.pow 2

theorem factor14_square_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 6,
      evaluateScaled Q D s (H2WitnessFourteen.factor ^ 2) =
        DirectSum.of (Grade (E := E) (M := M)) 6 a := by
  apply pureGrade_of_weighted (scaledGenerators Q D s)
  simpa using factor14_weighted.pow 2

/-- Exact degree-52 H² term in the dimension-thirteen certificate:
the degree-24 square is multiplied by `u⁷`. -/
theorem squareTerm13_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 13,
      evaluateScaled Q D s
          (MvPolynomial.C 18 * H2WitnessThirteen.factor ^ 2 * u ^ 7) =
        DirectSum.of (Grade (E := E) (M := M)) 13 a := by
  apply pureGrade_of_weighted (scaledGenerators Q D s)
  have hu : MvPolynomial.IsWeightedHomogeneous slotGrade u 1 :=
    MvPolynomial.isWeightedHomogeneous_X (R := ℚ) slotGrade 0
  convert ((factor13_weighted.pow 2).C_mul 18).mul (hu.pow 7) using 1

/-- Exact degree-56 H² term in the dimension-fourteen certificate:
the degree-24 square is multiplied by `u⁸`. -/
theorem squareTerm14_pure_grade (s : Fin 7 → ℝ) :
    ∃ a : Grade (E := E) (M := M) 14,
      evaluateScaled Q D s
          (MvPolynomial.C 20 * H2WitnessFourteen.factor ^ 2 * u ^ 8) =
        DirectSum.of (Grade (E := E) (M := M)) 14 a := by
  apply pureGrade_of_weighted (scaledGenerators Q D s)
  have hu : MvPolynomial.IsWeightedHomogeneous slotGrade u 1 :=
    MvPolynomial.isWeightedHomogeneous_X (R := ℚ) slotGrade 0
  convert ((factor14_weighted.pow 2).C_mul 20).mul (hu.pow 8) using 1

theorem squareTerm13_evaluate (s : Fin 7 → ℝ) :
    evaluateScaled Q D s
        (MvPolynomial.C 18 * H2WitnessThirteen.factor ^ 2 * u ^ 7) =
      rationalConstants 18 *
        (evaluateScaled Q D s H2WitnessThirteen.factor) ^ 2 *
        (evaluateScaled Q D s u) ^ 7 := by
  simp only [map_mul, map_pow, evaluateScaled,
    ManifoldSevenVariableGradedEvaluation.evaluate, MvPolynomial.eval₂Hom_C]

theorem squareTerm14_evaluate (s : Fin 7 → ℝ) :
    evaluateScaled Q D s
        (MvPolynomial.C 20 * H2WitnessFourteen.factor ^ 2 * u ^ 8) =
      rationalConstants 20 *
        (evaluateScaled Q D s H2WitnessFourteen.factor) ^ 2 *
        (evaluateScaled Q D s u) ^ 8 := by
  simp only [map_mul, map_pow, evaluateScaled,
    ManifoldSevenVariableGradedEvaluation.evaluate, MvPolynomial.eval₂Hom_C]

theorem rawGenerators_connection_independent
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    rawGenerators Q D' = rawGenerators Q D := by
  simp [rawGenerators, rawU_connection_independent Q D D',
    rawPowerSum_connection_independent Q D D' 0,
    rawPowerSum_connection_independent Q D D' 1,
    rawPowerSum_connection_independent Q D D' 2,
    rawPowerSum_connection_independent Q D D' 3,
    rawPowerSum_connection_independent Q D D' 4,
    rawPowerSum_connection_independent Q D D' 5]

theorem scaledGenerators_connection_independent (s : Fin 7 → ℝ)
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    scaledGenerators Q D' s = scaledGenerators Q D s := by
  simp [scaledGenerators, rawU_connection_independent Q D D',
    rawPowerSum_connection_independent Q D D' 0,
    rawPowerSum_connection_independent Q D D' 1,
    rawPowerSum_connection_independent Q D D' 2,
    rawPowerSum_connection_independent Q D D' 3,
    rawPowerSum_connection_independent Q D D' 4,
    rawPowerSum_connection_independent Q D D' 5]

theorem evaluateScaled_connection_independent (s : Fin 7 → ℝ)
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (p : P) : evaluateScaled Q D' s p = evaluateScaled Q D s p := by
  simp only [evaluateScaled, scaledGenerators_connection_independent Q D s D']

theorem homogeneousScaledClass_connection_independent (s : Fin 7 → ℝ)
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (n : ℕ) (p : P) :
    homogeneousScaledClass Q D' s n p = homogeneousScaledClass Q D s n p := by
  unfold homogeneousScaledClass
  rw [scaledGenerators_connection_independent Q D s D']

end QuaternionicSymmetry.ManifoldSevenVariableCurvatureEvaluation
