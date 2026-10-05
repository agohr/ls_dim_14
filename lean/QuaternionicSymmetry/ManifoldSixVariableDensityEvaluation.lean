import QuaternionicSymmetry.DimensionElevenTwelveDensity
import QuaternionicSymmetry.ManifoldQuaternionicPolynomialEvaluation
import Mathlib.Algebra.DirectSum.Module

/-!
The six independent variables in the printed dimension-eleven and
dimension-twelve certificates can be substituted by genuine manifold de Rham
classes. This is explicitly a substitution into *raw curvature traces*.
In particular, the first variable is `tr(F_Q²)`, not an identified
topological Pontryagin class, and the remaining variables follow the formal
power-sum convention `p_j = tr((-F_T²)^j)/2`.
-/

namespace QuaternionicSymmetry.ManifoldSixVariableDensityEvaluation

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldDeRhamRing
  QuaternionicSymmetry.ManifoldCharacteristicPolynomialSoundness
  QuaternionicSymmetry.ManifoldCharacteristicExpression
  QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
  QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence
  QuaternionicSymmetry.DimensionElevenTwelveDensity
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- The formal `(-1)^j tr(F_T^(2j))/2` substitution, indexed by `j-1`. -/
noncomputable def rawPowerSum
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (j : ℕ) : Grade (E := E) (M := M) (j + 1) :=
  ((-1 : ℝ) ^ (j + 1) / 2) •
    (by
      change QuaternionicSymmetry.ManifoldDifferentialForms.positiveDegreeCohomology
        (E := E) (M₀ := M) (4 * j + 3)
      have hp : QuaternionicSymmetry.LocalChernWeilOrderedTransgression.primitiveDegree
          (2 * j + 1) = 4 * j + 3 := by
        have h := QuaternionicSymmetry.LocalChernWeilOrderedTransgression.primitiveDegree_add_one
          (2 * j + 1)
        rw [QuaternionicSymmetry.LocalChernWeilTracePowers.powerDegree_eq] at h
        omega
      exact castClass hp (tangentTraceClass Q D (2 * j + 1)))

/-- The raw induced rank-three trace-square class. -/
noncomputable def rawU
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    Grade (E := E) (M := M) 1 := by
  change QuaternionicSymmetry.ManifoldDifferentialForms.positiveDegreeCohomology
    (E := E) (M₀ := M) 3
  exact traceCurvatureSquareClass Q D

/-- The six-variable assignment. `u` is the raw rank-three trace square;
`p_j` is `(-1)^j tr(F_T^(2j))/2`, as a formal curvature substitution. -/
noncomputable def traceVariables
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    Fin 6 → Total (E := E) (M := M) :=
  ![DirectSum.of _ 1 (rawU Q D),
    DirectSum.of _ 1 (rawPowerSum Q D 0),
    DirectSum.of _ 2 (rawPowerSum Q D 1),
    DirectSum.of _ 3 (rawPowerSum Q D 2),
    DirectSum.of _ 4 (rawPowerSum Q D 3),
    DirectSum.of _ 5 (rawPowerSum Q D 4)]

/-- Rational polynomial evaluation in the genuine commutative even de Rham
direct sum. -/
noncomputable def evaluate
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    DimensionElevenTwelveDensity.P →+* Total (E := E) (M := M) :=
  MvPolynomial.eval₂Hom rationalConstants (traceVariables Q D)

/-- The old four slots are `u,tr(F_T²),tr(F_T⁴),tr(F_T⁶)`;
in the six-variable convention they are `u,-2p₁,2p₂,-2p₃`.
This is a polynomial substitution, independent of curvature geometry. -/
noncomputable def fourToSix : MvPolynomial (Fin 4) ℚ →+*
    DimensionElevenTwelveDensity.P :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![u, -2 * p1, 2 * p2, -2 * p3]

omit [Nontrivial E] in
private theorem rawPowerSum_zero
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    (-2 : ℝ) • rawPowerSum Q D 0 = tangentTraceClass Q D 1 := by
  norm_num [rawPowerSum, castClass, smul_smul]

omit [Nontrivial E] in
private theorem rawPowerSum_one
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    (2 : ℝ) • rawPowerSum Q D 1 = tangentTraceClass Q D 3 := by
  norm_num [rawPowerSum, castClass, smul_smul]

omit [Nontrivial E] in
private theorem rawPowerSum_two
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    (-2 : ℝ) • rawPowerSum Q D 2 = tangentTraceClass Q D 5 := by
  norm_num [rawPowerSum, castClass, smul_smul]

/-- The earlier four-generator semantics is exactly the restriction of the
six-variable semantics under the displayed normalization. -/
theorem fourToSix_evaluation
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (P : MvPolynomial (Fin 4) ℚ) :
    evaluate Q D (fourToSix P) =
      EvenExpr.polynomialEvaluation (rawU Q D) (tangentTraceClass Q D 1)
        (tangentTraceClass Q D 3) (tangentTraceClass Q D 5) P := by
  have h : (evaluate Q D).comp fourToSix =
      EvenExpr.polynomialEvaluation (rawU Q D) (tangentTraceClass Q D 1)
        (tangentTraceClass Q D 3) (tangentTraceClass Q D 5) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [evaluate, fourToSix, EvenExpr.polynomialEvaluation,
        MvPolynomial.eval₂Hom_C]
    · intro i
      fin_cases i <;>
        simp only [fourToSix, evaluate, DimensionElevenTwelveDensity.u,
          p1, p2, p3, traceVariables, EvenExpr.polynomialEvaluation,
          EvenExpr.generatorValues, MvPolynomial.eval₂Hom_X']
      all_goals simp [two_mul, ← map_add, ← map_neg]
      all_goals congr 1
      · simpa [two_smul, neg_smul] using rawPowerSum_zero Q D
      · simpa [two_smul] using rawPowerSum_one Q D
      · simpa [two_smul, neg_smul] using rawPowerSum_two Q D
  exact RingHom.congr_fun h P

/-- On every expression in the prior four-generator language, the new
six-variable polynomial evaluation and the previous typed evaluation yield
the same actual homogeneous class. -/
theorem fourToSix_evenExpr
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (P : EvenExpr n) :
    evaluate Q D (fourToSix P.polynomial) =
      DirectSum.of (Grade (E := E) (M := M)) n
        (EvenExpr.evaluate (rawU Q D) (tangentTraceClass Q D 1)
          (tangentTraceClass Q D 3) (tangentTraceClass Q D 5) P) := by
  rw [fourToSix_evaluation]
  exact (EvenExpr.evaluation_sound _ _ _ _ P).symm

/-- The actual degree `4*n` cohomology component of a six-variable
polynomial. This definition makes sense even before establishing a polynomial
is weighted homogeneous. -/
noncomputable def homogeneousClass
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (n : ℕ) (P : DimensionElevenTwelveDensity.P) : Grade (E := E) (M := M) n :=
  DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) n (evaluate Q D P)

/-- The two certificate identities first transport to the complete graded
de Rham algebra, before projection to their geometric degrees. -/
theorem density11_printed_total
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    evaluate Q D density11 = evaluate Q D printed11 :=
  congrArg (evaluate Q D) density11_printed

theorem density12_printed_total
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    evaluate Q D density12 = evaluate Q D printed12 :=
  congrArg (evaluate Q D) density12_printed

theorem density11_printed_class
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    homogeneousClass Q D 11 density11 = homogeneousClass Q D 11 printed11 := by
  unfold homogeneousClass
  exact congrArg _ (density11_printed_total Q D)

theorem density12_printed_class
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    homogeneousClass Q D 12 density12 = homogeneousClass Q D 12 printed12 := by
  unfold homogeneousClass
  exact congrArg _ (density12_printed_total Q D)

omit [Nontrivial E] in
theorem rawPowerSum_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (j : ℕ) : rawPowerSum Q D₁ j = rawPowerSum Q D₀ j := by
  unfold rawPowerSum
  simp only [tangentTraceClass_connection_independent Q D₀ D₁]

theorem rawU_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    rawU Q D₁ = rawU Q D₀ :=
  traceCurvatureSquareClass_eq Q D₀ D₁

theorem traceVariables_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    traceVariables Q D₁ = traceVariables Q D₀ := by
  simp [traceVariables, rawU_connection_independent Q D₀ D₁,
    rawPowerSum_connection_independent Q D₀ D₁]

theorem evaluate_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (P : DimensionElevenTwelveDensity.P) : evaluate Q D₁ P = evaluate Q D₀ P := by
  simp only [evaluate, traceVariables_connection_independent Q D₀ D₁]

theorem homogeneousClass_connection_independent
    (D₀ D₁ : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (n : ℕ) (P : DimensionElevenTwelveDensity.P) :
    homogeneousClass Q D₁ n P = homogeneousClass Q D₀ n P := by
  simp only [homogeneousClass, evaluate_connection_independent Q D₀ D₁]

end QuaternionicSymmetry.ManifoldSixVariableDensityEvaluation
