import QuaternionicSymmetry.QuaternionicTangentRootConversion
import QuaternionicSymmetry.ManifoldSevenVariableCurvatureEvaluation
import QuaternionicSymmetry.ManifoldSixVariableScaledDensity

/-!
Analytic de Rham candidates obtained by the exact finite tangent-root
conversion. The coefficient `(2π)^(-2j)` converts the raw tangent curvature
trace to the normalized `iF/(2π)` root convention, including its `(-1)^j`
sign already present in `rawPowerSum`. The rank-three coefficient
`-1/(32π²)` is the analytic candidate for `u=p₁(Q)/4`.

Identifying these recovered classes with the Chern–Weil classes of the
locally descended corrected standard connection still requires the geometric
comparison of invariant connections. In particular the formal root identity
does not describe the pointwise spectrum of the corrected Weyl curvature.
-/

namespace QuaternionicSymmetry.ManifoldTangentTraceRootCandidates

set_option linter.unusedSectionVars false

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldSixVariableDensityEvaluation
  QuaternionicSymmetry.ManifoldSixVariableScaledDensity
  QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation
  QuaternionicSymmetry.ManifoldSevenVariableCurvatureEvaluation
  QuaternionicSymmetry.QuaternionicTangentRootConversion
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- Coefficient converting the raw `(-1)^j tr(F_T^(2j))/2` class to
the half trace of normalized tangent roots of `X_T=iF_T/(2π)`. -/
noncomputable def tangentTraceScale (j : ℕ) : ℝ :=
  1 / (2 * Real.pi) ^ (2 * j)

/-- The analytic degree-four candidate for `u=p₁(Q)/4`. -/
noncomputable def quarterUClass : Grade (E := E) (M := M) 1 :=
  quarterPontryaginTraceScale • rawU Q D

noncomputable def quarterUTotal : Total (E := E) (M := M) :=
  DirectSum.of (Grade (E := E) (M := M)) 1 (quarterUClass Q D)

/-- The normalized tangent half-trace classes. The zero-power value is
`2n`; positive powers are the actual global trace-form classes. -/
noncomputable def normalizedTangentHalfTrace (qdim : ℕ) : ℕ →
    Total (E := E) (M := M)
  | 0 => rationalConstants (2 * qdim)
  | j + 1 => DirectSum.of (Grade (E := E) (M := M)) (j + 1)
      (tangentTraceScale (j + 1) • rawPowerSum Q D j)

/-- Algebra structure induced by the actual constant-class ring map. It
need not be faithful on an empty manifold. -/
noncomputable def rationalAlgebra : Algebra ℚ (Total (E := E) (M := M)) :=
  (rationalConstants (E := E) (M := M)).toAlgebra

noncomputable local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  rationalAlgebra (E := E) (M := M)

/-- Triangularly recovered analytic candidate for the paper's corrected
standard-bundle power sum `p_j`, for `0≤j≤6`. -/
noncomputable def candidatePower (qdim : ℕ) (j : Fin 7) :
    Total (E := E) (M := M) :=
  recoveredStandardPower qdim (quarterUTotal Q D)
    (normalizedTangentHalfTrace Q D qdim) j

private def PureGrade (k : ℕ) (z : Total (E := E) (M := M)) : Prop :=
  ∃ a : Grade (E := E) (M := M) k,
    z = DirectSum.of (Grade (E := E) (M := M)) k a

private theorem pure_add {k : ℕ} {z w : Total (E := E) (M := M)}
    (hz : PureGrade k z) (hw : PureGrade k w) : PureGrade k (z + w) := by
  rcases hz with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  exact ⟨a + b, by simp⟩

private theorem pure_neg {k : ℕ} {z : Total (E := E) (M := M)}
    (hz : PureGrade k z) : PureGrade k (-z) := by
  rcases hz with ⟨a, rfl⟩
  exact ⟨-a, by simp⟩

private theorem pure_sub {k : ℕ} {z w : Total (E := E) (M := M)}
    (hz : PureGrade k z) (hw : PureGrade k w) : PureGrade k (z - w) := by
  simpa only [sub_eq_add_neg] using pure_add hz (pure_neg hw)

private theorem pure_mul {j k : ℕ} {z w : Total (E := E) (M := M)}
    (hz : PureGrade j z) (hw : PureGrade k w) : PureGrade (j + k) (z * w) := by
  rcases hz with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  exact ⟨gradeMul j k a b, DirectSum.of_mul_of a b⟩

private theorem pure_pow {j : ℕ} {z : Total (E := E) (M := M)}
    (hz : PureGrade j z) (k : ℕ) : PureGrade (k * j) (z ^ k) := by
  rcases hz with ⟨a, rfl⟩
  refine ⟨GradedMonoid.GMonoid.gnpow k a, ?_⟩
  simpa only [nsmul_eq_mul] using
    (DirectSum.ofPow (Grade (E := E) (M := M)) a k)

private theorem pure_u : PureGrade 1 (quarterUTotal Q D) :=
  ⟨quarterUClass Q D, rfl⟩

private theorem pure_tangent (qdim j : ℕ) :
    PureGrade (j + 1) (normalizedTangentHalfTrace Q D qdim (j + 1)) :=
  ⟨tangentTraceScale (j + 1) • rawPowerSum Q D j, rfl⟩

private theorem pure_rational (q : ℚ) :
    PureGrade 0 (rationalConstants (E := E) (M := M) q) :=
  ⟨(q : ℝ), rfl⟩

private theorem pure_nat (n : ℕ) :
    PureGrade 0 (n : Total (E := E) (M := M)) := by
  simpa only [map_natCast] using pure_rational (E := E) (M := M) (n : ℚ)

private theorem pure_half :
    PureGrade 0 (half (R := Total (E := E) (M := M))) := by
  dsimp [half]
  change PureGrade 0 ((rationalConstants (E := E) (M := M)) (1 / 2))
  exact pure_rational (E := E) (M := M) (1 / 2)

private theorem pure_u_pow (j : ℕ) :
    PureGrade j ((quarterUTotal Q D) ^ j) := by
  simpa only [Nat.mul_one] using pure_pow (pure_u Q D) j

private theorem pure_half_tangent (qdim j : ℕ) :
    PureGrade (j + 1)
      (half * normalizedTangentHalfTrace Q D qdim (j + 1)) := by
  simpa only [Nat.zero_add] using
    pure_mul (pure_half (E := E) (M := M)) (pure_tangent Q D qdim j)

private theorem pure_nat_u_pow (qdim j : ℕ) :
    PureGrade j
      ((qdim : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ j) := by
  simpa only [Nat.zero_add] using
    pure_mul (pure_nat (E := E) (M := M) qdim) (pure_u_pow Q D j)

private theorem pure_coefficient_term (c a b : ℕ)
    (q : Total (E := E) (M := M)) (hq : PureGrade b q) :
    PureGrade (a + b)
      ((c : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ a * q) := by
  have hcu : PureGrade a
      ((c : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ a) := by
    simpa only [Nat.zero_add] using
      pure_mul (pure_nat (E := E) (M := M) c) (pure_u_pow Q D a)
  exact pure_mul hcu hq

private theorem pure_recoveredQ1 (qdim : ℕ) :
    PureGrade 1 (recoveredQ1 qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) := by
  unfold recoveredQ1
  simpa using pure_sub (pure_half_tangent Q D qdim 0)
    (pure_nat_u_pow Q D qdim 1)

private theorem pure_recoveredQ2 (qdim : ℕ) :
    PureGrade 2 (recoveredQ2 qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) := by
  unfold recoveredQ2
  have h1 := pure_sub (pure_half_tangent Q D qdim 1)
    (pure_nat_u_pow Q D qdim 2)
  have h2 := pure_coefficient_term Q D 6 1 1 _ (pure_recoveredQ1 Q D qdim)
  simpa using pure_sub h1 h2

private theorem pure_recoveredQ3 (qdim : ℕ) :
    PureGrade 3 (recoveredQ3 qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) := by
  unfold recoveredQ3
  have h0 := pure_sub (pure_half_tangent Q D qdim 2)
    (pure_nat_u_pow Q D qdim 3)
  have ht1 : PureGrade 3
      ((15 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 2 *
        recoveredQ1 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 15 2 1 _
      (pure_recoveredQ1 Q D qdim)
  have ht2 : PureGrade 3
      ((15 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 1 *
        recoveredQ2 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 15 1 2 _
      (pure_recoveredQ2 Q D qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  simpa using hs2

private theorem pure_recoveredQ4 (qdim : ℕ) :
    PureGrade 4 (recoveredQ4 qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) := by
  unfold recoveredQ4
  have h0 := pure_sub (pure_half_tangent Q D qdim 3)
    (pure_nat_u_pow Q D qdim 4)
  have ht1 : PureGrade 4
      ((28 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 3 *
        recoveredQ1 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 28 3 1 _
      (pure_recoveredQ1 Q D qdim)
  have ht2 : PureGrade 4
      ((70 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 2 *
        recoveredQ2 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 70 2 2 _
      (pure_recoveredQ2 Q D qdim)
  have ht3 : PureGrade 4
      ((28 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 1 *
        recoveredQ3 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 28 1 3 _
      (pure_recoveredQ3 Q D qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  have hs3 := pure_sub hs2 ht3
  simpa using hs3

private theorem pure_recoveredQ5 (qdim : ℕ) :
    PureGrade 5 (recoveredQ5 qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) := by
  unfold recoveredQ5
  have h0 := pure_sub (pure_half_tangent Q D qdim 4)
    (pure_nat_u_pow Q D qdim 5)
  have ht1 : PureGrade 5
      ((45 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 4 *
        recoveredQ1 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 45 4 1 _
      (pure_recoveredQ1 Q D qdim)
  have ht2 : PureGrade 5
      ((210 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 3 *
        recoveredQ2 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 210 3 2 _
      (pure_recoveredQ2 Q D qdim)
  have ht3 : PureGrade 5
      ((210 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 2 *
        recoveredQ3 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 210 2 3 _
      (pure_recoveredQ3 Q D qdim)
  have ht4 : PureGrade 5
      ((45 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 1 *
        recoveredQ4 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 45 1 4 _
      (pure_recoveredQ4 Q D qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  have hs3 := pure_sub hs2 ht3
  have hs4 := pure_sub hs3 ht4
  simpa using hs4

private theorem pure_recoveredQ6 (qdim : ℕ) :
    PureGrade 6 (recoveredQ6 qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) := by
  unfold recoveredQ6
  have h0 := pure_sub (pure_half_tangent Q D qdim 5)
    (pure_nat_u_pow Q D qdim 6)
  have ht1 : PureGrade 6
      ((66 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 5 *
        recoveredQ1 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 66 5 1 _
      (pure_recoveredQ1 Q D qdim)
  have ht2 : PureGrade 6
      ((495 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 4 *
        recoveredQ2 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 495 4 2 _
      (pure_recoveredQ2 Q D qdim)
  have ht3 : PureGrade 6
      ((924 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 3 *
        recoveredQ3 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 924 3 3 _
      (pure_recoveredQ3 Q D qdim)
  have ht4 : PureGrade 6
      ((495 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 2 *
        recoveredQ4 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 495 2 4 _
      (pure_recoveredQ4 Q D qdim)
  have ht5 : PureGrade 6
      ((66 : Total (E := E) (M := M)) * (quarterUTotal Q D) ^ 1 *
        recoveredQ5 qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) := by
    simpa using pure_coefficient_term Q D 66 1 5 _
      (pure_recoveredQ5 Q D qdim)
  have hs1 := pure_sub h0 ht1
  have hs2 := pure_sub hs1 ht2
  have hs3 := pure_sub hs2 ht3
  have hs4 := pure_sub hs3 ht4
  have hs5 := pure_sub hs4 ht5
  simpa using hs5

private theorem pure_recoveredSymplecticPowers (qdim : ℕ) (j : Fin 7) :
    PureGrade j.val
      (recoveredSymplecticPowers qdim (quarterUTotal Q D)
        (normalizedTangentHalfTrace Q D qdim) j) := by
  fin_cases j
  · exact pure_nat (E := E) (M := M) qdim
  · exact pure_recoveredQ1 Q D qdim
  · exact pure_recoveredQ2 Q D qdim
  · exact pure_recoveredQ3 Q D qdim
  · exact pure_recoveredQ4 Q D qdim
  · exact pure_recoveredQ5 Q D qdim
  · exact pure_recoveredQ6 Q D qdim

private theorem pure_sign (j : ℕ) :
    PureGrade 0 ((-1 : Total (E := E) (M := M)) ^ j) := by
  have hneg : PureGrade 0 (-1 : Total (E := E) (M := M)) := by
    simpa using pure_neg (pure_nat (E := E) (M := M) 1)
  simpa only [Nat.mul_zero] using pure_pow hneg j

/-- Every recovered analytic standard power sum through weight six lies
entirely in its expected actual de Rham degree `4j`. -/
theorem candidatePower_pure_grade (qdim : ℕ) (j : Fin 7) :
    PureGrade j.val (candidatePower Q D qdim j) := by
  unfold candidatePower recoveredStandardPower
  have hsum := pure_add (pure_recoveredSymplecticPowers Q D qdim j)
    (pure_u_pow Q D j.val)
  simpa only [Nat.zero_add] using
    pure_mul (pure_sign (E := E) (M := M) j.val) hsum

/-- The homogeneous class recovered from the normalized curvature traces. -/
noncomputable def candidatePowerClass (qdim : ℕ) (j : Fin 7) :
    Grade (E := E) (M := M) j.val :=
  (candidatePower_pure_grade Q D qdim j).choose

theorem candidatePower_eq_of_class (qdim : ℕ) (j : Fin 7) :
    candidatePower Q D qdim j =
      DirectSum.of (Grade (E := E) (M := M)) j.val
        (candidatePowerClass Q D qdim j) :=
  (candidatePower_pure_grade Q D qdim j).choose_spec

theorem quarterUClass_connection_independent
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    quarterUClass Q D' = quarterUClass Q D := by
  simp [quarterUClass, rawU_connection_independent Q D D']

theorem quarterUTotal_connection_independent
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    quarterUTotal Q D' = quarterUTotal Q D := by
  simp [quarterUTotal, quarterUClass_connection_independent Q D D']

theorem normalizedTangentHalfTrace_connection_independent (qdim : ℕ)
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    normalizedTangentHalfTrace Q D' qdim =
      normalizedTangentHalfTrace Q D qdim := by
  funext j
  cases j with
  | zero => rfl
  | succ k =>
      simp [normalizedTangentHalfTrace,
        rawPowerSum_connection_independent Q D D' k]

theorem candidatePower_connection_independent (qdim : ℕ) (j : Fin 7)
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    candidatePower Q D' qdim j = candidatePower Q D qdim j := by
  simp only [candidatePower, quarterUTotal_connection_independent Q D D',
    normalizedTangentHalfTrace_connection_independent Q D qdim D']

theorem candidatePowerClass_connection_independent (qdim : ℕ) (j : Fin 7)
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    candidatePowerClass Q D' qdim j = candidatePowerClass Q D qdim j := by
  have hD' := candidatePower_eq_of_class Q D' qdim j
  have hD := candidatePower_eq_of_class Q D qdim j
  rw [candidatePower_connection_independent Q D qdim j D', hD] at hD'
  exact (DirectSum.of_injective j.val) hD'.symm

/-- The recovered analytic `u,p₁,…,p₆` assignment in genuine de Rham
degrees 4,4,8,12,16,20,24. -/
noncomputable def candidateGenerators (qdim : ℕ) : Generators (E := E) (M := M) where
  u := quarterUClass Q D
  p1 := candidatePowerClass Q D qdim 1
  p2 := candidatePowerClass Q D qdim 2
  p3 := candidatePowerClass Q D qdim 3
  p4 := candidatePowerClass Q D qdim 4
  p5 := candidatePowerClass Q D qdim 5
  p6 := candidatePowerClass Q D qdim 6

theorem candidateGenerators_connection_independent (qdim : ℕ)
    (D' : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q) :
    candidateGenerators Q D' qdim = candidateGenerators Q D qdim := by
  simp [candidateGenerators, quarterUClass_connection_independent Q D D',
    candidatePowerClass_connection_independent Q D qdim 1 D',
    candidatePowerClass_connection_independent Q D qdim 2 D',
    candidatePowerClass_connection_independent Q D qdim 3 D',
    candidatePowerClass_connection_independent Q D qdim 4 D',
    candidatePowerClass_connection_independent Q D qdim 5 D',
    candidatePowerClass_connection_independent Q D qdim 6 D']

end QuaternionicSymmetry.ManifoldTangentTraceRootCandidates
