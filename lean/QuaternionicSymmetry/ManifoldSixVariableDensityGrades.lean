import QuaternionicSymmetry.ManifoldSixVariableDensityEvaluation

/-! Finite grading certificates for the printed six-variable densities. -/

namespace QuaternionicSymmetry.ManifoldSixVariableDensityGrades

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldSixVariableDensityEvaluation
  QuaternionicSymmetry.DimensionElevenTwelveDensity
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- Evaluation has a single graded component. -/
private def HasGrade (n : ℕ) (P : DimensionElevenTwelveDensity.P) : Prop :=
  ∃ a : Grade (E := E) (M := M) n,
    evaluate Q D P = DirectSum.of (Grade (E := E) (M := M)) n a

private theorem hasGrade_add {n : ℕ} {P R : DimensionElevenTwelveDensity.P}
    (hP : HasGrade Q D n P) (hR : HasGrade Q D n R) :
    HasGrade Q D n (P + R) := by
  rcases hP with ⟨a, ha⟩
  rcases hR with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  simp [ha, hb]

private theorem hasGrade_mul {m n : ℕ} {P R : DimensionElevenTwelveDensity.P}
    (hP : HasGrade Q D m P) (hR : HasGrade Q D n R) :
    HasGrade Q D (m + n) (P * R) := by
  rcases hP with ⟨a, ha⟩
  rcases hR with ⟨b, hb⟩
  refine ⟨gradeMul m n a b, ?_⟩
  simp only [map_mul, ha, hb]
  exact DirectSum.of_mul_of a b

private theorem hasGrade_pow {m : ℕ} {P : DimensionElevenTwelveDensity.P}
    (hP : HasGrade Q D m P) (k : ℕ) :
    HasGrade Q D (k * m) (P ^ k) := by
  rcases hP with ⟨a, ha⟩
  refine ⟨GradedMonoid.GMonoid.gnpow k a, ?_⟩
  simp only [map_pow, ha]
  simpa only [nsmul_eq_mul] using
    (DirectSum.ofPow (Grade (E := E) (M := M)) a k)

private theorem hasGrade_C (q : ℚ) :
    HasGrade Q D 0 (MvPolynomial.C q) := by
  refine ⟨(q : ℝ), ?_⟩
  simp only [evaluate, MvPolynomial.eval₂Hom_C, rationalConstants,
    RingHom.comp_apply]
  rfl

private theorem hasGrade_C_mul {n : ℕ} (q : ℚ)
    {P : DimensionElevenTwelveDensity.P} (hP : HasGrade Q D n P) :
    HasGrade Q D n (MvPolynomial.C q * P) := by
  simpa only [Nat.zero_add] using
    (hasGrade_mul Q D (hasGrade_C Q D q) hP)

private theorem hasGrade_u : HasGrade Q D 1 u := by
  refine ⟨ManifoldSixVariableDensityEvaluation.rawU Q D, ?_⟩
  simp [evaluate, u, traceVariables]

private theorem hasGrade_p1 : HasGrade Q D 1 p1 := by
  refine ⟨ManifoldSixVariableDensityEvaluation.rawPowerSum Q D 0, ?_⟩
  simp [evaluate, p1, traceVariables]

private theorem hasGrade_p2 : HasGrade Q D 2 p2 := by
  refine ⟨ManifoldSixVariableDensityEvaluation.rawPowerSum Q D 1, ?_⟩
  simp [evaluate, p2, traceVariables]

private theorem hasGrade_p3 : HasGrade Q D 3 p3 := by
  refine ⟨ManifoldSixVariableDensityEvaluation.rawPowerSum Q D 2, ?_⟩
  simp [evaluate, p3, traceVariables]

private theorem hasGrade_p4 : HasGrade Q D 4 p4 := by
  refine ⟨ManifoldSixVariableDensityEvaluation.rawPowerSum Q D 3, ?_⟩
  simp [evaluate, p4, traceVariables]

private theorem hasGrade_p5 : HasGrade Q D 5 p5 := by
  refine ⟨ManifoldSixVariableDensityEvaluation.rawPowerSum Q D 4, ?_⟩
  simp [evaluate, p5, traceVariables]

private theorem hasGrade_mul' {m n k : ℕ} {P R : DimensionElevenTwelveDensity.P}
    (h : m + n = k) (hP : HasGrade Q D m P) (hR : HasGrade Q D n R) :
    HasGrade Q D k (P * R) := by
  subst k
  exact hasGrade_mul Q D hP hR

private theorem hasGrade_pow' {m k n : ℕ} {P : DimensionElevenTwelveDensity.P}
    (h : k * m = n) (hP : HasGrade Q D m P) :
    HasGrade Q D n (P ^ k) := by
  subst n
  exact hasGrade_pow Q D hP k

private theorem hasGrade_q11 : HasGrade Q D 4 q11 := by
  have hp1 := hasGrade_p1 Q D
  have hp2 := hasGrade_p2 Q D
  have hp3 := hasGrade_p3 Q D
  have hp4 := hasGrade_p4 Q D
  have hp1sq : HasGrade Q D 2 (p1 ^ 2) :=
    hasGrade_pow' Q D (m := 1) (k := 2) (n := 2) (by decide) hp1
  have h1 : HasGrade Q D 4 (MvPolynomial.C 8470 * p1 ^ 4) :=
    hasGrade_C_mul Q D _ (hasGrade_pow' Q D (by decide) hp1)
  have h2 : HasGrade Q D 4 (MvPolynomial.C 9207 * p1 ^ 2 * p2) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ hp1sq) hp2
  have h3 : HasGrade Q D 4 (MvPolynomial.C 825 * p2 ^ 2) :=
    hasGrade_C_mul Q D _ (hasGrade_pow' Q D (by decide) hp2)
  have h4 : HasGrade Q D 4 (MvPolynomial.C 2882 * p1 * p3) :=
    hasGrade_mul' Q D (by decide) (hasGrade_C_mul Q D _ hp1) hp3
  have h5 : HasGrade Q D 4 (MvPolynomial.C 450 * p4) :=
    hasGrade_C_mul Q D _ hp4
  simpa only [q11] using (hasGrade_C_mul Q D _
    (hasGrade_add Q D (hasGrade_add Q D
      (hasGrade_add Q D (hasGrade_add Q D h1 h2) h3) h4) h5)
    : HasGrade Q D 4 (MvPolynomial.C (4 / 1403325 : ℚ) *
        (MvPolynomial.C 8470 * p1 ^ 4 + MvPolynomial.C 9207 * p1 ^ 2 * p2 +
         MvPolynomial.C 825 * p2 ^ 2 + MvPolynomial.C 2882 * p1 * p3 +
         MvPolynomial.C 450 * p4)))

private theorem hasGrade_q12 : HasGrade Q D 4 q12 := by
  have hp1 := hasGrade_p1 Q D
  have hp2 := hasGrade_p2 Q D
  have hp3 := hasGrade_p3 Q D
  have hp4 := hasGrade_p4 Q D
  have hp1sq : HasGrade Q D 2 (p1 ^ 2) :=
    hasGrade_pow' Q D (m := 1) (k := 2) (n := 2) (by decide) hp1
  have h1 : HasGrade Q D 4 (MvPolynomial.C (146 / 3645 : ℚ) * p1 ^ 4) :=
    hasGrade_C_mul Q D _ (hasGrade_pow' Q D (by decide) hp1)
  have h2 : HasGrade Q D 4 (MvPolynomial.C (604 / 14175 : ℚ) * p1 ^ 2 * p2) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ hp1sq) hp2
  have h3 : HasGrade Q D 4 (MvPolynomial.C (158 / 42525 : ℚ) * p2 ^ 2) :=
    hasGrade_C_mul Q D _ (hasGrade_pow' Q D (by decide) hp2)
  have h4 : HasGrade Q D 4 (MvPolynomial.C (1616 / 127575 : ℚ) * p1 * p3) :=
    hasGrade_mul' Q D (by decide) (hasGrade_C_mul Q D _ hp1) hp3
  have h5 : HasGrade Q D 4 (MvPolynomial.C (268 / 155925 : ℚ) * p4) :=
    hasGrade_C_mul Q D _ hp4
  simpa only [q12] using (hasGrade_add Q D (hasGrade_add Q D
    (hasGrade_add Q D (hasGrade_add Q D h1 h2) h3) h4) h5)

private theorem hasGrade_u_pow (k : ℕ) : HasGrade Q D k (u ^ k) := by
  simpa only [Nat.mul_one] using hasGrade_pow Q D (hasGrade_u Q D) k

private theorem hasGrade_p1_pow (k : ℕ) : HasGrade Q D k (p1 ^ k) := by
  simpa only [Nat.mul_one] using hasGrade_pow Q D (hasGrade_p1 Q D) k

private theorem hasGrade_f5 : HasGrade Q D 5 f5 := by
  have h1 : HasGrade Q D 5 (MvPolynomial.C 385 * p1 ^ 5) :=
    hasGrade_C_mul Q D _ (hasGrade_p1_pow Q D 5)
  have h2 : HasGrade Q D 5 (MvPolynomial.C 770 * p1 ^ 3 * p2) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ (hasGrade_p1_pow Q D 3)) (hasGrade_p2 Q D)
  have h3 : HasGrade Q D 5 (MvPolynomial.C 440 * p1 ^ 2 * p3) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ (hasGrade_p1_pow Q D 2)) (hasGrade_p3 Q D)
  have h4 : HasGrade Q D 5 (MvPolynomial.C 231 * p1 * p2 ^ 2) :=
    hasGrade_mul' Q D (by decide) (hasGrade_C_mul Q D _ (hasGrade_p1 Q D))
      (hasGrade_pow' Q D (m := 2) (k := 2) (n := 4) (by decide)
        (hasGrade_p2 Q D))
  have h5 : HasGrade Q D 5 (MvPolynomial.C 198 * p1 * p4) :=
    hasGrade_mul' Q D (by decide) (hasGrade_C_mul Q D _ (hasGrade_p1 Q D))
      (hasGrade_p4 Q D)
  have h6 : HasGrade Q D 5 (MvPolynomial.C 88 * p2 * p3) :=
    hasGrade_mul' Q D (by decide) (hasGrade_C_mul Q D _ (hasGrade_p2 Q D))
      (hasGrade_p3 Q D)
  have h7 : HasGrade Q D 5 (MvPolynomial.C 48 * p5) :=
    hasGrade_C_mul Q D _ (hasGrade_p5 Q D)
  simpa only [f5] using (hasGrade_C_mul Q D _
    (hasGrade_add Q D (hasGrade_add Q D (hasGrade_add Q D
      (hasGrade_add Q D (hasGrade_add Q D (hasGrade_add Q D h1 h2) h3) h4) h5) h6) h7)
    : HasGrade Q D 5 (MvPolynomial.C (1 / 11496038400 : ℚ) *
       (MvPolynomial.C 385 * p1 ^ 5 + MvPolynomial.C 770 * p1 ^ 3 * p2 +
        MvPolynomial.C 440 * p1 ^ 2 * p3 + MvPolynomial.C 231 * p1 * p2 ^ 2 +
        MvPolynomial.C 198 * p1 * p4 + MvPolynomial.C 88 * p2 * p3 +
        MvPolynomial.C 48 * p5)))

private theorem hasGrade_printed11 : HasGrade Q D 11 printed11 := by
  have h1 : HasGrade Q D 11 (MvPolynomial.C 288 * u ^ 11) :=
    hasGrade_C_mul Q D _ (hasGrade_u_pow Q D 11)
  have h2 : HasGrade Q D 11 (MvPolynomial.C (4965304 / 51975 : ℚ) * p1 * u ^ 10) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ (hasGrade_p1 Q D)) (hasGrade_u_pow Q D 10)
  have h3 : HasGrade Q D 11
      ((MvPolynomial.C (35416 / 2835 : ℚ) * p1 ^ 2 +
        MvPolynomial.C (154736 / 93555 : ℚ) * p2) * u ^ 9) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_add Q D
        (hasGrade_C_mul Q D _ (hasGrade_p1_pow Q D 2))
        (hasGrade_C_mul Q D _ (hasGrade_p2 Q D)))
      (hasGrade_u_pow Q D 9)
  have h4 : HasGrade Q D 11
      ((MvPolynomial.C (33772 / 42525 : ℚ) * p1 ^ 3 +
        MvPolynomial.C (16052 / 42525 : ℚ) * p1 * p2 +
        MvPolynomial.C (18848 / 467775 : ℚ) * p3) * u ^ 8) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_add Q D (hasGrade_add Q D
        (hasGrade_C_mul Q D _ (hasGrade_p1_pow Q D 3))
        (hasGrade_mul' Q D (by decide)
          (hasGrade_C_mul Q D _ (hasGrade_p1 Q D)) (hasGrade_p2 Q D)))
        (hasGrade_C_mul Q D _ (hasGrade_p3 Q D)))
      (hasGrade_u_pow Q D 8)
  have h5 : HasGrade Q D 11 (q11 * u ^ 7) :=
    hasGrade_mul' Q D (by decide) (hasGrade_q11 Q D) (hasGrade_u_pow Q D 7)
  have h6 : HasGrade Q D 11 (MvPolynomial.C 8192 * f5 * u ^ 6) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ (hasGrade_f5 Q D)) (hasGrade_u_pow Q D 6)
  simpa only [printed11] using
    (hasGrade_add Q D (hasGrade_add Q D (hasGrade_add Q D
      (hasGrade_add Q D (hasGrade_add Q D h1 h2) h3) h4) h5) h6)

private theorem hasGrade_printed12 : HasGrade Q D 12 printed12 := by
  have h1 : HasGrade Q D 12 (MvPolynomial.C 336 * u ^ 12) :=
    hasGrade_C_mul Q D _ (hasGrade_u_pow Q D 12)
  have h2 : HasGrade Q D 12 (MvPolynomial.C (6101552 / 51975 : ℚ) * p1 * u ^ 11) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ (hasGrade_p1 Q D)) (hasGrade_u_pow Q D 11)
  have h3 : HasGrade Q D 12
      ((MvPolynomial.C (33368 / 2025 : ℚ) * p1 ^ 2 +
        MvPolynomial.C (962072 / 467775 : ℚ) * p2) * u ^ 10) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_add Q D
        (hasGrade_C_mul Q D _ (hasGrade_p1_pow Q D 2))
        (hasGrade_C_mul Q D _ (hasGrade_p2 Q D)))
      (hasGrade_u_pow Q D 10)
  have h4 : HasGrade Q D 12
      ((MvPolynomial.C (49064 / 42525 : ℚ) * p1 ^ 3 +
        MvPolynomial.C (22408 / 42525 : ℚ) * p1 * p2 +
        MvPolynomial.C (22384 / 467775 : ℚ) * p3) * u ^ 9) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_add Q D (hasGrade_add Q D
        (hasGrade_C_mul Q D _ (hasGrade_p1_pow Q D 3))
        (hasGrade_mul' Q D (by decide)
          (hasGrade_C_mul Q D _ (hasGrade_p1 Q D)) (hasGrade_p2 Q D)))
        (hasGrade_C_mul Q D _ (hasGrade_p3 Q D)))
      (hasGrade_u_pow Q D 9)
  have h5 : HasGrade Q D 12 (q12 * u ^ 8) :=
    hasGrade_mul' Q D (by decide) (hasGrade_q12 Q D) (hasGrade_u_pow Q D 8)
  have h6 : HasGrade Q D 12 (MvPolynomial.C 16384 * f5 * u ^ 7) :=
    hasGrade_mul' Q D (by decide)
      (hasGrade_C_mul Q D _ (hasGrade_f5 Q D)) (hasGrade_u_pow Q D 7)
  simpa only [printed12] using
    (hasGrade_add Q D (hasGrade_add Q D (hasGrade_add Q D
      (hasGrade_add Q D (hasGrade_add Q D h1 h2) h3) h4) h5) h6)

/-- The dimension-eleven printed density is entirely in actual de Rham
degree 44, without a component projection losing any other terms. -/
theorem printed11_pure_grade :
    evaluate Q D printed11 = DirectSum.of (Grade (E := E) (M := M)) 11
      (homogeneousClass Q D 11 printed11) := by
  rcases hasGrade_printed11 Q D with ⟨a, ha⟩
  unfold homogeneousClass
  rw [ha]
  change DirectSum.of _ 11 a = DirectSum.of _ 11 ((DirectSum.of _ 11 a) 11)
  rw [DirectSum.of_eq_same]

/-- The dimension-twelve printed density is entirely in de Rham degree 48. -/
theorem printed12_pure_grade :
    evaluate Q D printed12 = DirectSum.of (Grade (E := E) (M := M)) 12
      (homogeneousClass Q D 12 printed12) := by
  rcases hasGrade_printed12 Q D with ⟨a, ha⟩
  unfold homogeneousClass
  rw [ha]
  change DirectSum.of _ 12 a = DirectSum.of _ 12 ((DirectSum.of _ 12 a) 12)
  rw [DirectSum.of_eq_same]

theorem density11_pure_grade :
    evaluate Q D density11 = DirectSum.of (Grade (E := E) (M := M)) 11
      (homogeneousClass Q D 11 density11) := by
  rw [density11_printed, printed11_pure_grade]

theorem density12_pure_grade :
    evaluate Q D density12 = DirectSum.of (Grade (E := E) (M := M)) 12
      (homogeneousClass Q D 12 density12) := by
  rw [density12_printed, printed12_pure_grade]

end QuaternionicSymmetry.ManifoldSixVariableDensityGrades
