import QuaternionicSymmetry.PrintedTwoSixLinearAssembly
import QuaternionicSymmetry.QuaternionicZeroBlockPadding

/-! The three nonconstant first/second-moment terms of the printed
quaternionic dimension-five and dimension-six certificates. -/
namespace QuaternionicSymmetry.QuaternionicFiveSixPointwise
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  PrintedGaussianProjectionPositivity QuaternionicZeroBlockPadding
  PrintedProjectionCubicPositivity ElevenTwelveProjectionCertificates
  DimensionElevenTwelveDensity
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

private theorem eval_mul_u {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) (p : DimensionElevenTwelveDensity.P) (j : ℕ) :
    aeval v (p * u ^ j) = aeval v p * v 0 ^ j := by
  simp only [map_mul, map_pow, u, aeval_X]

def generators5 : Fin 3 → DimensionElevenTwelveDensity.P := ![
  m1Full * u ^ 4, m2Full * u ^ 3, m2One 12 * u ^ 3]
def generators6 : Fin 3 → DimensionElevenTwelveDensity.P := ![
  m1Full * u ^ 5, m2Full * u ^ 4, m2One 14 * u ^ 4]

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem generators5_in_positive_ray
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 5)
    (B : β → Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (i : Fin 3) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (generators5 i)) := by
  have hP : ∀ b, (padTwo (B b)).IsHermitian := fun b => padTwo_isHermitian _ (hB b)
  have h0 := m1_mixed_in_positive_ray Q c B hB η hη (by omega)
  have h1 := m2Full_mixed_in_positive_ray Q c B hB η hη (by omega)
  have h2 := m2One_mixed_in_positive_ray Q c (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h2
  norm_num only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at h2
  fin_cases i
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m1Full * u ^ 4))
    rw [eval_mul_u]
    simpa only [hn] using h0
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2Full * u ^ 3))
    rw [eval_mul_u]
    simpa only [hn] using h1
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2One 12 * u ^ 3))
    rw [eval_mul_u]
    simpa only [hn] using h2

theorem generators6_in_positive_ray
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 6)
    (B : β → Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (i : Fin 3) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (generators6 i)) := by
  have hP : ∀ b, (padTwo (B b)).IsHermitian := fun b => padTwo_isHermitian _ (hB b)
  have h0 := m1_mixed_in_positive_ray Q c B hB η hη (by omega)
  have h1 := m2Full_mixed_in_positive_ray Q c B hB η hη (by omega)
  have h2 := m2One_mixed_in_positive_ray Q c (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h2
  norm_num only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at h2
  fin_cases i
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m1Full * u ^ 5))
    rw [eval_mul_u]
    simpa only [hn] using h0
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2Full * u ^ 4))
    rw [eval_mul_u]
    simpa only [hn] using h1
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2One 14 * u ^ 4))
    rw [eval_mul_u]
    simpa only [hn] using h2

end
end QuaternionicSymmetry.QuaternionicFiveSixPointwise
