import QuaternionicSymmetry.PrintedTwoSixMomentAssembly
import QuaternionicSymmetry.QuaternionicSevenTenDensityBound

/-! Actual pointwise functional lower bounds for the printed densities
through quaternionic dimension six. -/
namespace QuaternionicSymmetry.QuaternionicTwoSixDensityBound
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  PrintedGaussianProjectionPositivity PrintedProjectionCubicPositivity
  QuaternionicFiveSixPointwise
  PrintedTwoSixMomentAssembly PrintedTwoSixLinearAssembly
  ReconstructionExamples DimensionElevenTwelveDensity
  QuaternionicSevenTenDensityBound
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [DecidableEq β] [FiniteDimensional ℝ V] in
private theorem eval_u_pow (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : β → Matrix κ κ ℂ) (η : β → E V) (n : ℕ) :
    aeval (densityValues Q c B η) (u ^ n) = embed (V := V) (form Q c) ^ n := by
  simp only [map_pow, u, aeval_X]
  rfl

private theorem eval_mul_u {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) (p : DimensionElevenTwelveDensity.P) (j : ℕ) :
    aeval v (p * u ^ j) = aeval v p * v 0 ^ j := by
  simp only [map_mul, map_pow, u, aeval_X]

theorem density5_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 5)
    (B : β → Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    72 * L (embed (V := V) (form Q c) ^ 5) ≤
      L (aeval (densityValues Q c B η) k5) := by
  have hg (i : Fin 3) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators5 i) :=
    PositiveRay.functional_nonneg
      (generators5_in_positive_ray Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 3, (coefficients5 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators5 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients5_nonneg i) (hg i)
  have he := linear_density5 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith

theorem density6_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 6)
    (B : β → Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    96 * L (embed (V := V) (form Q c) ^ 6) ≤
      L (aeval (densityValues Q c B η) k6) := by
  have hg (i : Fin 3) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators6 i) :=
    PositiveRay.functional_nonneg
      (generators6_in_positive_ray Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 3, (coefficients6 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators6 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients6_nonneg i) (hg i)
  have he := linear_density6 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith


omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem density2_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)
    (η : β → E V) (L : CE V →ₗ[ℝ] ℝ) :
    16 * L (embed (V := V) (form Q c) ^ 2) ≤
      L (aeval (densityValues Q c B η) density2) := by
  have he := linear_density2 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he
  linarith

theorem density3_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 3)
    (B : β → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    32 * L (embed (V := V) (form Q c) ^ 3) ≤
      L (aeval (densityValues Q c B η) density3) := by
  have hm := m1_mixed_in_positive_ray Q c B hB η hη (by omega)
  have hmg : PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (ElevenTwelveProjectionCertificates.m1Full*u^2)) := by
    rw [eval_mul_u]
    simpa only [hn] using hm
  have hg : 0 ≤ evaluatedFunctional (densityValues Q c B η) L
      (ElevenTwelveProjectionCertificates.m1Full*u^2) :=
    PositiveRay.functional_nonneg hmg L hL
  have he := linear_density3 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hg
  linarith

theorem density4_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 4)
    (B : β → Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    48 * L (embed (V := V) (form Q c) ^ 4) ≤
      L (aeval (densityValues Q c B η) density4) := by
  have hm := m1_mixed_in_positive_ray Q c B hB η hη (by omega)
  have hmg : PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (ElevenTwelveProjectionCertificates.m1Full*u^3)) := by
    rw [eval_mul_u]
    simpa only [hn] using hm
  have hg : 0 ≤ evaluatedFunctional (densityValues Q c B η) L
      (ElevenTwelveProjectionCertificates.m1Full*u^3) :=
    PositiveRay.functional_nonneg hmg L hL
  have he := linear_density4 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hg
  linarith

end
end QuaternionicSymmetry.QuaternionicTwoSixDensityBound
