import QuaternionicSymmetry.PrintedSevenTenLinearAssembly

/-! Exact pointwise lower bounds for the complete printed densities in
quaternionic dimensions 7–10, using actual Hermitian matrix moments. -/
namespace QuaternionicSymmetry.QuaternionicSevenTenDensityBound
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  PrintedProjectionCubicPositivity QuaternionicSevenPointwise
  QuaternionicEightPointwise QuaternionicNinePointwise QuaternionicTenPointwise
  PrintedSevenTenLinearAssembly PrintedCertificatesSevenTen
  DimensionElevenTwelveDensity
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def evaluatedFunctional (v : Fin 6 → CE V) (L : CE V →ₗ[ℝ] ℝ) :
    DimensionElevenTwelveDensity.P →ₗ[ℚ] ℝ :=
  (L.restrictScalars ℚ).comp (aeval v).toLinearMap

omit [FiniteDimensional ℝ V] in
@[simp] theorem evaluatedFunctional_apply (v : Fin 6 → CE V)
    (L : CE V →ₗ[ℝ] ℝ) (p : DimensionElevenTwelveDensity.P) :
    evaluatedFunctional v L p = L (aeval v p) := rfl

omit [DecidableEq β] [FiniteDimensional ℝ V] in
private theorem eval_u_pow (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : β → Matrix κ κ ℂ) (η : β → E V) (n : ℕ) :
    aeval (densityValues Q c B η) (u ^ n) = embed (V := V) (form Q c) ^ n := by
  simp only [map_pow, u, aeval_X]
  rfl

theorem density7_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 7)
    (B : β → Matrix (Fin 7 ⊕ Fin 7) (Fin 7 ⊕ Fin 7) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    128 * L (embed (V := V) (form Q c) ^ 7) ≤
      L (aeval (densityValues Q c B η) rhs7) := by
  have hg (i : Fin 6) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators7 i) :=
    PositiveRay.functional_nonneg
      (generators7_in_positive_ray Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 6, (coefficients7 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators7 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients7_nonneg i) (hg i)
  have he := linear_rhs7 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith


theorem density8_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 8)
    (B : β → Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    160 * L (embed (V := V) (form Q c) ^ 8) ≤
      L (aeval (densityValues Q c B η) rhs8) := by
  have hg (i : Fin 6) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators8 i) :=
    PositiveRay.functional_nonneg
      (generators8_in_positive_ray Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 6, (coefficients8 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators8 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients8_nonneg i) (hg i)
  have he := linear_rhs8 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith


theorem density9_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 9)
    (B : β → Matrix (Fin 9 ⊕ Fin 9) (Fin 9 ⊕ Fin 9) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    200 * L (embed (V := V) (form Q c) ^ 9) ≤
      L (aeval (densityValues Q c B η) rhs9) := by
  have hg (i : Fin 7) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators9 i) :=
    PositiveRay.functional_nonneg
      (generators9_in_positive_ray Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 7, (coefficients9 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators9 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients9_nonneg i) (hg i)
  have he := linear_rhs9 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith


theorem density10_lower_bound
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 10)
    (B : β → Matrix (Fin 10 ⊕ Fin 10) (Fin 10 ⊕ Fin 10) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    240 * L (embed (V := V) (form Q c) ^ 10) ≤
      L (aeval (densityValues Q c B η) rhs10) := by
  have hg (i : Fin 7) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators10 i) :=
    PositiveRay.functional_nonneg
      (generators10_in_positive_ray Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 7, (coefficients10 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators10 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients10_nonneg i) (hg i)
  have he := linear_rhs10 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith

end
end QuaternionicSymmetry.QuaternionicSevenTenDensityBound
