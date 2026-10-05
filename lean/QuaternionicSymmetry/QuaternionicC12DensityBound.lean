import QuaternionicSymmetry.QuaternionicC12Pointwise

/-! Pointwise lower bounds for the complete dimension-eleven/twelve densities.
The functional is any real linear functional positive on the quaternionic top
form. Manifold curvature realization and global integration are separate. -/
namespace QuaternionicSymmetry.QuaternionicC12DensityBound

open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  PrintedProjectionCubicPositivity QuaternionicC12Pointwise
  ElevenTwelveLinearAssembly DimensionElevenTwelveDensity ConditionalC12Bounds

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Evaluation followed by a real functional, viewed as a rational functional
on the printed polynomial ring. -/
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

theorem density11_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 11)
    (B : β → Matrix (Fin 11 ⊕ Fin 11) (Fin 11 ⊕ Fin 11) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    288 * L (embed (V := V) (form Q c) ^ 11) ≤
      L (aeval (densityValues Q c B η) density11) := by
  have hg (i : Fin 12) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators11 i) :=
    PositiveRay.functional_nonneg
      (generators11_in_positive_ray hsource Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 12, (coefficients11 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators11 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients11_nonneg i) (hg i)
  have he := linear_density11 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith

theorem density12_lower_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 12)
    (B : β → Matrix (Fin 12 ⊕ Fin 12) (Fin 12 ⊕ Fin 12) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    336 * L (embed (V := V) (form Q c) ^ 12) ≤
      L (aeval (densityValues Q c B η) density12) := by
  have hg (i : Fin 12) :
      0 ≤ evaluatedFunctional (densityValues Q c B η) L (generators12 i) :=
    PositiveRay.functional_nonneg
      (generators12_in_positive_ray hsource Q c hn B hB η hη i) L hL
  have hs : 0 ≤ ∑ i : Fin 12, (coefficients12 i : ℝ) *
      evaluatedFunctional (densityValues Q c B η) L (generators12 i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast coefficients12_nonneg i) (hg i)
  have he := linear_density12 (evaluatedFunctional (densityValues Q c B η) L)
  simp only [evaluatedFunctional_apply, eval_u_pow] at he hs
  linarith

end
end QuaternionicSymmetry.QuaternionicC12DensityBound
