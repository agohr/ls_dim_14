import QuaternionicSymmetry.MatrixTracePolynomial
import QuaternionicSymmetry.QuaternionicHaarOrbital
import QuaternionicSymmetry.OrbitalDiagonalMomentPolynomial
import QuaternionicSymmetry.OrbitalIntegerSpectrumRealization

/-!
From a proved symplectic diagonalization of each real matrix combination to
the finite Schur polynomial in complexified even forms. The diagonalization
premise is explicit pending the concrete matrix spectral construction.
-/

namespace QuaternionicSymmetry.OrbitalMatrixPolynomialBridge

open Matrix MeasureTheory CompactSymplecticHaar MatrixTracePolynomial
  OrbitalConjugateSchur OrbitalDiagonalSpectra OrbitalInterleavedBridge
  QuaternionicHaarOrbital OrbitalDiagonalMomentPolynomial

noncomputable section

variable {β : Type*} [Fintype β]

def finiteOrbitalPolynomial {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) :
    MvPolynomial β ℝ :=
  MvPolynomial.C (4 ^ k : ℝ) *
    ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
      MvPolynomial.C ((QuarticOrbitalEleven.factorialRho n lam : ℝ) *
        matrixSchurValue B lam) * schurPolynomial A lam

theorem eval_finiteOrbitalPolynomial {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) (x : β → ℝ) :
    (finiteOrbitalPolynomial B A k).eval x =
      4 ^ k * ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho n lam : ℝ) *
          matrixSchurValue B lam * matrixSchurValue (matrixCombination A x) lam := by
  simp [finiteOrbitalPolynomial, eval_schurPolynomial]

theorem halfTrace_matrixCombination {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : CompactSymplecticHaar.Group n) (x : β → ℝ) :
    halfTrace (standardJ n) B (matrixCombination A x) g =
      ∑ b, halfTrace (standardJ n) B (A b) g * x b := by
  have hA : matrixCombination A x = ∑ b, x b • A b := by
    ext i j
    simp [matrixCombination, Matrix.sum_apply]
  rw [hA]
  change (pairingLinear B g) (∑ b, x b • A b) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul]
  exact mul_comm _ _

theorem integral_traceCoordinates {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) (x : β → ℝ) :
    (∫ g, (∑ b, traceCoordinates (standardJ n) B A g b * x b) ^ (2*k)
      ∂probability (standardJ n)) =
        4 ^ k * evenMoment (standardJ n) B (matrixCombination A x) k := by
  have hsum (g : CompactSymplecticHaar.Group n) :
      (∑ b, traceCoordinates (standardJ n) B A g b * x b) =
        2 * halfTrace (standardJ n) B (matrixCombination A x) g := by
    rw [halfTrace_matrixCombination, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    unfold traceCoordinates
    ring
  simp_rw [hsum, mul_pow]
  rw [integral_const_mul]
  simp only [evenMoment, pow_mul]
  norm_num

/-- The numerical identity is derived from the source formula and actual
conjugacies, with no numerical moment identity assumed separately. -/
theorem finiteOrbitalPolynomial_integral
    (hsource : LiteralInterleavedFormula) (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (B : Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (A : β → Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (x : Fin (m+6) → ℝ) (u : CompactSymplecticHaar.Group (m+6))
    (hB : B = conjugate (standardJ (m+6)) u (hermitianDiagonal x))
    (hdiag : ∀ t : β → ℝ, ∃ (y : Fin (m+6) → ℝ)
      (v : CompactSymplecticHaar.Group (m+6)),
      matrixCombination A t = conjugate (standardJ (m+6)) v (hermitianDiagonal y))
    (t : β → ℝ) :
    (∫ g, (∑ b, traceCoordinates (standardJ (m+6)) B A g b * t b) ^ (2*k)
      ∂probability (standardJ (m+6))) =
      ((2*k).factorial : ℝ) * (finiteOrbitalPolynomial B A k).eval t := by
  obtain ⟨y, v, hv⟩ := hdiag t
  have h := evenMoment_finiteSchur_of_diagonalizations
    hsource m k hm hk B (matrixCombination A t) x y u v hB hv
  have hfact : ((2*k).factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hfact] at h
  rw [integral_traceCoordinates, eval_finiteOrbitalPolynomial, h]
  ring

theorem finiteOrbitalPolynomial_sqrtSpectrum {n : ℕ} (a : List ℕ) (ha : a.length ≤ n)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) :
    finiteOrbitalPolynomial
      (hermitianDiagonal (OrbitalIntegerSpectrumRealization.sqrtSpectrum n a)) A k =
      MvPolynomial.aeval (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
        (FiniteTypeCSchurSix.orbital n k a) := by
  unfold finiteOrbitalPolynomial FiniteTypeCSchurSix.orbital
  rw [Finset.mul_sum]
  simp only [map_sum, map_mul, MvPolynomial.aeval_C,
    matrixSchurValue_diagonal, OrbitalIntegerSpectrumRealization.realSchurValue_sqrtSpectrum n a ha]
  apply Finset.sum_congr rfl
  intro lam _
  simp only [schurPolynomial, map_pow, map_ofNat, mul_assoc]
  congr 1

variable {V ι : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Signed positivity of the finite matrix Schur polynomial in the even
exterior algebra, conditional on the explicit matrix diagonalizations. -/
theorem finiteOrbitalPolynomial_mem_positiveRay
    (hsource : LiteralInterleavedFormula) (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (B : Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (A : β → Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (x : Fin (m+6) → ℝ) (u : CompactSymplecticHaar.Group (m+6))
    (hB : B = conjugate (standardJ (m+6)) u (hermitianDiagonal x))
    (hdiag : ∀ t : β → ℝ, ∃ (y : Fin (m+6) → ℝ)
      (v : CompactSymplecticHaar.Group (m+6)),
      matrixCombination A t = conjugate (standardJ (m+6)) v (hermitianDiagonal y))
    (Q : QuaternionicStructure V) (c : Module.Basis ι ℝ V)
    (η : β → QuaternionicFundamental.E V)
    (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hkQ : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (QuaternionicFundamental.topForm Q c)
      ((-1 : QuaternionicFundamental.E V) ^ k *
        MvPolynomial.aeval η (finiteOrbitalPolynomial B A k) *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) :=
  polynomial_mem_positiveRay_of_integral Q c (standardJ (m+6)) B A η hη k hkQ
    (finiteOrbitalPolynomial B A k)
    (finiteOrbitalPolynomial_integral hsource m k hm hk B A x u hB hdiag)

end
end QuaternionicSymmetry.OrbitalMatrixPolynomialBridge
