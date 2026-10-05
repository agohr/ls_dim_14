import QuaternionicSymmetry.OrbitalPointwisePolynomialSign

/-! Real squared-spectrum generators for the scalar orbital cone. -/

namespace QuaternionicSymmetry.OrbitalRealSquaredSpectrum

open Matrix MvPolynomial CompactSymplecticHaar OrbitalConjugateSchur
  OrbitalRealSchurPolynomial OrbitalDiagonalSpectra MatrixTracePolynomial
  OrbitalMatrixPolynomialBridge OrbitalSymplecticSpectral QuaternionicMatrixModel
  OrbitalInterleavedBridge OrbitalPointwisePolynomialSign QuaternionicHaarOrbital
  OrbitalIntegerSpectrumRealization MeasureTheory

noncomputable section

variable {β : Type*} [Fintype β]

/-- A Schur value on an arbitrary real squared spectrum. -/
def squaredSchurValue {n : ℕ} (a : Fin n → ℝ) (lam : List ℕ) : ℝ :=
  MvPolynomial.aeval (fun i : Fin 6 => ∑ j : Fin n, a j ^ (i.val + 1))
    (FiniteTypeCSchurSix.schur lam)

/-- The exact `4^k`-normalized type-C orbital generator. Unlike the finite
certificate API, `a` may contain any real coordinates. -/
def realSquaredOrbital (n k : ℕ) (a : Fin n → ℝ) :
    MvPolynomial (Fin 6) ℝ :=
  C ((4 : ℝ) ^ k) *
    ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
      C ((QuarticOrbitalEleven.factorialRho n lam : ℝ) * squaredSchurValue a lam) *
        MvPolynomial.map (Rat.castHom ℝ) (FiniteTypeCSchurSix.schur lam)

theorem squaredSchurValue_square {n : ℕ} (x : Fin n → ℝ) (lam : List ℕ) :
    squaredSchurValue (fun i => x i ^ 2) lam = realSchurValue x lam := by
  rfl

theorem squaredSpectrum_nonneg {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ x i ^ 2 := sq_nonneg _

/-- The real generator extends the existing integer-list certificate API
without changing its normalization. Omitted list entries are zero. -/
theorem realSquaredOrbital_integer (n k : ℕ) (a : List ℕ)
    (ha : a.length ≤ n) :
    realSquaredOrbital n k (fun i => (a.getD i.val 0 : ℝ)) =
      MvPolynomial.map (Rat.castHom ℝ) (FiniteTypeCSchurSix.orbital n k a) := by
  unfold realSquaredOrbital FiniteTypeCSchurSix.orbital
  simp only [map_sum, map_mul, MvPolynomial.map_C, map_pow, map_ofNat,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lam _
  have hs : squaredSchurValue (fun i : Fin n => (a.getD i.val 0 : ℝ)) lam =
      realSchurValue (sqrtSpectrum n a) lam := by
    unfold squaredSchurValue realSchurValue
    exact congrArg (fun f : Fin 6 → ℝ => MvPolynomial.aeval f
      (FiniteTypeCSchurSix.schur lam)) (funext (fun i => by
        apply Finset.sum_congr rfl
        intro j _
        simp [sqrtSpectrum]))
  rw [hs, realSchurValue_sqrtSpectrum n a ha lam]
  simp [mul_assoc]

/-- For a diagonal Hermitian test matrix, the matrix Haar polynomial is
exactly the real squared-spectrum generator evaluated at the six trace
coordinate polynomials. -/
theorem finiteOrbitalPolynomial_diagonal {n : ℕ} (x : Fin n → ℝ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) :
    finiteOrbitalPolynomial (hermitianDiagonal x) A k =
      MvPolynomial.aeval (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
        (realSquaredOrbital n k (fun i => x i ^ 2)) := by
  unfold finiteOrbitalPolynomial realSquaredOrbital
  rw [map_mul, map_sum]
  simp only [map_pow, map_ofNat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lam _
  rw [matrixSchurValue_diagonal, ← squaredSchurValue_square]
  have hmap : MvPolynomial.aeval
      (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
      (MvPolynomial.map (Rat.castHom ℝ) (FiniteTypeCSchurSix.schur lam)) =
      schurPolynomial A lam := by
    change MvPolynomial.eval₂Hom (algebraMap ℝ (MvPolynomial β ℝ))
        (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
        (MvPolynomial.map (Rat.castHom ℝ) (FiniteTypeCSchurSix.schur lam)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ (MvPolynomial β ℝ))
        (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
        (FiniteTypeCSchurSix.schur lam)
    rw [MvPolynomial.eval₂Hom_map_hom]
    congr 1
  simp only [map_mul, MvPolynomial.aeval_C, hmap]
  simp [MvPolynomial.algebraMap_eq, mul_comm]

/-- Intrinsic matrix form of the same generator under an explicit compact
symplectic diagonalization. -/
theorem finiteOrbitalPolynomial_of_diagonalization {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) (x : Fin n → ℝ) (u : Group n)
    (hB : B = conjugate (standardJ n) u (hermitianDiagonal x)) :
    finiteOrbitalPolynomial B A k =
      MvPolynomial.aeval (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
        (realSquaredOrbital n k (fun i => x i ^ 2)) := by
  rw [hB]
  have h : finiteOrbitalPolynomial
      (conjugate (standardJ n) u (hermitianDiagonal x)) A k =
      finiteOrbitalPolynomial (hermitianDiagonal x) A k := by
    unfold finiteOrbitalPolynomial
    simp only [matrixSchurValue_conjugate]
  rw [h]
  exact finiteOrbitalPolynomial_diagonal x A k

/-- Every Hermitian anti-self-dual test matrix determines a nonnegative real
squared spectrum, with the exact generator normalization. -/
theorem exists_realSquaredSpectrum {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hB : HermitianAntiSelfDual B)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) :
    ∃ a : Fin n → ℝ, (∀ i, 0 ≤ a i) ∧
      finiteOrbitalPolynomial B A k =
        MvPolynomial.aeval (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
          (realSquaredOrbital n k a) := by
  obtain ⟨x, u, hx⟩ := exists_symplectic_diagonalization hB
  exact ⟨fun i => x i ^ 2, squaredSpectrum_nonneg x,
    finiteOrbitalPolynomial_of_diagonalization B A k x u hx⟩

/-- The scalar generator is normalized so that its evaluation is the Haar
even moment divided by `(2k)!`. This form can be integrated against a
Gaussian law without choosing measurable eigenvalues: use the intrinsic
`finiteOrbitalPolynomial B A k` on the left of the preceding bridge. -/
theorem exists_realSquaredSpectrum_moment
    (hsource : LiteralInterleavedFormula) (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (B : Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : HermitianAntiSelfDual B)
    (A : β → Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hA : ∀ b, HermitianAntiSelfDual (A b)) :
    ∃ a : Fin (m+6) → ℝ, (∀ i, 0 ≤ a i) ∧
      ∀ t : β → ℝ,
        (∫ g, (∑ b, traceCoordinates (standardJ (m+6)) B A g b * t b) ^ (2*k)
          ∂probability (standardJ (m+6))) =
          ((2*k).factorial : ℝ) *
            ((MvPolynomial.aeval
              (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
              (realSquaredOrbital (m+6) k a)).eval t) := by
  obtain ⟨x, u, hx⟩ := exists_symplectic_diagonalization hB
  refine ⟨fun i => x i ^ 2, squaredSpectrum_nonneg x, ?_⟩
  intro t
  have hdiag (s : β → ℝ) : ∃ (y : Fin (m+6) → ℝ)
      (v : CompactSymplecticHaar.Group (m+6)),
      matrixCombination A s = conjugate (standardJ (m+6)) v (hermitianDiagonal y) :=
    exists_symplectic_diagonalization
      (matrixCombination_HermitianAntiSelfDual A hA s)
  rw [← finiteOrbitalPolynomial_of_diagonalization B A k x u hx]
  exact finiteOrbitalPolynomial_integral hsource m k hm hk B A x u hx hdiag t

end
end QuaternionicSymmetry.OrbitalRealSquaredSpectrum
