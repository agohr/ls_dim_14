import QuaternionicSymmetry.OrbitalOddFiniteSchurBridge

/-! Real spectral Schur polynomials obtained by substituting even power sums
into the project's explicit rational Jacobi--Trudi formulas. -/

namespace QuaternionicSymmetry.OrbitalRealSchurPolynomial

open MvPolynomial

noncomputable section

def spectralPowerPolynomial (n : ℕ) (i : Fin 6) : MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n, X j ^ (2 * (i.val+1))

def spectralSchurPolynomial (n : ℕ) (lam : List ℕ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval (spectralPowerPolynomial n) (FiniteTypeCSchurSix.schur lam)

def realSchurValue {n : ℕ} (x : Fin n → ℝ) (lam : List ℕ) : ℝ :=
  MvPolynomial.aeval
    (fun i : Fin 6 => ∑ j : Fin n, (x j ^ 2) ^ (i.val+1))
    (FiniteTypeCSchurSix.schur lam)

theorem eval_spectralPowerPolynomial (n : ℕ) (i : Fin 6)
    (x : Fin n → ℝ) :
    (spectralPowerPolynomial n i).eval x =
      ∑ j : Fin n, (x j ^ 2) ^ (i.val+1) := by
  simp [spectralPowerPolynomial, pow_mul]

theorem eval_spectralSchurPolynomial (n : ℕ) (lam : List ℕ)
    (x : Fin n → ℝ) :
    (spectralSchurPolynomial n lam).eval x = realSchurValue x lam := by
  change ((MvPolynomial.aeval x).restrictScalars ℚ)
      (MvPolynomial.aeval (spectralPowerPolynomial n)
        (FiniteTypeCSchurSix.schur lam)) = _
  rw [MvPolynomial.comp_aeval_apply (spectralPowerPolynomial n)
    ((MvPolynomial.aeval x).restrictScalars ℚ)
    (FiniteTypeCSchurSix.schur lam)]
  unfold realSchurValue
  exact congrArg
    (fun f : Fin 6 → ℝ => MvPolynomial.aeval f
      (FiniteTypeCSchurSix.schur lam))
    (funext (fun i => eval_spectralPowerPolynomial n i x))

theorem realSchurValue_rat {n : ℕ} (x : Fin n → ℚ) (lam : List ℕ) :
    realSchurValue (fun i => (x i : ℝ)) lam =
      (OrbitalOddSchurWeightOne.schurEvalOnSquares x lam : ℝ) := by
  unfold realSchurValue OrbitalOddSchurWeightOne.schurEvalOnSquares
  change _ = (Rat.castHom ℝ) (MvPolynomial.aeval
    (fun i : Fin 6 => ∑ j : Fin n, (x j ^ 2) ^ (i.val+1))
    (FiniteTypeCSchurSix.schur lam))
  rw [MvPolynomial.map_aeval
    (fun i : Fin 6 => ∑ j : Fin n, (x j ^ 2) ^ (i.val+1))
    (Rat.castHom ℝ) (FiniteTypeCSchurSix.schur lam)]
  simp only [MvPolynomial.aeval_def]
  congr 1
  funext i
  norm_cast

def finiteSchurPolynomial (n k : ℕ) (x : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
    MvPolynomial.C
      ((QuarticOrbitalEleven.factorialRho n lam : ℝ) * realSchurValue x lam) *
      spectralSchurPolynomial n lam

theorem eval_finiteSchurPolynomial (n k : ℕ) (x y : Fin n → ℝ) :
    (finiteSchurPolynomial n k x).eval y =
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho n lam : ℝ) *
          realSchurValue x lam * realSchurValue y lam := by
  simp [finiteSchurPolynomial, eval_spectralSchurPolynomial]

theorem finiteSchurSum_rat (n k : ℕ) (x y : Fin n → ℚ) :
    (finiteSchurPolynomial n k (fun i => (x i : ℝ))).eval
      (fun i => (y i : ℝ)) =
    ((∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
      QuarticOrbitalEleven.factorialRho n lam *
        OrbitalOddSchurWeightOne.schurEvalOnSquares x lam *
          OrbitalOddSchurWeightOne.schurEvalOnSquares y lam : ℚ) : ℝ) := by
  rw [eval_finiteSchurPolynomial]
  simp_rw [realSchurValue_rat]
  norm_cast

end
end QuaternionicSymmetry.OrbitalRealSchurPolynomial
