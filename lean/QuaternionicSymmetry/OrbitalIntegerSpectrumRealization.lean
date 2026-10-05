import QuaternionicSymmetry.OrbitalRealDiagonalSchurContinuation

/-! The integer squared spectra used by the finite orbital polynomials are
realized by diagonal square-root spectra, with zero padding. -/

namespace QuaternionicSymmetry.OrbitalIntegerSpectrumRealization

open OrbitalRealDiagonalSchurContinuation OrbitalRealSchurPolynomial
open CompactSymplecticHaar OrbitalDiagonalSpectra

noncomputable section

def sqrtSpectrum (n : ℕ) (a : List ℕ) : Fin n → ℝ :=
  fun i => Real.sqrt (a.getD i.val 0 : ℝ)

private theorem ofFn_getD_eq_append (n : ℕ) (a : List ℕ)
    (hlen : a.length ≤ n) :
    List.ofFn (fun i : Fin n => a.getD i.val 0) =
      a ++ List.replicate (n-a.length) 0 := by
  apply List.ext_getElem
  · simp [Nat.add_sub_of_le hlen]
  · intro i hi hright
    rw [List.getElem_ofFn]
    by_cases h : i < a.length
    · rw [List.getElem_append_left h, List.getD_eq_getElem a 0 h]
    · rw [List.getElem_append_right (Nat.le_of_not_gt h),
        List.getD_eq_default a 0 (Nat.le_of_not_gt h)]
      simp

private theorem cast_powerSum (a : List ℕ) (d : ℕ) :
    (a.map (fun v : ℕ => (v : ℝ) ^ d)).sum =
      (FiniteTypeCSchurSix.powerSum a d : ℝ) := by
  induction a with
  | nil => simp [FiniteTypeCSchurSix.powerSum]
  | cons b bs ih => simp [FiniteTypeCSchurSix.powerSum, ih]

theorem sqrtSpectrum_powerSum (n : ℕ) (a : List ℕ)
    (hlen : a.length ≤ n) (d : ℕ) (hd : 0 < d) :
    (∑ i : Fin n, (sqrtSpectrum n a i ^ 2) ^ d) =
      (FiniteTypeCSchurSix.powerSum a d : ℝ) := by
  simp_rw [sqrtSpectrum, Real.sq_sqrt (by positivity :
    (0 : ℝ) ≤ (a.getD _ 0 : ℝ))]
  rw [← List.sum_ofFn]
  have hmap : List.ofFn (fun i : Fin n => ((a.getD i.val 0 : ℕ) : ℝ) ^ d) =
      (List.ofFn (fun i : Fin n => a.getD i.val 0)).map
        (fun v : ℕ => (v : ℝ) ^ d) := by simp [Function.comp_def]
  rw [hmap]
  rw [ofFn_getD_eq_append n a hlen]
  simp only [List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate]
  simp [Nat.ne_of_gt hd]
  exact cast_powerSum a d

theorem realSchurValue_sqrtSpectrum (n : ℕ) (a : List ℕ)
    (hlen : a.length ≤ n) (lam : List ℕ) :
    realSchurValue (sqrtSpectrum n a) lam =
      (FiniteTypeCSchurSix.schurValue a lam : ℝ) := by
  unfold realSchurValue FiniteTypeCSchurSix.schurValue
  change _ = (Rat.castHom ℝ) (MvPolynomial.aeval
    (fun i : Fin 6 => FiniteTypeCSchurSix.powerSum a (i.val+1))
    (FiniteTypeCSchurSix.schur lam))
  rw [MvPolynomial.map_aeval
    (fun i : Fin 6 => FiniteTypeCSchurSix.powerSum a (i.val+1))
    (Rat.castHom ℝ) (FiniteTypeCSchurSix.schur lam)]
  simp only [MvPolynomial.aeval_def]
  congr 1
  funext i
  simpa using sqrtSpectrum_powerSum n a hlen (i.val+1) (by omega)

theorem orbital_aeval_real_sqrtSpectrum (n k : ℕ) (a : List ℕ)
    (hlen : a.length ≤ n) (y : Fin n → ℝ) :
    MvPolynomial.aeval
      (fun i : Fin 6 => ∑ j : Fin n, (y j ^ 2) ^ (i.val+1))
      (FiniteTypeCSchurSix.orbital n k a) =
    (4 : ℝ)^k *
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho n lam : ℝ) *
          realSchurValue (sqrtSpectrum n a) lam *
            realSchurValue y lam := by
  unfold FiniteTypeCSchurSix.orbital
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lam _
  simp only [map_pow]
  have hmap (q : ℚ) : (algebraMap ℚ ℝ) q = (q : ℝ) := rfl
  rw [hmap, hmap, hmap]
  rw [← realSchurValue_sqrtSpectrum n a hlen lam]
  change (4 : ℝ)^k *
      (QuarticOrbitalEleven.factorialRho n lam : ℝ) *
      realSchurValue (sqrtSpectrum n a) lam *
      realSchurValue y lam = _
  ring

/-- Every integer spectrum accepted by the existing finite orbital
polynomial, including nonsquare entries, is realized by a real diagonal Haar
moment. The source's diagonal integral formula remains an explicit premise. -/
theorem diagonal_evenMoment_orbital_integerSpectrum
    (hsource : ForresterDiagonalInput.ForresterDiagonalFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (a : List ℕ) (hlen : a.length ≤ m+6)
    (y : Fin (m+6) → ℝ) :
    (4 : ℝ)^k *
      (evenMoment (standardJ (m+6))
        (hermitianDiagonal (sqrtSpectrum (m+6) a))
        (hermitianDiagonal y) k /
          ((2*k).factorial : ℝ)) =
      MvPolynomial.aeval
        (fun i : Fin 6 => ∑ j : Fin (m+6), (y j ^ 2) ^ (i.val+1))
        (FiniteTypeCSchurSix.orbital (m+6) k a) := by
  rw [orbital_aeval_real_sqrtSpectrum (m+6) k a hlen y]
  rw [OrbitalRealDiagonalSchurContinuation.diagonal_evenMoment_finiteSchur_allReal hsource m k hm hk
    (sqrtSpectrum (m+6) a) y]

end
end QuaternionicSymmetry.OrbitalIntegerSpectrumRealization
