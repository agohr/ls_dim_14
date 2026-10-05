import QuaternionicSymmetry.OrbitalOddCompanionTableSpecialization
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! Newton specialization of the universal six-column companion table. -/

namespace QuaternionicSymmetry.OrbitalOddNewtonSpecialization

open Finset MvPolynomial
open OrbitalOddSchurTwo OrbitalCompanionSchurTable

noncomputable section

private theorem sum_filtered_antidiagonal (k : ℕ) (f : ℕ × ℕ → ℚ) :
    (∑ a ∈ (Finset.antidiagonal (k+1)).filter
      (fun a : ℕ × ℕ => 0 < a.1 ∧ a.1 ≤ k), f a) =
      ∑ i : Fin k, f (i.val+1, k-i.val) := by
  symm
  refine Finset.sum_bij (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    (i.val+1, k-i.val)) ?_ ?_ ?_ ?_
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_antidiagonal]
    have hi := i.isLt
    omega
  · intro i _ j _ hij
    apply Fin.ext
    have h := congrArg Prod.fst hij
    dsimp at h
    omega
  · intro a ha
    rcases a with ⟨u, v⟩
    have hmem : u + v = k+1 ∧ 0 < u ∧ u < k+1 := by
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
      omega
    refine ⟨⟨u-1, by omega⟩, Finset.mem_univ _, ?_⟩
    change (u-1+1, k-(u-1)) = (u,v)
    apply Prod.ext <;> dsimp <;> omega
  · intro i _
    rfl

theorem spectralPower_newton (n k : ℕ) (t : Fin n → ℚ) :
    (∑ j : Fin n, t j ^ (k+1)) =
      (-1 : ℚ)^k * (k+1) * elementary n (k+1) t +
        ∑ i : Fin k, (-1 : ℚ)^i.val * elementary n (i.val+1) t *
          (∑ j : Fin n, t j ^ (k-i.val)) := by
  have hpoly := MvPolynomial.psum_eq_mul_esymm_sub_sum
    (Fin n) ℚ (k+1) (by omega)
  have h := congrArg (MvPolynomial.aeval t) hpoly
  simp [MvPolynomial.psum, MvPolynomial.esymm, elementary] at h ⊢
  rw [sum_filtered_antidiagonal] at h
  simp only [pow_add, pow_one] at h
  have hsign : (-1 : ℚ)^k * -1 * -1 = (-1 : ℚ)^k := by ring
  rw [hsign] at h
  have hsum :
      (∑ i : Fin k,
        ((-1 : ℚ)^i.val * -1 * elementary n (i.val+1) t) *
          (∑ j : Fin n, t j ^ (k-i.val))) =
      -(∑ i : Fin k, (-1 : ℚ)^i.val * elementary n (i.val+1) t *
          (∑ j : Fin n, t j ^ (k-i.val))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [elementary] at hsum
  rw [hsum, sub_neg_eq_add] at h
  have hpow : (∑ j : Fin n, t j ^ k * t j) =
      ∑ j : Fin n, t j ^ (k+1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
  rw [hpow] at h
  simpa [elementary] using h

/-- The universal table's Newton recurrence becomes the actual power sum of
the spectral roots after elementary specialization. -/
theorem newtonPower_spectral (n k : ℕ) (t : Fin n → ℚ)
    (hk : 0 < k) :
    newtonPower (fun r => elementary n r t) k =
      ∑ j : Fin n, t j ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hinner : ∀ i : Fin k,
              newtonPower (fun r => elementary n r t) (k-i.val) =
                ∑ j : Fin n, t j ^ (k-i.val) := by
            intro i
            apply ih
            · omega
            · have hi := i.isLt
              omega
          rw [newtonPower]
          simp_rw [hinner]
          simpa only [Nat.succ_eq_add_one] using
            (spectralPower_newton n k t).symm

theorem schurValue_spectral (n : ℕ) (x : Fin n → ℚ)
    (lam : List ℕ) :
    schurValue (fun r => elementary n r (fun i => x i ^ 2)) lam =
      OrbitalOddSchurWeightOne.schurEvalOnSquares x lam := by
  unfold schurValue OrbitalOddSchurWeightOne.schurEvalOnSquares
  have hf : (fun i : Fin 6 =>
      newtonPower (fun r => elementary n r (fun j => x j ^ 2)) (i.val+1)) =
      (fun i : Fin 6 => ∑ j : Fin n, (x j ^ 2) ^ (i.val+1)) := by
    funext i
    exact newtonPower_spectral n (i.val+1) (fun j => x j ^ 2) (by omega)
  rw [hf]

end
end QuaternionicSymmetry.OrbitalOddNewtonSpecialization
