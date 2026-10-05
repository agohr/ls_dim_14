import QuaternionicSymmetry.CompactMomentPolynomial
import QuaternionicSymmetry.OrbitalDiagonalSpectra
import Mathlib.Order.Interval.Set.Infinite

/-!
Positive rational spectra with separated coordinates suffice to determine a
real polynomial. Thus a spectral identity proved only where its Vandermonde
denominators are nonzero can later be evaluated without those restrictions.
-/

namespace QuaternionicSymmetry.OrbitalRegularPolynomialContinuation

open OrbitalOddDeterminantBase

noncomputable section

def regularTestSet {n : ℕ} (i : Fin n) : Set ℝ :=
  (fun q : ℚ => (q : ℝ)) '' Set.Ioo ((i.val : ℚ) + 1) ((i.val : ℚ) + 2)

theorem regularTestSet_infinite {n : ℕ} (i : Fin n) : (regularTestSet i).Infinite := by
  apply Set.Infinite.image Rat.cast_injective.injOn
  exact Set.Ioo_infinite (by linarith)

theorem oddVandermonde_ne_zero {n : ℕ} (x : Fin n → ℚ)
    (hx : ∀ i, 0 < x i) (hmono : StrictMono x) : oddVandermonde x ≠ 0 := by
  unfold oddVandermonde
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (hx i)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hlt := hmono (Finset.mem_Ioi.mp hj)
    have hi := hx i
    have hj := hx j
    nlinarith

/-- Every point of the product test set comes from positive, strictly
increasing rational coordinates. -/
theorem regularTestSet_coordinates {n : ℕ} (x : Fin n → ℝ)
    (hx : x ∈ Set.pi Set.univ regularTestSet) :
    ∃ q : Fin n → ℚ, (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, (q i : ℝ) = x i) := by
  have h (i : Fin n) : ∃ q : ℚ,
      q ∈ Set.Ioo ((i.val : ℚ) + 1) ((i.val : ℚ) + 2) ∧ (q : ℝ) = x i :=
    hx i (Set.mem_univ i)
  choose q hq heq using h
  refine ⟨q, ?_, ?_, heq⟩
  · intro i
    have hi := (hq i).1
    have hn : (0 : ℚ) ≤ i.val := Nat.cast_nonneg _
    linarith
  · intro i j hij
    have hi := (hq i).2
    have hj := (hq j).1
    have hnat : i.val + 1 ≤ j.val := hij
    have hcast : (i.val : ℚ) + 1 ≤ (j.val : ℚ) := by exact_mod_cast hnat
    linarith

/-- Real coefficients are determined by regular positive rational spectra;
no rationality assumption on the polynomial coefficients is needed. -/
theorem polynomial_eq_of_regular_rational {n : ℕ} (p q : MvPolynomial (Fin n) ℝ)
    (h : ∀ x : Fin n → ℚ, (∀ i, 0 < x i) → StrictMono x →
      p.eval (fun i => (x i : ℝ)) = q.eval (fun i => (x i : ℝ))) : p = q := by
  apply MvPolynomial.funext_set regularTestSet regularTestSet_infinite
  intro x hx
  obtain ⟨y, hy, hmono, heq⟩ := regularTestSet_coordinates x hx
  have hfun : (fun i => (y i : ℝ)) = x := funext heq
  simpa only [hfun] using h y hy hmono

/-- The same result using exactly the positivity and nonzero denominator
hypotheses of the diagonal source formula. -/
theorem polynomial_eq_of_positive_nondegenerate {n : ℕ}
    (p q : MvPolynomial (Fin n) ℝ)
    (h : ∀ x : Fin n → ℚ, (∀ i, 0 < x i) → oddVandermonde x ≠ 0 →
      p.eval (fun i => (x i : ℝ)) = q.eval (fun i => (x i : ℝ))) : p = q := by
  apply polynomial_eq_of_regular_rational
  intro x hx hmono
  exact h x hx (oddVandermonde_ne_zero x hx hmono)

/-- Both spectra may vary independently. -/
theorem polynomial_eq_of_regular_rational_pair {n m : ℕ}
    (p q : MvPolynomial (Fin n ⊕ Fin m) ℝ)
    (h : ∀ (x : Fin n → ℚ) (y : Fin m → ℚ),
      (∀ i, 0 < x i) → StrictMono x → (∀ i, 0 < y i) → StrictMono y →
      p.eval (Sum.elim (fun i => (x i : ℝ)) (fun i => (y i : ℝ))) =
      q.eval (Sum.elim (fun i => (x i : ℝ)) (fun i => (y i : ℝ)))) : p = q := by
  apply MvPolynomial.funext_set (Sum.elim regularTestSet regularTestSet)
    (by intro i; cases i <;> exact regularTestSet_infinite _)
  intro z hz
  obtain ⟨x, hx, hxm, hxe⟩ := regularTestSet_coordinates (fun i => z (Sum.inl i))
    (fun i _ => hz (Sum.inl i) (Set.mem_univ _))
  obtain ⟨y, hy, hym, hye⟩ := regularTestSet_coordinates (fun i => z (Sum.inr i))
    (fun i _ => hz (Sum.inr i) (Set.mem_univ _))
  have heq : Sum.elim (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) = z := by
    funext i
    cases i with
    | inl i => exact hxe i
    | inr i => exact hye i
  simpa only [heq] using h x y hx hxm hy hym

end
end QuaternionicSymmetry.OrbitalRegularPolynomialContinuation
