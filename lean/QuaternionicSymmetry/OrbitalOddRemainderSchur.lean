import QuaternionicSymmetry.OrbitalOddSchurOneRow
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Every odd alternant factors through polynomial remainder coefficients

Evaluation at the spectral variables identifies an arbitrary monomial
alternant with a Vandermonde matrix times a matrix of remainders modulo the
monic root polynomial. This gives an exact quotient-free all-rank candidate
for the Schur polynomial attached to an exponent selection.
-/

namespace QuaternionicSymmetry.OrbitalOddRemainderSchur

open Matrix Polynomial Finset OrbitalOddCoefficientFormula
open OrbitalOddDeterminantBase
open OrbitalOddOrderedSelections OrbitalOddFormalKernel
open OrbitalOddSchurOneRow OrbitalOddSchurWeightOne

noncomputable section

def spectralRootPoly {n : ℕ} (t : Fin n → ℚ) : Polynomial ℚ :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))

def exponentRemainder {n N : ℕ} (t : Fin n → ℚ)
    (e : Fin n → Fin N) (j : Fin n) : Polynomial ℚ :=
  (Polynomial.X ^ (e j).val) %ₘ spectralRootPoly t

def remainderCoefficientMatrix {n N : ℕ} (t : Fin n → ℚ)
    (e : Fin n → Fin N) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (exponentRemainder t e j).coeff i.val

theorem spectralRootPoly_monic {n : ℕ} (t : Fin n → ℚ) :
    (spectralRootPoly t).Monic :=
  Polynomial.monic_prod_X_sub_C t Finset.univ

theorem spectralRootPoly_degree {n : ℕ} (t : Fin n → ℚ) :
    (spectralRootPoly t).natDegree = n := by
  simp [spectralRootPoly]

theorem spectralRootPoly_eval_zero {n : ℕ} (t : Fin n → ℚ)
    (i : Fin n) : (spectralRootPoly t).eval (t i) = 0 := by
  unfold spectralRootPoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- Vieta's formula in the coefficient indexing used by the six-column
remainder block. -/
theorem spectralRootPoly_coeff {n r : ℕ} (t : Fin n → ℚ) (hr : r ≤ n) :
    (spectralRootPoly t).coeff (n-r) =
      (-1 : ℚ) ^ r *
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          ∏ i ∈ s, t i := by
  have h := Multiset.prod_X_sub_C_coeff
    ((Finset.univ : Finset (Fin n)).val.map t) (k := n-r) (by
      simp)
  have hcard : Multiset.card ((Finset.univ : Finset (Fin n)).val.map t) = n := by simp
  rw [hcard, Nat.sub_sub_self hr] at h
  change (spectralRootPoly t).coeff (n-r) = _
  convert h using 1
  · simp [spectralRootPoly, Finset.prod, Function.comp_def]
  · rw [Finset.esymm_map_val]

private theorem mod_X_mul_remainder {n : ℕ} (hn : 0 < n)
    (t : Fin n → ℚ) (R : Polynomial ℚ) (hR : R.natDegree < n) :
    (Polynomial.X * R) %ₘ spectralRootPoly t =
      Polynomial.X * R -
        Polynomial.C (R.coeff (n-1)) * spectralRootPoly t := by
  let P := spectralRootPoly t
  let c := R.coeff (n-1)
  let S := Polynomial.X * R - Polynomial.C c * P
  have hRle : R.natDegree ≤ n-1 := Nat.le_sub_one_iff_lt hn |>.mpr hR
  have hXle : (Polynomial.X * R).natDegree ≤ n := by
    calc
      (Polynomial.X * R).natDegree ≤ Polynomial.X.natDegree + R.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ n := by simp only [Polynomial.natDegree_X]; omega
  have hCle : (Polynomial.C c * P).natDegree ≤ n := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by
      simp [P, spectralRootPoly_degree])
  have hSle : S.natDegree ≤ n := by
    dsimp [S]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hXle hCle)
  have hSn : S.coeff n = 0 := by
    have hn_eq : n-1+1 = n := by omega
    have hPn : P.coeff n = 1 := by
      rw [← spectralRootPoly_degree t]
      exact (spectralRootPoly_monic t).coeff_natDegree
    dsimp [S, c]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, ← hn_eq,
      Polynomial.coeff_X_mul, hn_eq, hPn]
    ring
  have hSlt : S.natDegree < n := by
    have := Polynomial.natDegree_le_pred hSle hSn
    omega
  have hSmod : S %ₘ P = S := by
    apply (Polynomial.modByMonic_eq_self_iff (spectralRootPoly_monic t)).mpr
    rw [Polynomial.degree_eq_natDegree (spectralRootPoly_monic t).ne_zero,
      spectralRootPoly_degree]
    have hSdegree : S.degree ≤ ((n-1 : ℕ) : WithBot ℕ) :=
      Polynomial.natDegree_le_iff_degree_le.mp
        (Nat.le_sub_one_iff_lt hn |>.mpr hSlt)
    exact hSdegree.trans_lt (by exact_mod_cast Nat.sub_lt hn (by decide))
  have hdvd : P ∣ Polynomial.X * R - S := by
    refine ⟨Polynomial.C c, ?_⟩
    dsimp [S]
    ring
  have hcongr := Polynomial.modByMonic_eq_of_dvd_sub
    (spectralRootPoly_monic t) hdvd
  change (Polynomial.X * R) %ₘ P = S
  rw [hcongr, hSmod]

/-- The companion recurrence for all monomial remainders. It computes the
six-column block from coefficients of the spectral root polynomial. -/
theorem monomialRemainder_succ {n : ℕ} (hn : 0 < n)
    (t : Fin n → ℚ) (q : ℕ) :
    (Polynomial.X ^ (q+1)) %ₘ spectralRootPoly t =
      Polynomial.X * ((Polynomial.X ^ q) %ₘ spectralRootPoly t) -
        Polynomial.C (((Polynomial.X ^ q) %ₘ spectralRootPoly t).coeff (n-1)) *
          spectralRootPoly t := by
  let P := spectralRootPoly t
  let R := (Polynomial.X ^ q) %ₘ P
  have hP : P.Monic := spectralRootPoly_monic t
  have hPne : P ≠ 1 := by
    intro h
    have hd := spectralRootPoly_degree t
    change spectralRootPoly t = 1 at h
    rw [h] at hd
    simp at hd
    omega
  have hR : R.natDegree < n := by
    have h := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ q) hP hPne
    simpa [R, P, spectralRootPoly_degree] using h
  have hdvd : P ∣ Polynomial.X * Polynomial.X ^ q - Polynomial.X * R := by
    refine ⟨Polynomial.X * ((Polynomial.X ^ q) /ₘ P), ?_⟩
    have hdiv := Polynomial.modByMonic_eq_sub_mul_div (Polynomial.X ^ q) hP
    dsimp [R] at *
    rw [hdiv]
    ring
  have hcongr := Polynomial.modByMonic_eq_of_dvd_sub hP hdvd
  change (Polynomial.X ^ (q+1)) %ₘ P =
    Polynomial.X * R - Polynomial.C (R.coeff (n-1)) * P
  have hpow : (Polynomial.X : Polynomial ℚ) ^ (q+1) =
      Polynomial.X * Polynomial.X ^ q := by
    rw [pow_succ]
    ring
  rw [hpow, hcongr]
  exact mod_X_mul_remainder hn t R hR

theorem monomialRemainder_coeff_succ {n : ℕ} (hn : 0 < n)
    (t : Fin n → ℚ) (q i : ℕ) :
    ((Polynomial.X ^ (q+1)) %ₘ spectralRootPoly t).coeff i =
      (if 1 ≤ i then
        ((Polynomial.X ^ q) %ₘ spectralRootPoly t).coeff (i-1)
      else 0) -
        ((Polynomial.X ^ q) %ₘ spectralRootPoly t).coeff (n-1) *
          (spectralRootPoly t).coeff i := by
  let R := (Polynomial.X ^ q) %ₘ spectralRootPoly t
  have hx : (Polynomial.X * R).coeff i =
      if 1 ≤ i then R.coeff (i-1) else 0 := by
    simpa only [pow_one] using Polynomial.coeff_X_pow_mul' R 1 i
  rw [monomialRemainder_succ hn, Polynomial.coeff_sub, hx,
    Polynomial.coeff_C_mul]

/-- Initial companion state: reducing the first power at the root
polynomial's degree simply removes the monic leading term. -/
theorem monomialRemainder_degree (n : ℕ) (hn : 0 < n)
    (t : Fin n → ℚ) :
    (Polynomial.X ^ n) %ₘ spectralRootPoly t =
      Polynomial.X ^ n - spectralRootPoly t := by
  let P := spectralRootPoly t
  have hPmd : Polynomial.IsMonicOfDegree P n :=
    ⟨spectralRootPoly_degree t, spectralRootPoly_monic t⟩
  have hSlt : ((Polynomial.X : Polynomial ℚ) ^ n - P).natDegree < n :=
    Polynomial.IsMonicOfDegree.natDegree_sub_lt hn.ne'
      (Polynomial.isMonicOfDegree_X_pow ℚ n) hPmd
  have hSmod : ((Polynomial.X : Polynomial ℚ) ^ n - P) %ₘ P =
      Polynomial.X ^ n - P := by
    apply (Polynomial.modByMonic_eq_self_iff (spectralRootPoly_monic t)).mpr
    rw [Polynomial.degree_eq_natDegree (spectralRootPoly_monic t).ne_zero,
      spectralRootPoly_degree]
    by_cases hz : (Polynomial.X : Polynomial ℚ) ^ n - P = 0
    · simp [hz]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mp hSlt
  have hdvd : P ∣ (Polynomial.X : Polynomial ℚ) ^ n -
      (Polynomial.X ^ n - P) := by
    refine ⟨1, ?_⟩
    ring
  have hcongr := Polynomial.modByMonic_eq_of_dvd_sub
    (spectralRootPoly_monic t) hdvd
  change ((Polynomial.X : Polynomial ℚ) ^ n) %ₘ P = _
  rw [hcongr, hSmod]

theorem monomialRemainder_degree_coeff {n r : ℕ}
    (t : Fin n → ℚ) (hrpos : 0 < r) (hr : r ≤ n) :
    ((Polynomial.X ^ n) %ₘ spectralRootPoly t).coeff (n-r) =
      -((-1 : ℚ) ^ r *
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          ∏ i ∈ s, t i) := by
  have hn : 0 < n := hrpos.trans_le hr
  rw [monomialRemainder_degree n hn,
    Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    spectralRootPoly_coeff t hr]
  have hne : n-r ≠ n := by omega
  simp [hne]

private theorem exponentRemainder_degree {n N : ℕ} (hn : 0 < n)
    (t : Fin n → ℚ) (e : Fin n → Fin N) (j : Fin n) :
    (exponentRemainder t e j).natDegree < n := by
  have hne : spectralRootPoly t ≠ 1 := by
    intro h
    have hd := spectralRootPoly_degree t
    rw [h] at hd
    simp at hd
    omega
  exact (Polynomial.natDegree_modByMonic_lt _ (spectralRootPoly_monic t) hne).trans_eq
    (spectralRootPoly_degree t)

private theorem exponentRemainder_eval {n N : ℕ}
    (t : Fin n → ℚ) (e : Fin n → Fin N) (i j : Fin n) :
    (exponentRemainder t e j).eval (t i) = t i ^ (e j).val := by
  have h := Polynomial.eval₂_modByMonic_eq_self_of_root
    (f := RingHom.id ℚ) (p := Polynomial.X ^ (e j).val)
    (q := spectralRootPoly t) (spectralRootPoly_monic t)
    (spectralRootPoly_eval_zero t i)
  simpa [exponentRemainder] using h

/-- Generalized Vandermonde evaluation is the ordinary Vandermonde times the
matrix of monomial remainders. -/
theorem monomialAlternant_eq_vandermonde_mul_remainders {n N : ℕ}
    (t : Fin n → ℚ) (e : Fin n → Fin N) :
    (Matrix.of fun i j => t i ^ (e j).val) =
      Matrix.vandermonde t * remainderCoefficientMatrix t e := by
  cases n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n =>
      ext i j
      rw [Matrix.of_apply, Matrix.mul_apply]
      simp only [Matrix.vandermonde_apply, remainderCoefficientMatrix,
        Matrix.of_apply]
      rw [← exponentRemainder_eval t e i j,
        Polynomial.eval_eq_sum_range'
          (exponentRemainder_degree (by omega) t e j)]
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- The determinant form of the all-rank bialternant factorization. -/
theorem det_monomialAlternant {n N : ℕ}
    (t : Fin n → ℚ) (e : Fin n → Fin N) :
    (Matrix.of fun i j => t i ^ (e j).val).det =
      (Matrix.vandermonde t).det *
        (remainderCoefficientMatrix t e).det := by
  rw [monomialAlternant_eq_vandermonde_mul_remainders, Matrix.det_mul]

theorem det_selectedOddAlternant {n N : ℕ}
    (x : Fin n → ℚ) (e : Fin n → Fin N) :
    (selectedOddAlternant x e).det =
      oddVandermonde x *
        (remainderCoefficientMatrix (fun i => x i ^ 2) e).det := by
  let t : Fin n → ℚ := fun i => x i ^ 2
  have hmatrix : selectedOddAlternant x e =
      Matrix.of fun i j => x i *
        (Matrix.of fun i j => t i ^ (e j).val) i j := by
    ext i j
    simp only [selectedOddAlternant, Matrix.of_apply, t]
    rw [← pow_mul, pow_add]
    ring
  have hbase : oddAlternant x =
      Matrix.of fun i j => x i * (Matrix.vandermonde t) i j := by
    ext i j
    simp only [oddAlternant, Matrix.of_apply, Matrix.vandermonde_apply, t]
    rw [← pow_mul, pow_add]
    ring
  have hodd : (∏ i : Fin n, x i) * (Matrix.vandermonde t).det =
      oddVandermonde x := by
    rw [← Matrix.det_mul_column]
    exact (congrArg Matrix.det hbase).symm.trans (det_oddAlternant x)
  rw [hmatrix, Matrix.det_mul_column, det_monomialAlternant]
  change (∏ i : Fin n, x i) *
      ((Matrix.vandermonde t).det * (remainderCoefficientMatrix t e).det) =
    oddVandermonde x * (remainderCoefficientMatrix t e).det
  rw [← hodd]
  ring

def remainderSchurOnSquares {n N : ℕ} (x : Fin n → ℚ)
    (e : Fin n → Fin N) : ℚ :=
  (remainderCoefficientMatrix (fun i => x i ^ 2) e).det

/-- Remove the trailing zero parts of the rank-padded partition attached to
an exponent selection. The project's finite Schur definition uses this
canonical list representation. -/
def selectionPartition {n N : ℕ} (e : Fin n ↪o Fin N) : List ℕ :=
  (selectionPartitionRows e).filter (· ≠ 0)

private theorem list_sum_filter_ne_zero (l : List ℕ) :
    (l.filter (· ≠ 0)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : a = 0
      · subst a
        simpa using ih
      · have hp : decide (a ≠ 0) = true := by simp [ha]
        simp only [List.filter_cons, hp, ↓reduceIte, List.sum_cons]
        rw [ih]

theorem selectionPartition_sum {n N : ℕ} (e : Fin n ↪o Fin N) :
    (selectionPartition e).sum = (selectionPartitionRows e).sum := by
  exact list_sum_filter_ne_zero _

private theorem filter_ne_zero_of_sum_zero (l : List ℕ) (h : l.sum = 0) :
    l.filter (· ≠ 0) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : a = 0 := by
        simp only [List.sum_cons] at h
        omega
      have hl : l.sum = 0 := by simpa [ha] using h
      have hp : decide (a ≠ 0) = false := by simp [ha]
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      exact ih hl

private theorem filter_ne_zero_of_sum_one (l : List ℕ) (h : l.sum = 1) :
    l.filter (· ≠ 0) = [1] := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      by_cases ha : a = 0
      · have hl : l.sum = 1 := by simpa [ha] using h
        simpa [ha] using ih hl
      · have haval : a = 1 := by
          simp only [List.sum_cons] at h
          omega
        have hl : l.sum = 0 := by
          simp only [List.sum_cons] at h
          omega
        simp only [List.filter_cons, haval]
        rw [filter_ne_zero_of_sum_zero l hl]
        simp

theorem selectionPartition_weight_zero {n N : ℕ}
    (e : Fin n ↪o Fin N) (h : (selectionPartitionRows e).sum = 0) :
    selectionPartition e = [] :=
  filter_ne_zero_of_sum_zero _ h

theorem selectionPartition_weight_one {n N : ℕ}
    (e : Fin n ↪o Fin N) (h : (selectionPartitionRows e).sum = 1) :
    selectionPartition e = [1] :=
  filter_ne_zero_of_sum_one _ h

/-- A partition of weight at most `k` can shift only its last `k` exponent
columns. This is the finite support bound behind the six-column reduction. -/
theorem selectionOffset_zero_before_weight {n N k : ℕ}
    (e : Fin n ↪o Fin N)
    (hweight : (selectionPartitionRows e).sum ≤ k)
    (j : Fin n) (hj : k < n - j.val) : selectionOffset e j = 0 := by
  by_contra hne
  have hpos : 1 ≤ selectionOffset e j := Nat.one_le_iff_ne_zero.mpr hne
  have htail : (Finset.Ici j).card ≤
      ∑ i ∈ Finset.Ici j, selectionOffset e i := by
    calc
      (Finset.Ici j).card = ∑ i ∈ Finset.Ici j, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ Finset.Ici j, selectionOffset e i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hpos.trans (selectionOffset_monotone e (Finset.mem_Ici.mp hi))
  have htotal : (∑ i ∈ Finset.Ici j, selectionOffset e i) ≤
      ∑ i : Fin n, selectionOffset e i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact Nat.zero_le _
  rw [Fin.card_Ici] at htail
  have hsum : (∑ i : Fin n, selectionOffset e i) ≤ k := by
    simpa [selectionPartitionRows_sum] using hweight
  omega

theorem remainderCoefficientMatrix_column_before_weight {n N k : ℕ}
    (t : Fin n → ℚ) (e : Fin n ↪o Fin N)
    (hweight : (selectionPartitionRows e).sum ≤ k)
    (i j : Fin n) (hj : k < n - j.val) :
    remainderCoefficientMatrix t e i j = (1 : Matrix (Fin n) (Fin n) ℚ) i j := by
  have hz := selectionOffset_zero_before_weight e hweight j hj
  have hbound := orderEmbedding_index_le e j
  have hval : (e j).val = j.val := by
    simp only [selectionOffset] at hz
    omega
  have hmod : (Polynomial.X ^ j.val) %ₘ spectralRootPoly t =
      Polynomial.X ^ j.val := by
    apply (Polynomial.modByMonic_eq_self_iff (spectralRootPoly_monic t)).mpr
    rw [Polynomial.degree_X_pow]
    have hPdeg : (spectralRootPoly t).degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree (spectralRootPoly_monic t).ne_zero,
        spectralRootPoly_degree]
    rw [hPdeg]
    exact_mod_cast j.isLt
  simp [remainderCoefficientMatrix, exponentRemainder, hval, hmod,
    Matrix.one_apply, Fin.ext_iff]

/-- Remove a leading identity block from a determinant without division. -/
theorem det_eq_tailBlock_of_leftIdentity (m k : ℕ)
    (M : Matrix (Fin (m+k)) (Fin (m+k)) ℚ)
    (hleft : ∀ (i : Fin (m+k)) (j : Fin m),
      M i (Fin.castAdd k j) = (1 : Matrix (Fin (m+k)) (Fin (m+k)) ℚ)
        i (Fin.castAdd k j)) :
    M.det = (M.submatrix (Fin.natAdd m) (Fin.natAdd m)).det := by
  let E : Fin m ⊕ Fin k ≃ Fin (m+k) := finSumFinEquiv
  have hdet : (M.submatrix E E).det = M.det :=
    Matrix.det_submatrix_equiv_self E M
  let B : Matrix (Fin m) (Fin k) ℚ :=
    M.submatrix (Fin.castAdd k) (Fin.natAdd m)
  let D : Matrix (Fin k) (Fin k) ℚ :=
    M.submatrix (Fin.natAdd m) (Fin.natAdd m)
  have hblock : M.submatrix E E =
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℚ) B 0 D := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simp [E, B, D, Matrix.fromBlocks_apply₁₁,
        finSumFinEquiv_apply_left, hleft, Matrix.one_apply, Fin.ext_iff]
    · simp [E, B, D, Matrix.fromBlocks_apply₁₂,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    · have hne : Fin.natAdd m a ≠ Fin.castAdd k b := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      simp [E, B, D, Matrix.fromBlocks_apply₂₁,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        hleft, hne]
    · simp [E, B, D, Matrix.fromBlocks_apply₂₂,
        finSumFinEquiv_apply_right]
  rw [← hdet, hblock, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul]

/-- Every Schur candidate of weight at most six, in rank at least six, is a
six-by-six determinant of the final remainder coefficients. -/
theorem remainderSchurOnSquares_eq_sixBlock (m N : ℕ)
    (x : Fin (m+6) → ℚ) (e : Fin (m+6) ↪o Fin N)
    (hweight : (selectionPartitionRows e).sum ≤ 6) :
    remainderSchurOnSquares x e =
      ((remainderCoefficientMatrix (fun i => x i ^ 2) e).submatrix
        (Fin.natAdd m) (Fin.natAdd m)).det := by
  unfold remainderSchurOnSquares
  apply det_eq_tailBlock_of_leftIdentity m 6
  intro i j
  apply remainderCoefficientMatrix_column_before_weight
    (k := 6) (hweight := hweight)
  simp only [Fin.val_castAdd]
  have hj := j.isLt
  omega

/-- Exact source-normalized all-rank formal kernel after the two odd
Vandermondes have been factored. The finite remainder determinants are
polynomials in the squared spectra; identifying them with the project's
Jacobi–Trudi Schur polynomials is the remaining algebraic comparison. -/
theorem sourceFullFormalOddKernel_coeff_remainderSchur {n k : ℕ}
    (x y : Fin n → ℚ) :
    sourceConstant n *
      PowerSeries.coeff (n ^ 2 + 2 * k)
        (sourceFullFormalOddKernel x y).det =
      oddVandermonde x * oddVandermonde y *
        ∑ e : Fin n ↪o Fin (n + k),
          if k = (selectionPartitionRows e).sum then
            QuarticOrbitalEleven.factorialRho n (selectionPartitionRows e) *
              remainderSchurOnSquares x e *
                remainderSchurOnSquares y e
          else 0 := by
  rw [sourceFullFormalOddKernel_coeff_partitionRows]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with h
  · rw [det_selectedOddAlternant, det_selectedOddAlternant]
    unfold remainderSchurOnSquares
    ring
  · simp

theorem remainderSchurOnSquares_weight_zero {n N : ℕ}
    (x : Fin n → ℚ) (e : Fin n ↪o Fin N)
    (hweight : (selectionPartitionRows e).sum = 0) :
    remainderSchurOnSquares x e =
      OrbitalOddSchurWeightOne.schurEvalOnSquares x [] := by
  let t : Fin n → ℚ := fun i => x i ^ 2
  have hsum : (∑ i : Fin n, selectionOffset e i) = 0 := by
    simpa [selectionPartitionRows_sum] using hweight
  have hvalues : ∀ j : Fin n, (e j).val = j.val := by
    intro j
    have hle : selectionOffset e j ≤ ∑ i : Fin n, selectionOffset e i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [hsum] at hle
    have hz : selectionOffset e j = 0 := Nat.eq_zero_of_le_zero hle
    have hbound := orderEmbedding_index_le e j
    simp only [selectionOffset] at hz
    omega
  have hmat : remainderCoefficientMatrix t e = 1 := by
    ext i j
    have hdeg : (Polynomial.X ^ j.val) %ₘ spectralRootPoly t =
        Polynomial.X ^ j.val := by
      apply (Polynomial.modByMonic_eq_self_iff (spectralRootPoly_monic t)).mpr
      rw [Polynomial.degree_X_pow]
      have hPdeg : (spectralRootPoly t).degree = (n : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree (spectralRootPoly_monic t).ne_zero,
          spectralRootPoly_degree]
      rw [hPdeg]
      exact_mod_cast j.isLt
    simp [remainderCoefficientMatrix, exponentRemainder, hvalues j,
      hdeg, Matrix.one_apply, Fin.ext_iff]
  unfold remainderSchurOnSquares
  rw [hmat, Matrix.det_one]
  simp [OrbitalOddSchurWeightOne.schurEvalOnSquares,
    FiniteTypeCSchurSix.schur]

/-- Weight one permits exactly the partition with one box in an arbitrary
positive rank. -/
private theorem weight_one_selection_values (n : ℕ)
    (e : Fin (n+1) ↪o Fin (n+2))
    (hweight : (∑ i : Fin (n+1), selectionOffset e i) = 1) :
    ∀ j : Fin (n+1),
      (e j).val = if j = Fin.last n then n+1 else j.val := by
  let last : Fin (n+1) := Fin.last n
  have hlastle : selectionOffset e last ≤ 1 := by
    calc
      selectionOffset e last ≤ ∑ i : Fin (n+1), selectionOffset e i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ last)
      _ = 1 := hweight
  have hlastpos : 0 < selectionOffset e last := by
    by_contra h
    have hz : selectionOffset e last = 0 := Nat.eq_zero_of_not_pos h
    have hall : ∀ i : Fin (n+1), selectionOffset e i = 0 := by
      intro i
      have hi : selectionOffset e i ≤ selectionOffset e last :=
        selectionOffset_monotone e (Fin.le_last i)
      rw [hz] at hi
      omega
    have hsum : (∑ i : Fin (n+1), selectionOffset e i) = 0 := by
      simp [hall]
    omega
  have hlast : selectionOffset e last = 1 := by omega
  have herase : ∑ i ∈ (Finset.univ : Finset (Fin (n+1))).erase last,
      selectionOffset e i = 0 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (n+1)))
      (selectionOffset e) (Finset.mem_univ last)
    rw [hweight, hlast] at h
    omega
  intro j
  by_cases hj : j = last
  · subst j
    simp only [if_true, last] at *
    have hbound := orderEmbedding_index_le e (Fin.last n)
    simp only [selectionOffset] at hlast
    simp only [Fin.val_last] at hlast
    omega
  · have hzero : selectionOffset e j = 0 := by
      have hmem : j ∈ (Finset.univ : Finset (Fin (n+1))).erase last :=
        Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
      have hle : selectionOffset e j ≤
          ∑ i ∈ (Finset.univ : Finset (Fin (n+1))).erase last,
            selectionOffset e i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      omega
    have hj' : j ≠ Fin.last n := by simpa only [last] using hj
    simp only [if_neg hj']
    have hbound := orderEmbedding_index_le e j
    simp only [selectionOffset] at hzero
    omega

theorem remainderSchurOnSquares_weight_one (n : ℕ)
    (x : Fin (n+1) → ℚ) (e : Fin (n+1) ↪o Fin (n+2))
    (hweight : (selectionPartitionRows e).sum = 1) :
    remainderSchurOnSquares x e =
      OrbitalOddSchurWeightOne.schurEvalOnSquares x [1] := by
  let t : Fin (n+1) → ℚ := fun i => x i ^ 2
  have hvalues := weight_one_selection_values n e
    (by simpa [selectionPartitionRows_sum] using hweight)
  have hPdeg : (spectralRootPoly t).degree = (n+1 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (spectralRootPoly_monic t).ne_zero,
      spectralRootPoly_degree]
    norm_cast
  let u : Fin (n+1) → ℚ := fun i =>
    (oneRowRemainder n 0 t).coeff i.val
  have hmatrix : remainderCoefficientMatrix t e =
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ).updateCol (Fin.last n) u := by
    ext i j
    by_cases hj : j = Fin.last n
    · subst j
      simp only [remainderCoefficientMatrix, Matrix.of_apply,
        Matrix.updateCol_self]
      have hlast := hvalues (Fin.last n)
      simp only [if_true] at hlast
      simp [exponentRemainder, oneRowRemainder, spectralRootPoly,
        rootPoly, hlast, u]
    · have hval := hvalues j
      simp only [if_neg hj] at hval
      have hmod : (Polynomial.X ^ j.val) %ₘ spectralRootPoly t =
          Polynomial.X ^ j.val := by
        apply (Polynomial.modByMonic_eq_self_iff (spectralRootPoly_monic t)).mpr
        rw [Polynomial.degree_X_pow, hPdeg]
        exact_mod_cast j.isLt
      simp [remainderCoefficientMatrix, exponentRemainder, hval,
        hmod, Matrix.updateCol_ne hj, u, Matrix.one_apply, Fin.ext_iff]
  have hdet : ((1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ).updateCol
      (Fin.last n) u).det = u (Fin.last n) := by
    have hu : (fun a : Fin (n+1) =>
        ∑ j : Fin (n+1), u j •
          (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) a j) = u := by
      funext a
      simp [Matrix.one_apply]
    rw [← hu, Matrix.det_updateCol_sum]
    simp [Matrix.one_apply]
  unfold remainderSchurOnSquares
  rw [hmatrix, hdet]
  change oneRowCoefficient n 0 t =
    OrbitalOddSchurWeightOne.schurEvalOnSquares x [1]
  rw [oneRowCoefficient_zero, OrbitalOddSchurWeightOne.schurEvalOnSquares_one]
  rfl

end
end QuaternionicSymmetry.OrbitalOddRemainderSchur
