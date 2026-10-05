import QuaternionicSymmetry.OrbitalOddDeterminantBase
import QuaternionicSymmetry.OrbitalRankTwoHC
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The all-rank odd determinant through its leading formal coefficient

The first `n` odd powers in the source's `sinh` determinant give an identity
in `ℚ[t]`, not just after rational numerical substitution.  Mapping this
identity to `ℚ⟦t⟧` records its exact coefficient at degree `n²`.  A
rectangular determinant expansion then shows that higher odd powers do not
change any coefficient through that degree. Thus the full formal `sinh`
determinant vanishes below degree `n²` and has the source's normalized
odd-Vandermonde coefficient at degree `n²`. The Haar integral and the higher
type-C Schur coefficients remain separate obligations.
-/

namespace QuaternionicSymmetry.OrbitalOddFormalKernel

open Matrix OrbitalOddDeterminantBase

noncomputable section

/-- The first `n` odd terms in each entry, with `t` left polynomial. -/
def polynomialOddKernel {n : ℕ} (x y : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) (Polynomial ℚ) :=
  Matrix.of fun i j => ∑ k : Fin n,
    Polynomial.C ((x i * y j) ^ (2 * k.val + 1) /
      (Nat.factorial (2 * k.val + 1) : ℚ)) *
      Polynomial.X ^ (2 * k.val + 1)

theorem eval_polynomialOddKernel {n : ℕ} (x y : Fin n → ℚ) (t : ℚ) :
    (Polynomial.evalRingHom t).mapMatrix (polynomialOddKernel x y) =
      truncatedOddKernel x y t := by
  ext i j
  simp only [polynomialOddKernel, truncatedOddKernel, Matrix.of_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom,
    Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The finite normalized determinant identity in `ℚ[t]`. -/
theorem normalized_polynomialOddKernel {n : ℕ} (x y : Fin n → ℚ) :
    Polynomial.C (normalizer n) * (polynomialOddKernel x y).det =
      Polynomial.X ^ (n ^ 2) *
        Polynomial.C (oddVandermonde x * oddVandermonde y) := by
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  change normalizer n * (Polynomial.evalRingHom t) (polynomialOddKernel x y).det =
    t ^ (n ^ 2) * (oddVandermonde x * oddVandermonde y)
  rw [(Polynomial.evalRingHom t).map_det, eval_polynomialOddKernel]
  simpa only [mul_assoc] using normalized_truncatedOddKernel x y t

/-- The same first-`n` odd kernel regarded as a formal power-series matrix. -/
def finiteFormalOddKernel {n : ℕ} (x y : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℚ) :=
  (Polynomial.coeToPowerSeries.ringHom).mapMatrix (polynomialOddKernel x y)

/-- The finite determinant has exactly one formal coefficient. -/
theorem normalized_finiteFormalOddKernel {n : ℕ} (x y : Fin n → ℚ) :
    PowerSeries.C (normalizer n) * (finiteFormalOddKernel x y).det =
      PowerSeries.X ^ (n ^ 2) *
        PowerSeries.C (oddVandermonde x * oddVandermonde y) := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom)
    (normalized_polynomialOddKernel x y)
  simpa only [map_mul, RingHom.map_det, finiteFormalOddKernel,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X, Polynomial.coe_pow] using h

/-- Rectangular determinant expansion for a product `A B`.  Terms with a
repeated intermediate index vanish by column alternation; the surviving
terms are the finite algebraic starting point for the odd Schur series. -/
theorem det_rectangular_mul {n N : ℕ}
    (A : Matrix (Fin n) (Fin N) (Polynomial ℚ))
    (B : Matrix (Fin N) (Fin n) (Polynomial ℚ)) :
    (A * B).det =
      ∑ f : Fin n → Fin N,
        (A.submatrix id f).det * ∏ j, B (f j) j := by
  calc
    (A * B).det = ∑ f : Fin n → Fin N, ∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ * ∏ j, A (σ j) (f j) * B (f j) j := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ f : Fin n → Fin N,
        (A.submatrix id f).det * ∏ j, B (f j) j := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Matrix.det_apply', Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Matrix.submatrix_apply, id_eq]
      rw [Finset.prod_mul_distrib]
      ring

/-- A repeated odd exponent makes a rectangular-product determinant term
zero, independently of the coefficient ring's values. -/
theorem odd_column_repetition {n N : ℕ} (x : Fin n → ℚ)
    (f : Fin n → Fin N) (hf : ¬ Function.Injective f) :
    ((Matrix.of (fun i k =>
      (Polynomial.C (x i ^ (2 * k.val + 1))))).submatrix id f).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    change ¬ ∀ i j, f i = f j → i = j at hf
    push_neg at hf
    exact hf
  apply Matrix.det_zero_of_column_eq hne
  intro k
  simp [hij]

/-- The two rectangular factors of a finite odd-kernel truncation. -/
def oddPowerMatrix {n N : ℕ} (x : Fin n → ℚ) :
    Matrix (Fin n) (Fin N) (Polynomial ℚ) :=
  Matrix.of fun i k => Polynomial.C (x i ^ (2 * k.val + 1))

def weightedOddPowerMatrix {n N : ℕ} (y : Fin n → ℚ) :
    Matrix (Fin N) (Fin n) (Polynomial ℚ) :=
  Matrix.of fun k j =>
    Polynomial.C (y j ^ (2 * k.val + 1) /
      (Nat.factorial (2 * k.val + 1) : ℚ)) *
      Polynomial.X ^ (2 * k.val + 1)

/-- A finite truncation at `N` terms, now allowing `N` to exceed the rank. -/
def polynomialOddKernelUpTo {n : ℕ} (N : ℕ) (x y : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) (Polynomial ℚ) :=
  oddPowerMatrix (N := N) x * weightedOddPowerMatrix (N := N) y

theorem polynomialOddKernelUpTo_apply {n N : ℕ} (x y : Fin n → ℚ)
    (i j : Fin n) :
    polynomialOddKernelUpTo N x y i j =
      ∑ k : Fin N,
        Polynomial.C ((x i * y j) ^ (2 * k.val + 1) /
          (Nat.factorial (2 * k.val + 1) : ℚ)) *
          Polynomial.X ^ (2 * k.val + 1) := by
  simp only [polynomialOddKernelUpTo, oddPowerMatrix, weightedOddPowerMatrix,
    Matrix.mul_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc]
  rw [← Polynomial.C_mul]
  congr 1
  ring_nf

theorem polynomialOddKernelUpTo_self {n : ℕ} (x y : Fin n → ℚ) :
    polynomialOddKernelUpTo n x y = polynomialOddKernel x y := by
  apply Matrix.ext
  intro i j
  rw [polynomialOddKernelUpTo_apply]
  rfl

/-- Every finite truncation has a rectangular determinant expansion.  Its
repeated-index terms vanish, leaving only injective selections of odd
exponents. -/
theorem polynomialOddKernelUpTo_det {n N : ℕ} (x y : Fin n → ℚ) :
    (polynomialOddKernelUpTo N x y).det =
      ∑ f : Fin n → Fin N,
        ((oddPowerMatrix x).submatrix id f).det *
          ∏ j, weightedOddPowerMatrix y (f j) j := by
  exact det_rectangular_mul (oddPowerMatrix x) (weightedOddPowerMatrix y)

theorem polynomialOddKernelUpTo_det_injective {n N : ℕ} (x y : Fin n → ℚ) :
    (polynomialOddKernelUpTo N x y).det =
      ∑ f : Fin n → Fin N with Function.Injective f,
        ((oddPowerMatrix x).submatrix id f).det *
          ∏ j, weightedOddPowerMatrix y (f j) j := by
  rw [polynomialOddKernelUpTo_det]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro f _ hf
  have hnoninj : ¬ Function.Injective f := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hf
  have hzero : ((oddPowerMatrix x).submatrix id f).det = 0 := by
    exact odd_column_repetition x f hnoninj
  simp [hzero]

/-- A strictly increasing sequence of `n` natural indices has its `i`th
index at least `i`. -/
theorem orderEmbedding_index_le {n N : ℕ} (e : Fin n ↪o Fin N)
    (i : Fin n) : i.val ≤ (e i).val := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      induction i using Fin.induction with
      | zero => simp
      | succ i ih =>
          have hlt : (e i.castSucc).val < (e i.succ).val :=
            e.strictMono Fin.castSucc_lt_succ
          simp only [Fin.val_succ, Fin.val_castSucc] at *
          omega

/-- An injective selection of `n` odd exponents has total exponent at least
`1 + 3 + ⋯ + (2n - 1) = n²`. -/
theorem odd_selected_sum_ge {n N : ℕ} (f : Fin n → Fin N)
    (hf : Function.Injective f) :
    n ^ 2 ≤ ∑ i : Fin n, (2 * (f i).val + 1) := by
  let s : Finset (Fin N) := Finset.univ.image f
  have hs : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf]
    simp
  let e := s.orderEmbOfFin hs
  have himage : Finset.univ.image (fun i : Fin n => e i) = s := by
    simpa only [Finset.map_eq_image] using (Finset.map_orderEmbOfFin_univ s hs)
  have hsumf : (Finset.univ.sum fun i : Fin n => 2 * (f i).val + 1) =
      s.sum (fun a => 2 * a.val + 1) := by
    dsimp [s]
    exact (Finset.sum_image (s := Finset.univ) (g := f)
      (f := fun a : Fin N => 2 * a.val + 1) hf.injOn).symm
  have hsume : (Finset.univ.sum fun i : Fin n => 2 * (e i).val + 1) =
      s.sum (fun a => 2 * a.val + 1) := by
    rw [← himage]
    exact (Finset.sum_image (s := Finset.univ) (g := fun i : Fin n => e i)
      (f := fun a : Fin N => 2 * a.val + 1) e.injective.injOn).symm
  rw [hsumf, ← hsume, ← sum_odd n]
  apply Finset.sum_le_sum
  intro i _
  have hbound := orderEmbedding_index_le e i
  omega

/-- Selecting any exponent beyond the first `n` raises the total degree
strictly above `n²`. -/
theorem odd_selected_sum_gt_of_high {n N : ℕ} (f : Fin n → Fin N)
    (hf : Function.Injective f)
    (hhigh : ∃ j : Fin n, n ≤ (f j).val) :
    n ^ 2 < ∑ i : Fin n, (2 * (f i).val + 1) := by
  let s : Finset (Fin N) := Finset.univ.image f
  have hs : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf]
    simp
  let e := s.orderEmbOfFin hs
  have himage : Finset.univ.image (fun i : Fin n => e i) = s := by
    simpa only [Finset.map_eq_image] using (Finset.map_orderEmbOfFin_univ s hs)
  have hsumf : (Finset.univ.sum fun i : Fin n => 2 * (f i).val + 1) =
      s.sum (fun a => 2 * a.val + 1) := by
    dsimp [s]
    exact (Finset.sum_image (s := Finset.univ) (g := f)
      (f := fun a : Fin N => 2 * a.val + 1) hf.injOn).symm
  have hsume : (Finset.univ.sum fun i : Fin n => 2 * (e i).val + 1) =
      s.sum (fun a => 2 * a.val + 1) := by
    rw [← himage]
    exact (Finset.sum_image (s := Finset.univ) (g := fun i : Fin n => e i)
      (f := fun a : Fin N => 2 * a.val + 1) e.injective.injOn).symm
  obtain ⟨j, hj⟩ := hhigh
  have hmem : f j ∈ Finset.univ.image (fun i : Fin n => e i) := by
    rw [himage]
    exact Finset.mem_image_of_mem f (Finset.mem_univ j)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  rw [hsumf, ← hsume, ← sum_odd n]
  apply Finset.sum_lt_sum
  · intro k _
    have hbound := orderEmbedding_index_le e k
    omega
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    have hbound : n ≤ (e i).val := by simpa [hi] using hj
    have hiless := i.isLt
    omega

/-- The right rectangular factor contributes one monomial, whose degree is
the selected sum of odd exponents. -/
theorem weightedOddPowerMatrix_prod {n N : ℕ} (y : Fin n → ℚ)
    (f : Fin n → Fin N) :
    (∏ j : Fin n, weightedOddPowerMatrix y (f j) j) =
      Polynomial.C (∏ j : Fin n,
        y j ^ (2 * (f j).val + 1) /
          (Nat.factorial (2 * (f j).val + 1) : ℚ)) *
        Polynomial.X ^ (∑ j : Fin n, (2 * (f j).val + 1)) := by
  simp only [weightedOddPowerMatrix, Matrix.of_apply]
  rw [Finset.prod_mul_distrib]
  rw [← map_prod (Polynomial.C : ℚ →+* Polynomial ℚ)]
  rw [Finset.prod_pow_eq_pow_sum]

def selectionTerm {n N : ℕ} (x y : Fin n → ℚ)
    (f : Fin n → Fin N) : Polynomial ℚ :=
  ((oddPowerMatrix x).submatrix id f).det *
    ∏ j, weightedOddPowerMatrix y (f j) j

/-- Higher odd exponents cannot affect any coefficient through degree
`n²` in the finite determinant expansion. -/
theorem high_selection_coeff_zero {n N : ℕ} (x y : Fin n → ℚ)
    (f : Fin n → Fin N) (hf : Function.Injective f)
    (hhigh : ∃ j : Fin n, n ≤ (f j).val) (m : ℕ) (hm : m ≤ n ^ 2) :
    (selectionTerm x y f).coeff m = 0 := by
  unfold selectionTerm
  rw [weightedOddPowerMatrix_prod, ← mul_assoc,
    Polynomial.coeff_mul_X_pow']
  have hdegree := odd_selected_sum_gt_of_high f hf hhigh
  simp [Nat.not_le.mpr (lt_of_le_of_lt hm hdegree)]

theorem high_selection_coeff_zero' {n N : ℕ} (x y : Fin n → ℚ)
    (f : Fin n → Fin N)
    (hhigh : ∃ j : Fin n, n ≤ (f j).val) (m : ℕ) (hm : m ≤ n ^ 2) :
    (selectionTerm x y f).coeff m = 0 := by
  by_cases hf : Function.Injective f
  · exact high_selection_coeff_zero x y f hf hhigh m hm
  · unfold selectionTerm
    have hz : ((oddPowerMatrix x).submatrix id f).det = 0 := by
      simpa [oddPowerMatrix] using odd_column_repetition x f hf
    rw [hz]
    simp

theorem coeff_polynomialOddKernelUpTo {n N : ℕ} (x y : Fin n → ℚ)
    (m : ℕ) :
    ((polynomialOddKernelUpTo N x y).det).coeff m =
      ∑ f : Fin n → Fin N, (selectionTerm x y f).coeff m := by
  rw [polynomialOddKernelUpTo_det, Polynomial.finset_sum_coeff]
  rfl

private theorem selectionTerm_castLE {n N : ℕ} (h : n ≤ N)
    (x y : Fin n → ℚ) (g : Fin n → Fin n) :
    selectionTerm (N := N) x y (fun j => (g j).castLE h) =
      selectionTerm (N := n) x y g := by
  rfl

/-- Once at least the first `n` odd powers are present, adding further
finite odd powers changes no determinant coefficient through degree `n²`. -/
theorem polynomialOddKernelUpTo_coeff_stable {n N : ℕ} (h : n ≤ N)
    (x y : Fin n → ℚ) (m : ℕ) (hm : m ≤ n ^ 2) :
    ((polynomialOddKernelUpTo N x y).det).coeff m =
      ((polynomialOddKernel x y).det).coeff m := by
  rw [← polynomialOddKernelUpTo_self, coeff_polynomialOddKernelUpTo,
    coeff_polynomialOddKernelUpTo]
  let low : (Fin n → Fin N) → Prop := fun f => ∀ j, (f j).val < n
  have hremove : (Finset.univ.sum fun f : Fin n → Fin N =>
      (selectionTerm x y f).coeff m) =
      (Finset.univ.filter low).sum (fun f => (selectionTerm x y f).coeff m) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hhigh : ∃ j : Fin n, n ≤ (f j).val := by
      have hnot : ¬ low f := by simpa only [Finset.mem_filter, Finset.mem_univ,
        true_and] using hf
      unfold low at hnot
      push_neg at hnot
      exact hnot
    exact high_selection_coeff_zero' x y f hhigh m hm
  rw [hremove]
  symm
  refine Finset.sum_bij
    (fun g (_ : g ∈ (Finset.univ : Finset (Fin n → Fin n))) =>
      fun j => (g j).castLE h) ?_ ?_ ?_ ?_
  · intro g _
    simp [low]
  · intro g₁ _ g₂ _ hfg
    funext j
    exact Fin.castLE_injective h (congrFun hfg j)
  · intro f hf
    have hlow : low f := by simpa [low] using hf
    let g : Fin n → Fin n := fun j => ⟨(f j).val, hlow j⟩
    refine ⟨g, Finset.mem_univ _, ?_⟩
    funext j
    exact Fin.ext rfl
  · intro g _
    exact congrArg (Polynomial.coeff · m) (selectionTerm_castLE h x y g).symm

/-- The full entrywise `sinh` series, with its value at arbitrary rational
spectral parameters. -/
def fullFormalOddKernel {n : ℕ} (x y : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℚ) :=
  Matrix.of fun i j =>
    PowerSeries.rescale (x i * y j) OrbitalRankTwoHC.sinhSeries

theorem coeff_fullFormalOddKernel {n : ℕ} (x y : Fin n → ℚ)
    (i j : Fin n) (m : ℕ) :
    PowerSeries.coeff m (fullFormalOddKernel x y i j) =
      (x i * y j) ^ m *
        ((1 - (-1 : ℚ) ^ m) / (2 * (Nat.factorial m : ℚ))) := by
  rw [fullFormalOddKernel, Matrix.of_apply, PowerSeries.coeff_rescale,
    OrbitalRankTwoHC.coeff_sinhSeries]

theorem coeff_polynomialOddKernelUpTo_apply {n N : ℕ}
    (x y : Fin n → ℚ) (i j : Fin n) (m : ℕ) :
    (polynomialOddKernelUpTo N x y i j).coeff m =
      ∑ k : Fin N,
        if m = 2 * k.val + 1 then
          (x i * y j) ^ (2 * k.val + 1) /
            (Nat.factorial (2 * k.val + 1) : ℚ)
        else 0 := by
  rw [polynomialOddKernelUpTo_apply, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.coeff_C_mul_X_pow]

private theorem odd_truncation_coeff (a : ℚ) (N m : ℕ)
    (hm : m < 2 * N + 1) :
    (∑ k : Fin N,
      if m = 2 * k.val + 1 then a ^ (2 * k.val + 1) /
        (Nat.factorial (2 * k.val + 1) : ℚ) else 0) =
      a ^ m * ((1 - (-1 : ℚ) ^ m) / (2 * (Nat.factorial m : ℚ))) := by
  by_cases hex : ∃ k : Fin N, m = 2 * k.val + 1
  · obtain ⟨k, hk⟩ := hex
    subst m
    have hunique (l : Fin N) : (2 * k.val + 1 = 2 * l.val + 1) ↔ l = k := by
      constructor
      · intro hl; exact Fin.ext (by omega)
      · intro h; rw [h]
    simp only [hunique]
    simp [pow_add, pow_mul]
    ring
  · have hm0 : m % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
      · exact h0
      · have hk : m / 2 < N := by omega
        have h_eq : m = 2 * (m / 2) + 1 := by omega
        exact (hex ⟨⟨m / 2, hk⟩, h_eq⟩).elim
    have hzero : ∀ k : Fin N, m ≠ 2 * k.val + 1 := by
      intro k hk
      exact hex ⟨k, hk⟩
    simp [hzero, neg_one_pow_eq_pow_mod_two, hm0]

/-- Each full `sinh` entry and its `N`-term polynomial truncation have the
same coefficients in degrees strictly below `2N+1`. -/
theorem coeff_full_eq_truncated {n N : ℕ} (x y : Fin n → ℚ)
    (i j : Fin n) (m : ℕ) (hm : m < 2 * N + 1) :
    PowerSeries.coeff m (fullFormalOddKernel x y i j) =
      (polynomialOddKernelUpTo N x y i j).coeff m := by
  rw [coeff_fullFormalOddKernel, coeff_polynomialOddKernelUpTo_apply]
  exact (odd_truncation_coeff (x i * y j) N m hm).symm

def finiteFormalOddKernelUpTo {n : ℕ} (N : ℕ) (x y : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℚ) :=
  (Polynomial.coeToPowerSeries.ringHom).mapMatrix
    (polynomialOddKernelUpTo N x y)

theorem coeff_finiteFormalOddKernelUpTo {n N : ℕ} (x y : Fin n → ℚ)
    (i j : Fin n) (m : ℕ) :
    PowerSeries.coeff m (finiteFormalOddKernelUpTo N x y i j) =
      (polynomialOddKernelUpTo N x y i j).coeff m := by
  simp only [finiteFormalOddKernelUpTo, RingHom.mapMatrix_apply,
    Matrix.map_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe]

private theorem coeff_prod_congr {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A B : ι → PowerSeries ℚ) (m : ℕ)
    (h : ∀ i ∈ s, ∀ k ≤ m, PowerSeries.coeff k (A i) =
      PowerSeries.coeff k (B i)) :
    PowerSeries.coeff m (s.prod A) = PowerSeries.coeff m (s.prod B) := by
  rw [PowerSeries.coeff_prod, PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.prod_congr rfl
  intro i hi
  apply h i hi
  have hsum : s.sum (fun j => l j) = m := (Finset.mem_finsuppAntidiag.mp hl).1
  have hle : l i ≤ s.sum (fun j => l j) :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  omega

theorem coeff_det_congr {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (PowerSeries ℚ)) (m : ℕ)
    (h : ∀ i j k, k ≤ m → PowerSeries.coeff k (A i j) =
      PowerSeries.coeff k (B i j)) :
    PowerSeries.coeff m A.det = PowerSeries.coeff m B.det := by
  simp only [Matrix.det_apply', map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hle : p.2 ≤ m := by
    have hsum := Finset.mem_antidiagonal.mp hp
    omega
  exact coeff_prod_congr Finset.univ (fun i => A (σ i) i)
    (fun i => B (σ i) i) p.2 (fun i _ k hk => h (σ i) i k (hk.trans hle))

private theorem full_coeff_eq_polynomial {n : ℕ} (x y : Fin n → ℚ)
    (m : ℕ) (hm : m ≤ n ^ 2) :
    PowerSeries.coeff m (fullFormalOddKernel x y).det =
      ((polynomialOddKernel x y).det).coeff m := by
  let N := n + n ^ 2 + 1
  have hN : n ≤ N := by dsimp [N]; omega
  have hdegree : m < 2 * N + 1 := by dsimp [N]; omega
  have hfull : PowerSeries.coeff m (fullFormalOddKernel x y).det =
      PowerSeries.coeff m (finiteFormalOddKernelUpTo N x y).det := by
    apply coeff_det_congr
    intro i j k hk
    exact (coeff_full_eq_truncated x y i j k (lt_of_le_of_lt hk hdegree)).trans
      (coeff_finiteFormalOddKernelUpTo x y i j k).symm
  have hcast : PowerSeries.coeff m
      (finiteFormalOddKernelUpTo N x y).det =
      ((polynomialOddKernelUpTo N x y).det).coeff m := by
    unfold finiteFormalOddKernelUpTo
    rw [← ((Polynomial.coeToPowerSeries.ringHom :
      Polynomial ℚ →+* PowerSeries ℚ)).map_det]
    exact Polynomial.coeff_coe _ _
  exact hfull.trans <| hcast.trans <|
    polynomialOddKernelUpTo_coeff_stable hN x y m hm

/-- The full formal symplectic odd determinant has the normalized leading
coefficient claimed by the source formula.  This uses no convergence or Haar
integral: it is an identity of rational formal power-series coefficients. -/
theorem fullFormalOddKernel_leading {n : ℕ} (x y : Fin n → ℚ) :
    normalizer n * PowerSeries.coeff (n ^ 2) (fullFormalOddKernel x y).det =
      oddVandermonde x * oddVandermonde y := by
  rw [full_coeff_eq_polynomial x y (n ^ 2) (le_refl _)]
  have hpoly := congrArg (fun p : Polynomial ℚ => p.coeff (n ^ 2))
    (normalized_polynomialOddKernel x y)
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul'] at hpoly
  simpa using hpoly

/-- Every coefficient of the full odd determinant below `n²` vanishes. -/
theorem fullFormalOddKernel_coeff_lt {n : ℕ} (x y : Fin n → ℚ)
    (m : ℕ) (hm : m < n ^ 2) :
    PowerSeries.coeff m (fullFormalOddKernel x y).det = 0 := by
  rw [full_coeff_eq_polynomial x y m hm.le]
  have hpoly := congrArg (fun p : Polynomial ℚ => p.coeff m)
    (normalized_polynomialOddKernel x y)
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul'] at hpoly
  have hnot : ¬ n ^ 2 ≤ m := Nat.not_le.mpr hm
  simp only [if_neg hnot] at hpoly
  have hnorm : normalizer n ≠ 0 := by
    unfold normalizer
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact_mod_cast Nat.factorial_ne_zero (2 * k.val + 1)
  exact (mul_eq_zero.mp hpoly).resolve_left hnorm

/-- The source uses entries `2 sinh`, rather than `sinh`; its constant is
`sourceConstant n = normalizer n / 2ⁿ`. -/
def sourceFullFormalOddKernel {n : ℕ} (x y : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℚ) :=
  (PowerSeries.C (2 : ℚ)) • fullFormalOddKernel x y

theorem sourceFullFormalOddKernel_leading {n : ℕ} (x y : Fin n → ℚ) :
    sourceConstant n *
      PowerSeries.coeff (n ^ 2) (sourceFullFormalOddKernel x y).det =
        oddVandermonde x * oddVandermonde y := by
  unfold sourceFullFormalOddKernel
  rw [Matrix.det_smul, Fintype.card_fin, ← map_pow,
    PowerSeries.coeff_C_mul]
  calc
    sourceConstant n * ((2 : ℚ) ^ n *
        PowerSeries.coeff (n ^ 2) (fullFormalOddKernel x y).det) =
      (sourceConstant n * (2 : ℚ) ^ n) *
        PowerSeries.coeff (n ^ 2) (fullFormalOddKernel x y).det := by ring
    _ = oddVandermonde x * oddVandermonde y := by
      rw [sourceConstant_mul_twoPow]
      exact fullFormalOddKernel_leading x y

theorem sourceFullFormalOddKernel_coeff_lt {n : ℕ} (x y : Fin n → ℚ)
    (m : ℕ) (hm : m < n ^ 2) :
    PowerSeries.coeff m (sourceFullFormalOddKernel x y).det = 0 := by
  unfold sourceFullFormalOddKernel
  rw [Matrix.det_smul, Fintype.card_fin, ← map_pow,
    PowerSeries.coeff_C_mul, fullFormalOddKernel_coeff_lt x y m hm,
    mul_zero]

end
end QuaternionicSymmetry.OrbitalOddFormalKernel
