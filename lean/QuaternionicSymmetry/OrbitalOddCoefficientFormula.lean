import QuaternionicSymmetry.OrbitalOddFormalKernel

/-!
# Finite formulas for every coefficient of the odd orbital determinant

At any prescribed degree, the full formal determinant is determined by a
finite rectangular odd-power matrix.  The formula below retains the exact
factorials and determinants, with no analytic or Haar interpretation.
-/

namespace QuaternionicSymmetry.OrbitalOddCoefficientFormula

open Matrix OrbitalOddFormalKernel

noncomputable section

/-- The rational alternant for an arbitrary selection of odd powers. -/
def selectedOddAlternant {n N : ℕ} (x : Fin n → ℚ)
    (f : Fin n → Fin N) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => x i ^ (2 * (f j).val + 1)

private theorem selectedOddAlternant_map {n N : ℕ} (x : Fin n → ℚ)
    (f : Fin n → Fin N) :
    ((oddPowerMatrix x).submatrix id f).det =
      Polynomial.C (selectedOddAlternant x f).det := by
  have hmatrix : (oddPowerMatrix x).submatrix id f =
      (Polynomial.C : ℚ →+* Polynomial ℚ).mapMatrix
        (selectedOddAlternant x f) := by
    ext i j
    rfl
  rw [hmatrix, ← RingHom.map_det]

/-- A selected term is a single monomial with its exact rational weight. -/
theorem selectionTerm_eq_monomial {n N : ℕ} (x y : Fin n → ℚ)
    (f : Fin n → Fin N) :
    selectionTerm x y f =
      Polynomial.C ((selectedOddAlternant x f).det *
        ∏ j : Fin n, y j ^ (2 * (f j).val + 1) /
          (Nat.factorial (2 * (f j).val + 1) : ℚ)) *
        Polynomial.X ^ (∑ j : Fin n, (2 * (f j).val + 1)) := by
  unfold selectionTerm
  rw [selectedOddAlternant_map, weightedOddPowerMatrix_prod,
    ← mul_assoc, ← map_mul]

/-- The coefficient of an individual selection vanishes except at its total
odd degree. -/
theorem selectionTerm_coeff {n N : ℕ} (x y : Fin n → ℚ)
    (f : Fin n → Fin N) (m : ℕ) :
    (selectionTerm x y f).coeff m =
      if m = ∑ j : Fin n, (2 * (f j).val + 1) then
        (selectedOddAlternant x f).det *
          ∏ j : Fin n, y j ^ (2 * (f j).val + 1) /
            (Nat.factorial (2 * (f j).val + 1) : ℚ)
      else 0 := by
  rw [selectionTerm_eq_monomial, Polynomial.coeff_C_mul_X_pow]

/-- An exponent at index `n+k` forces at least `2(k+1)` degrees above
the odd Vandermonde's leading degree. -/
theorem odd_selected_sum_ge_of_high {n N k : ℕ}
    (f : Fin n → Fin N) (hf : Function.Injective f)
    (hhigh : ∃ j : Fin n, n + k ≤ (f j).val) :
    n ^ 2 + 2 * (k + 1) ≤
      ∑ i : Fin n, (2 * (f i).val + 1) := by
  cases n with
  | zero =>
      obtain ⟨j, _⟩ := hhigh
      exact Fin.elim0 j
  | succ q =>
      let s : Finset (Fin N) := Finset.univ.image f
      have hs : s.card = q + 1 := by
        dsimp [s]
        rw [Finset.card_image_of_injective _ hf]
        simp
      let e := s.orderEmbOfFin hs
      have himage : Finset.univ.image (fun i : Fin (q + 1) => e i) = s := by
        simpa only [Finset.map_eq_image] using (Finset.map_orderEmbOfFin_univ s hs)
      have hsumf : (∑ i : Fin (q + 1), (2 * (f i).val + 1)) =
          s.sum (fun a => 2 * a.val + 1) := by
        dsimp [s]
        exact (Finset.sum_image (s := Finset.univ) (g := f)
          (f := fun a : Fin N => 2 * a.val + 1) hf.injOn).symm
      have hsume : (∑ i : Fin (q + 1), (2 * (e i).val + 1)) =
          s.sum (fun a => 2 * a.val + 1) := by
        rw [← himage]
        exact (Finset.sum_image (s := Finset.univ) (g := fun i : Fin (q + 1) => e i)
          (f := fun a : Fin N => 2 * a.val + 1) e.injective.injOn).symm
      obtain ⟨j, hj⟩ := hhigh
      have hmem : f j ∈ Finset.univ.image (fun i : Fin (q + 1) => e i) := by
        rw [himage]
        exact Finset.mem_image_of_mem f (Finset.mem_univ j)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      have hlast : q + 1 + k ≤ (e (Fin.last q)).val := by
        have hle : e i ≤ e (Fin.last q) := e.monotone (Fin.le_last i)
        have hv : (e i).val ≤ (e (Fin.last q)).val := Fin.val_le_of_le hle
        have hv' : q + 1 + k ≤ (e i).val := by simpa [hi] using hj
        omega
      rw [hsumf, ← hsume]
      have hpoint : ∀ i : Fin (q + 1),
          2 * i.val + 1 + (if i = Fin.last q then 2 * (k + 1) else 0) ≤
            2 * (e i).val + 1 := by
        intro i
        have hbase := orderEmbedding_index_le e i
        split_ifs with h
        · subst i
          have hval : (Fin.last q).val = q := rfl
          omega
        · omega
      have hsum := Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin (q + 1)))) (fun i _ => hpoint i)
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] at hsum
      have hbase : (∑ i : Fin (q + 1), (2 * i.val + 1)) = (q + 1) ^ 2 :=
        OrbitalOddDeterminantBase.sum_odd (q + 1)
      have hleft : (∑ i : Fin (q + 1), 2 * i.val) +
          (∑ _i : Fin (q + 1), 1) = (q + 1) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        exact hbase
      have hright : (∑ i : Fin (q + 1), 2 * (e i).val) +
          (∑ _i : Fin (q + 1), 1) =
          ∑ i : Fin (q + 1), (2 * (e i).val + 1) := by
        rw [← Finset.sum_add_distrib]
      rw [hleft, hright] at hsum
      convert hsum using 1

theorem high_selection_coeff_zero_weight {n N k : ℕ} (x y : Fin n → ℚ)
    (f : Fin n → Fin N) (hhigh : ∃ j : Fin n, n + k ≤ (f j).val)
    (m : ℕ) (hm : m ≤ n ^ 2 + 2 * k) :
    (selectionTerm x y f).coeff m = 0 := by
  by_cases hf : Function.Injective f
  · rw [selectionTerm_coeff]
    have hdegree := odd_selected_sum_ge_of_high f hf hhigh
    have hne : m ≠ ∑ i : Fin n, (2 * (f i).val + 1) := by omega
    simp [hne]
  · unfold selectionTerm
    have hz : ((oddPowerMatrix x).submatrix id f).det = 0 := by
      exact odd_column_repetition x f hf
    simp [hz]

private theorem selectionTerm_castLE_general {n L N : ℕ} (h : L ≤ N)
    (x y : Fin n → ℚ) (g : Fin n → Fin L) :
    selectionTerm (N := N) x y (fun j => (g j).castLE h) =
      selectionTerm (N := L) x y g := by
  rfl

/-- For weight `k`, the first `n+k` odd powers determine every determinant
coefficient through degree `n²+2k`. -/
theorem polynomialOddKernelUpTo_coeff_stable_weight {n N k : ℕ}
    (h : n + k ≤ N) (x y : Fin n → ℚ) (m : ℕ)
    (hm : m ≤ n ^ 2 + 2 * k) :
    ((polynomialOddKernelUpTo N x y).det).coeff m =
      ((polynomialOddKernelUpTo (n + k) x y).det).coeff m := by
  rw [coeff_polynomialOddKernelUpTo, coeff_polynomialOddKernelUpTo]
  let low : (Fin n → Fin N) → Prop := fun f => ∀ j, (f j).val < n + k
  have hremove : (Finset.univ.sum fun f : Fin n → Fin N =>
      (selectionTerm x y f).coeff m) =
      (Finset.univ.filter low).sum fun f => (selectionTerm x y f).coeff m := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hhigh : ∃ j : Fin n, n + k ≤ (f j).val := by
      have hnot : ¬ low f := by simpa only [Finset.mem_filter, Finset.mem_univ,
        true_and] using hf
      unfold low at hnot
      push_neg at hnot
      exact hnot
    exact high_selection_coeff_zero_weight x y f hhigh m hm
  rw [hremove]
  symm
  refine Finset.sum_bij
    (fun g (_ : g ∈ (Finset.univ : Finset (Fin n → Fin (n + k)))) =>
      fun j => (g j).castLE h) ?_ ?_ ?_ ?_
  · intro g _
    simp [low]
  · intro g₁ _ g₂ _ hfg
    funext j
    exact Fin.castLE_injective h (congrFun hfg j)
  · intro f hf
    have hlow : low f := by simpa [low] using hf
    let g : Fin n → Fin (n + k) := fun j => ⟨(f j).val, hlow j⟩
    refine ⟨g, Finset.mem_univ _, ?_⟩
    funext j
    exact Fin.ext rfl
  · intro g _
    exact congrArg (Polynomial.coeff · m) (selectionTerm_castLE_general h x y g).symm

/-- Any formal coefficient is a finite sum of rational alternants.  The
choice `N = m+1` includes every entrywise power that can contribute at
degree `m`. -/
theorem fullFormalOddKernel_coeff_finite {n : ℕ} (x y : Fin n → ℚ)
    (m : ℕ) :
    PowerSeries.coeff m (fullFormalOddKernel x y).det =
      ∑ f : Fin n → Fin (m + 1),
        if m = ∑ j : Fin n, (2 * (f j).val + 1) then
          (selectedOddAlternant x f).det *
            ∏ j : Fin n, y j ^ (2 * (f j).val + 1) /
              (Nat.factorial (2 * (f j).val + 1) : ℚ)
        else 0 := by
  have hfull : PowerSeries.coeff m (fullFormalOddKernel x y).det =
      PowerSeries.coeff m
        (finiteFormalOddKernelUpTo (m + 1) x y).det := by
    apply coeff_det_congr
    intro i j k hk
    exact (coeff_full_eq_truncated x y i j k (by omega)).trans
      (coeff_finiteFormalOddKernelUpTo x y i j k).symm
  have hcast : PowerSeries.coeff m
      (finiteFormalOddKernelUpTo (m + 1) x y).det =
      ((polynomialOddKernelUpTo (m + 1) x y).det).coeff m := by
    unfold finiteFormalOddKernelUpTo
    rw [← ((Polynomial.coeToPowerSeries.ringHom :
      Polynomial ℚ →+* PowerSeries ℚ)).map_det]
    exact Polynomial.coeff_coe _ _
  rw [hfull, hcast, coeff_polynomialOddKernelUpTo]
  apply Finset.sum_congr rfl
  intro f _
  exact selectionTerm_coeff x y f m

/-- The full formal determinant agrees with the `n+k` term odd kernel
through weight `k`. -/
theorem fullFormalOddKernel_coeff_stable_weight {n k : ℕ}
    (x y : Fin n → ℚ) (m : ℕ) (hm : m ≤ n ^ 2 + 2 * k) :
    PowerSeries.coeff m (fullFormalOddKernel x y).det =
      ((polynomialOddKernelUpTo (n + k) x y).det).coeff m := by
  let N := n + n ^ 2 + 2 * k + 1
  have hN : n + k ≤ N := by dsimp [N]; omega
  have hdegree : m < 2 * N + 1 := by dsimp [N]; omega
  have hfull : PowerSeries.coeff m (fullFormalOddKernel x y).det =
      PowerSeries.coeff m (finiteFormalOddKernelUpTo N x y).det := by
    apply coeff_det_congr
    intro i j l hl
    exact (coeff_full_eq_truncated x y i j l
      (lt_of_le_of_lt hl hdegree)).trans
      (coeff_finiteFormalOddKernelUpTo x y i j l).symm
  have hcast : PowerSeries.coeff m (finiteFormalOddKernelUpTo N x y).det =
      ((polynomialOddKernelUpTo N x y).det).coeff m := by
    unfold finiteFormalOddKernelUpTo
    rw [← ((Polynomial.coeToPowerSeries.ringHom :
      Polynomial ℚ →+* PowerSeries ℚ)).map_det]
    exact Polynomial.coeff_coe _ _
  exact hfull.trans <| hcast.trans <|
    polynomialOddKernelUpTo_coeff_stable_weight hN x y m hm

/-- Exact all-rank coefficient formula at the degree for weight `k`.
Only the first `n+k` odd powers appear. -/
theorem fullFormalOddKernel_coeff_weight {n k : ℕ} (x y : Fin n → ℚ) :
    PowerSeries.coeff (n ^ 2 + 2 * k) (fullFormalOddKernel x y).det =
      ∑ f : Fin n → Fin (n + k),
        if n ^ 2 + 2 * k = ∑ j : Fin n, (2 * (f j).val + 1) then
          (selectedOddAlternant x f).det *
            ∏ j : Fin n, y j ^ (2 * (f j).val + 1) /
              (Nat.factorial (2 * (f j).val + 1) : ℚ)
        else 0 := by
  rw [fullFormalOddKernel_coeff_stable_weight x y _ (le_refl _),
    coeff_polynomialOddKernelUpTo]
  apply Finset.sum_congr rfl
  intro f _
  exact selectionTerm_coeff x y f _

/-- Every coefficient with parity opposite the rank vanishes. -/
theorem fullFormalOddKernel_coeff_wrong_parity {n k : ℕ}
    (x y : Fin n → ℚ) :
    PowerSeries.coeff (n + 2 * k + 1) (fullFormalOddKernel x y).det = 0 := by
  rw [fullFormalOddKernel_coeff_finite]
  apply Finset.sum_eq_zero
  intro f _
  have hdegree : (∑ j : Fin n, (2 * (f j).val + 1)) =
      n + 2 * ∑ j : Fin n, (f j).val := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [add_comm]
  have hne : n + 2 * k + 1 ≠
      ∑ j : Fin n, (2 * (f j).val + 1) := by omega
  simp [hne]

/-- The source's `2 sinh` convention multiplies every coefficient by `2ⁿ`.
Its normalizing constant therefore converts to `normalizer n`. -/
theorem sourceFullFormalOddKernel_coeff_weight {n k : ℕ}
    (x y : Fin n → ℚ) :
    OrbitalOddDeterminantBase.sourceConstant n *
        PowerSeries.coeff (n ^ 2 + 2 * k)
          (sourceFullFormalOddKernel x y).det =
      OrbitalOddDeterminantBase.normalizer n *
        PowerSeries.coeff (n ^ 2 + 2 * k)
          (fullFormalOddKernel x y).det := by
  unfold sourceFullFormalOddKernel
  rw [Matrix.det_smul, Fintype.card_fin, ← map_pow,
    PowerSeries.coeff_C_mul]
  rw [← mul_assoc, OrbitalOddDeterminantBase.sourceConstant_mul_twoPow]

/-- The exact source-normalized coefficient, with its factorial weights and
finite selection range displayed in one formula. -/
theorem sourceFullFormalOddKernel_coeff_weight_explicit {n k : ℕ}
    (x y : Fin n → ℚ) :
    OrbitalOddDeterminantBase.sourceConstant n *
        PowerSeries.coeff (n ^ 2 + 2 * k)
          (sourceFullFormalOddKernel x y).det =
      OrbitalOddDeterminantBase.normalizer n *
        ∑ f : Fin n → Fin (n + k),
          if n ^ 2 + 2 * k = ∑ j : Fin n, (2 * (f j).val + 1) then
            (selectedOddAlternant x f).det *
              ∏ j : Fin n, y j ^ (2 * (f j).val + 1) /
                (Nat.factorial (2 * (f j).val + 1) : ℚ)
          else 0 := by
  rw [sourceFullFormalOddKernel_coeff_weight,
    fullFormalOddKernel_coeff_weight]

/-- The full odd kernel is symmetric in its spectral arguments after
transposing the matrix. -/
theorem fullFormalOddKernel_swap {n : ℕ} (x y : Fin n → ℚ) :
    fullFormalOddKernel x y = (fullFormalOddKernel y x)ᵀ := by
  ext i j
  simp only [fullFormalOddKernel, Matrix.of_apply, Matrix.transpose_apply]
  rw [mul_comm]

theorem fullFormalOddKernel_coeff_swap {n : ℕ} (x y : Fin n → ℚ) (m : ℕ) :
    PowerSeries.coeff m (fullFormalOddKernel x y).det =
      PowerSeries.coeff m (fullFormalOddKernel y x).det := by
  rw [fullFormalOddKernel_swap, Matrix.det_transpose]

/-- Rectangular Cauchy–Binet with every selection counted in every order.
The factorial removes the permutation multiplicity. -/
private theorem sum_permuted_selection {n N : ℕ}
    (A : Matrix (Fin n) (Fin N) (Polynomial ℚ))
    (B : Matrix (Fin N) (Fin n) (Polynomial ℚ))
    (σ : Equiv.Perm (Fin n)) :
    (∑ f : Fin n → Fin N,
      (Equiv.Perm.sign σ : Polynomial ℚ) *
        (A.submatrix id f).det * ∏ j, B (f (σ j)) j) =
      ∑ f : Fin n → Fin N,
        (A.submatrix id f).det * ∏ j, B (f j) j := by
  refine Finset.sum_bij (fun f _ => f ∘ σ) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ hfg
    funext j
    have hj := congrFun hfg (σ.symm j)
    simpa [Function.comp_def] using hj
  · intro g _
    refine ⟨g ∘ σ.symm, Finset.mem_univ _, ?_⟩
    funext j
    simp [Function.comp_def]
  · intro f _
    have hmatrix : A.submatrix id (f ∘ σ) =
        (A.submatrix id f).submatrix id σ := by
      ext i j
      rfl
    rw [hmatrix, Matrix.det_permute']
    rfl

theorem det_rectangular_mul_symmetrized {n N : ℕ}
    (A : Matrix (Fin n) (Fin N) (Polynomial ℚ))
    (B : Matrix (Fin N) (Fin n) (Polynomial ℚ)) :
    (Nat.factorial n : Polynomial ℚ) * (A * B).det =
      ∑ f : Fin n → Fin N,
        (A.submatrix id f).det * (B.submatrix f id).det := by
  let S : Polynomial ℚ :=
    ∑ f : Fin n → Fin N,
      (A.submatrix id f).det * ∏ j, B (f j) j
  have hpair : (∑ f : Fin n → Fin N,
      (A.submatrix id f).det * (B.submatrix f id).det) =
      ∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin N,
        (Equiv.Perm.sign σ : Polynomial ℚ) *
          (A.submatrix id f).det * ∏ j, B (f (σ j)) j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    conv_lhs => rhs; rw [Matrix.det_apply']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Matrix.submatrix_apply]
    simp only [id_eq]
    ring
  have hperm : (∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin N,
        (Equiv.Perm.sign σ : Polynomial ℚ) *
          (A.submatrix id f).det * ∏ j, B (f (σ j)) j) =
      (Nat.factorial n : Polynomial ℚ) * S := by
    simp_rw [sum_permuted_selection]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [det_rectangular_mul]
  exact (hpair.trans hperm).symm

/-- The rectangular identity applied to the odd kernel pairs the two
alternants before coefficient extraction. -/
theorem polynomialOddKernelUpTo_paired {n N : ℕ} (x y : Fin n → ℚ) :
    (Nat.factorial n : Polynomial ℚ) *
        (polynomialOddKernelUpTo N x y).det =
      ∑ f : Fin n → Fin N,
        ((oddPowerMatrix x).submatrix id f).det *
          ((weightedOddPowerMatrix y).submatrix f id).det := by
  exact det_rectangular_mul_symmetrized (oddPowerMatrix x)
    (weightedOddPowerMatrix y)

/-- The selected right determinant is the second odd alternant times its
factorial weight and one monomial. -/
theorem weightedOddPowerMatrix_selected_det {n N : ℕ}
    (y : Fin n → ℚ) (f : Fin n → Fin N) :
    ((weightedOddPowerMatrix y).submatrix f id).det =
      Polynomial.C ((∏ i : Fin n,
        ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)) *
          (selectedOddAlternant y f).det) *
        Polynomial.X ^ (∑ i : Fin n, (2 * (f i).val + 1)) := by
  let v : Fin n → Polynomial ℚ := fun i =>
    Polynomial.C ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹) *
      Polynomial.X ^ (2 * (f i).val + 1)
  let M : Matrix (Fin n) (Fin n) (Polynomial ℚ) :=
    ((Polynomial.C : ℚ →+* Polynomial ℚ).mapMatrix
      (selectedOddAlternant y f))ᵀ
  have hmatrix : (weightedOddPowerMatrix y).submatrix f id =
      Matrix.of fun i j => v i * M i j := by
    apply Matrix.ext
    intro i j
    simp only [weightedOddPowerMatrix, Matrix.submatrix_apply,
      Matrix.of_apply, id_eq, v, M, Matrix.transpose_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply,
      selectedOddAlternant]
    calc
      Polynomial.C (y j ^ (2 * (f i).val + 1) /
          (Nat.factorial (2 * (f i).val + 1) : ℚ)) *
          Polynomial.X ^ (2 * (f i).val + 1) =
        (Polynomial.C ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹) *
          Polynomial.C (y j ^ (2 * (f i).val + 1))) *
          Polynomial.X ^ (2 * (f i).val + 1) := by
            rw [← map_mul]
            congr 1
            simp [div_eq_mul_inv, mul_comm]
      _ = _ := by ring
  rw [hmatrix, Matrix.det_mul_column]
  have hdet : M.det = Polynomial.C (selectedOddAlternant y f).det := by
    dsimp [M]
    rw [Matrix.det_transpose]
    exact (Polynomial.C : ℚ →+* Polynomial ℚ).map_det
      (selectedOddAlternant y f) |>.symm
  rw [hdet]
  have hv : (∏ i : Fin n, v i) =
      Polynomial.C (∏ i : Fin n,
        ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)) *
        Polynomial.X ^ (∑ i : Fin n, (2 * (f i).val + 1)) := by
    dsimp [v]
    rw [Finset.prod_mul_distrib,
      ← map_prod (Polynomial.C : ℚ →+* Polynomial ℚ),
      Finset.prod_pow_eq_pow_sum]
  rw [hv]
  calc
    (Polynomial.C (∏ i : Fin n,
        ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)) *
        Polynomial.X ^ (∑ i : Fin n, (2 * (f i).val + 1))) *
        Polynomial.C (selectedOddAlternant y f).det =
      (Polynomial.C (∏ i : Fin n,
        ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)) *
        Polynomial.C (selectedOddAlternant y f).det) *
        Polynomial.X ^ (∑ i : Fin n, (2 * (f i).val + 1)) := by ring
    _ = _ := by rw [← map_mul]

theorem fullFormalOddKernel_coeff_weight_paired {n k : ℕ}
    (x y : Fin n → ℚ) :
    (Nat.factorial n : ℚ) *
        PowerSeries.coeff (n ^ 2 + 2 * k)
          (fullFormalOddKernel x y).det =
      ∑ f : Fin n → Fin (n + k),
        (((oddPowerMatrix x).submatrix id f).det *
          ((weightedOddPowerMatrix y).submatrix f id).det).coeff
            (n ^ 2 + 2 * k) := by
  rw [fullFormalOddKernel_coeff_stable_weight x y _ (le_refl _)]
  have h := congrArg (fun p : Polynomial ℚ => p.coeff (n ^ 2 + 2 * k))
    (polynomialOddKernelUpTo_paired (N := n + k) x y)
  change (Polynomial.C (Nat.factorial n : ℚ) *
      (polynomialOddKernelUpTo (n + k) x y).det).coeff (n ^ 2 + 2 * k) = _ at h
  simpa only [Polynomial.coeff_C_mul, Polynomial.finset_sum_coeff] using h

/-- A paired term has both spectral determinants and no remaining polynomial
operations in its coefficient. -/
theorem pairedOddTerm_coeff {n N : ℕ} (x y : Fin n → ℚ)
    (f : Fin n → Fin N) (m : ℕ) :
    (((oddPowerMatrix x).submatrix id f).det *
      ((weightedOddPowerMatrix y).submatrix f id).det).coeff m =
      if m = ∑ i : Fin n, (2 * (f i).val + 1) then
        (selectedOddAlternant x f).det *
          (selectedOddAlternant y f).det *
            ∏ i : Fin n,
              ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)
      else 0 := by
  rw [selectedOddAlternant_map, weightedOddPowerMatrix_selected_det,
    ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · subst m
    ring
  · rfl

/-- The rational paired-alternant coefficient formula.  This is the
finite algebraic Cauchy–Binet form preceding the type-C Schur quotient. -/
theorem fullFormalOddKernel_coeff_weight_alternants {n k : ℕ}
    (x y : Fin n → ℚ) :
    (Nat.factorial n : ℚ) *
        PowerSeries.coeff (n ^ 2 + 2 * k)
          (fullFormalOddKernel x y).det =
      ∑ f : Fin n → Fin (n + k),
        if n ^ 2 + 2 * k = ∑ i : Fin n, (2 * (f i).val + 1) then
          (selectedOddAlternant x f).det *
            (selectedOddAlternant y f).det *
              ∏ i : Fin n,
                ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)
        else 0 := by
  rw [fullFormalOddKernel_coeff_weight_paired]
  apply Finset.sum_congr rfl
  intro f _
  exact pairedOddTerm_coeff x y f _

/-- Paired alternants with exactly the source's `2 sinh` entries and
normalization constant. -/
theorem sourceFullFormalOddKernel_coeff_weight_alternants {n k : ℕ}
    (x y : Fin n → ℚ) :
    (Nat.factorial n : ℚ) *
      (OrbitalOddDeterminantBase.sourceConstant n *
        PowerSeries.coeff (n ^ 2 + 2 * k)
          (sourceFullFormalOddKernel x y).det) =
      OrbitalOddDeterminantBase.normalizer n *
        ∑ f : Fin n → Fin (n + k),
          if n ^ 2 + 2 * k = ∑ i : Fin n, (2 * (f i).val + 1) then
            (selectedOddAlternant x f).det *
              (selectedOddAlternant y f).det *
                ∏ i : Fin n,
                  ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)
          else 0 := by
  rw [sourceFullFormalOddKernel_coeff_weight]
  rw [← mul_assoc, mul_comm (Nat.factorial n : ℚ), mul_assoc,
    fullFormalOddKernel_coeff_weight_alternants]

theorem sourceFullFormalOddKernel_coeff_wrong_parity {n k : ℕ}
    (x y : Fin n → ℚ) :
    PowerSeries.coeff (n + 2 * k + 1)
      (sourceFullFormalOddKernel x y).det = 0 := by
  unfold sourceFullFormalOddKernel
  rw [Matrix.det_smul, Fintype.card_fin, ← map_pow,
    PowerSeries.coeff_C_mul,
    fullFormalOddKernel_coeff_wrong_parity, mul_zero]

end
end QuaternionicSymmetry.OrbitalOddCoefficientFormula
