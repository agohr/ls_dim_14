import QuaternionicSymmetry.OrbitalOddCoefficientFormula

/-!
# Ordered odd-power selections

Injective selections factor uniquely into an increasing selection of exponents
and a permutation of the columns. This removes the factorial multiplicity in
the paired-alternant formula.
-/

namespace QuaternionicSymmetry.OrbitalOddOrderedSelections

open Matrix OrbitalOddFormalKernel OrbitalOddCoefficientFormula

noncomputable section

theorem sum_injective_eq_factorial_mul_ordered {n N : ℕ}
    (F : (Fin n → Fin N) → ℚ)
    (hperm : ∀ (e : Fin n ↪o Fin N) (σ : Equiv.Perm (Fin n)),
      F (fun i => e (σ i)) = F e) :
    (∑ f : Fin n → Fin N with Function.Injective f, F f) =
      (Nat.factorial n : ℚ) * ∑ e : Fin n ↪o Fin N, F e := by
  let T := (Finset.univ : Finset ((Fin n ↪o Fin N) × Equiv.Perm (Fin n)))
  let U := (Finset.univ : Finset (Fin n → Fin N)).filter Function.Injective
  have hsum : T.sum (fun ep => F (fun i => ep.1 (ep.2 i))) =
      U.sum F := by
    refine Finset.sum_bij (fun ep _ => fun i => ep.1 (ep.2 i)) ?_ ?_ ?_ ?_
    · intro ⟨e, σ⟩ _
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i j hij
      exact σ.injective (e.injective hij)
    · intro ⟨e, σ⟩ _ ⟨e', σ'⟩ _ h
      change (fun i => e (σ i)) = (fun i => e' (σ' i)) at h
      have hrange : Set.range e = Set.range e' := by
        calc
          Set.range e = Set.range (fun i => e (σ i)) := by
            ext z
            constructor
            · rintro ⟨i, rfl⟩
              exact ⟨σ.symm i, by simp⟩
            · rintro ⟨i, rfl⟩
              exact ⟨σ i, rfl⟩
          _ = Set.range (fun i => e' (σ' i)) := by rw [h]
          _ = Set.range e' := by
            ext z
            constructor
            · rintro ⟨i, rfl⟩
              exact ⟨σ' i, rfl⟩
            · rintro ⟨i, rfl⟩
              exact ⟨σ'.symm i, by simp⟩
      have he : e = e' := OrderEmbedding.range_inj.mp hrange
      subst e'
      have hσ : σ = σ' := by
        apply Equiv.ext
        intro i
        exact e.injective (congrFun h i)
      exact Prod.ext rfl hσ
    · intro f hf
      have hfinj : Function.Injective f := by simpa [U] using hf
      let s : Finset (Fin N) := Finset.univ.image f
      have hs : s.card = n := by
        dsimp [s]
        rw [Finset.card_image_of_injective _ hfinj]
        simp
      let e : Fin n ↪o Fin N := s.orderEmbOfFin hs
      let σfun : Fin n → Fin n := fun j =>
        (s.orderIsoOfFin hs).symm ⟨f j, Finset.mem_image_of_mem f (Finset.mem_univ j)⟩
      have hσinj : Function.Injective σfun := by
        intro i j hij
        apply hfinj
        have h := congrArg (s.orderIsoOfFin hs) hij
        have h' : (⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩ : s) =
            ⟨f j, Finset.mem_image_of_mem f (Finset.mem_univ j)⟩ := by
          simpa [σfun] using h
        exact congrArg Subtype.val h'
      let σ : Equiv.Perm (Fin n) :=
        Equiv.ofBijective σfun (Finite.injective_iff_bijective.mp hσinj)
      refine ⟨(e, σ), Finset.mem_univ _, ?_⟩
      funext j
      change e (σfun j) = f j
      change ((s.orderIsoOfFin hs) ((s.orderIsoOfFin hs).symm
        ⟨f j, Finset.mem_image_of_mem f (Finset.mem_univ j)⟩)).val = f j
      simp
    · intro ⟨e, σ⟩ _
      rfl
  rw [← hsum]
  simp only [T, Fintype.sum_prod_type, hperm, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

def pairedOddWeightTerm {n N : ℕ} (x y : Fin n → ℚ)
    (m : ℕ) (f : Fin n → Fin N) : ℚ :=
  if m = ∑ i : Fin n, (2 * (f i).val + 1) then
    (selectedOddAlternant x f).det *
      (selectedOddAlternant y f).det *
        ∏ i : Fin n,
          ((Nat.factorial (2 * (f i).val + 1) : ℚ)⁻¹)
  else 0

private theorem selectedOddAlternant_perm {n N : ℕ} (x : Fin n → ℚ)
    (f : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) :
    (selectedOddAlternant x (fun i => f (σ i))).det =
      (Equiv.Perm.sign σ : ℚ) * (selectedOddAlternant x f).det := by
  have hmatrix : selectedOddAlternant x (fun i => f (σ i)) =
      (selectedOddAlternant x f).submatrix id σ := by
    ext i j
    rfl
  rw [hmatrix, Matrix.det_permute']

private theorem pairedOddWeightTerm_perm {n N : ℕ} (x y : Fin n → ℚ)
    (m : ℕ) (e : Fin n ↪o Fin N) (σ : Equiv.Perm (Fin n)) :
    pairedOddWeightTerm x y m (fun i => e (σ i)) =
      pairedOddWeightTerm x y m e := by
  have hdegree : (∑ i : Fin n, (2 * (e (σ i)).val + 1)) =
      ∑ i : Fin n, (2 * (e i).val + 1) := by
    exact Equiv.sum_comp σ (fun i : Fin n => 2 * (e i).val + 1)
  have hfactor : (∏ i : Fin n,
      ((Nat.factorial (2 * (e (σ i)).val + 1) : ℚ)⁻¹)) =
      ∏ i : Fin n,
        ((Nat.factorial (2 * (e i).val + 1) : ℚ)⁻¹) := by
    exact Equiv.prod_comp σ (fun i : Fin n =>
      ((Nat.factorial (2 * (e i).val + 1) : ℚ)⁻¹))
  unfold pairedOddWeightTerm
  rw [hdegree, selectedOddAlternant_perm,
    selectedOddAlternant_perm, hfactor]
  split_ifs <;> try rfl
  have hs : (Equiv.Perm.sign σ : ℚ) * (Equiv.Perm.sign σ : ℚ) = 1 := by
    exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign σ)
  calc
    ((Equiv.Perm.sign σ : ℚ) * (selectedOddAlternant x e).det) *
        ((Equiv.Perm.sign σ : ℚ) * (selectedOddAlternant y e).det) *
          ∏ i : Fin n,
            ((Nat.factorial (2 * (e i).val + 1) : ℚ)⁻¹) =
      ((Equiv.Perm.sign σ : ℚ) * (Equiv.Perm.sign σ : ℚ)) *
        ((selectedOddAlternant x e).det *
          (selectedOddAlternant y e).det) *
            ∏ i : Fin n,
              ((Nat.factorial (2 * (e i).val + 1) : ℚ)⁻¹) := by ring
    _ = _ := by rw [hs, one_mul]

private theorem pairedOddWeightTerm_zero_noninjective {n N : ℕ}
    (x y : Fin n → ℚ) (m : ℕ) (f : Fin n → Fin N)
    (hf : ¬ Function.Injective f) : pairedOddWeightTerm x y m f = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    change ¬ ∀ i j, f i = f j → i = j at hf
    push_neg at hf
    exact hf
  have hz : (selectedOddAlternant x f).det = 0 := by
    apply Matrix.det_zero_of_column_eq hne
    intro a
    simp [selectedOddAlternant, hij]
  simp [pairedOddWeightTerm, hz]

/-- The weight-`k` coefficient is a sum over strictly increasing selections
of odd exponents, with no factorial multiplicity. -/
theorem fullFormalOddKernel_coeff_weight_ordered {n k : ℕ}
    (x y : Fin n → ℚ) :
    PowerSeries.coeff (n ^ 2 + 2 * k) (fullFormalOddKernel x y).det =
      ∑ e : Fin n ↪o Fin (n + k),
        pairedOddWeightTerm x y (n ^ 2 + 2 * k) e := by
  have hpaired := fullFormalOddKernel_coeff_weight_alternants (n := n) (k := k) x y
  change (Nat.factorial n : ℚ) *
      PowerSeries.coeff (n ^ 2 + 2 * k) (fullFormalOddKernel x y).det =
    ∑ f : Fin n → Fin (n + k),
      pairedOddWeightTerm x y (n ^ 2 + 2 * k) f at hpaired
  have hfilter : (∑ f : Fin n → Fin (n + k),
      pairedOddWeightTerm x y (n ^ 2 + 2 * k) f) =
      ∑ f : Fin n → Fin (n + k) with Function.Injective f,
        pairedOddWeightTerm x y (n ^ 2 + 2 * k) f := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hnoninj : ¬ Function.Injective f := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hf
    exact pairedOddWeightTerm_zero_noninjective x y _ f hnoninj
  rw [hfilter,
    sum_injective_eq_factorial_mul_ordered
      (fun f => pairedOddWeightTerm x y (n ^ 2 + 2 * k) f)
      (pairedOddWeightTerm_perm x y _)] at hpaired
  have hfact : (Nat.factorial n : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact mul_left_cancel₀ hfact hpaired

/-- The row offsets of an increasing exponent selection. Reversing their
order gives the usual padded partition indexing an alternant. -/
def selectionOffset {n N : ℕ} (e : Fin n ↪o Fin N)
    (i : Fin n) : ℕ := (e i).val - i.val

def selectionPartitionRows {n N : ℕ} (e : Fin n ↪o Fin N) : List ℕ :=
  List.ofFn fun i : Fin n => selectionOffset e (Fin.rev i)

theorem selected_degree_eq_base_add_offsets {n N : ℕ}
    (e : Fin n ↪o Fin N) :
    (∑ i : Fin n, (2 * (e i).val + 1)) =
      n ^ 2 + 2 * ∑ i : Fin n, selectionOffset e i := by
  have hpoint : ∀ i : Fin n,
      2 * (e i).val + 1 =
        (2 * i.val + 1) + 2 * selectionOffset e i := by
    intro i
    have hbound := orderEmbedding_index_le e i
    simp only [selectionOffset]
    omega
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  rw [OrbitalOddDeterminantBase.sum_odd, ← Finset.mul_sum]

theorem ordered_weight_iff_offsets {n N k : ℕ}
    (e : Fin n ↪o Fin N) :
    n ^ 2 + 2 * k = ∑ i : Fin n, (2 * (e i).val + 1) ↔
      k = ∑ i : Fin n, selectionOffset e i := by
  rw [selected_degree_eq_base_add_offsets]
  omega

theorem selectionPartitionRows_sum {n N : ℕ}
    (e : Fin n ↪o Fin N) :
    (selectionPartitionRows e).sum =
      ∑ i : Fin n, selectionOffset e i := by
  simp only [selectionPartitionRows, List.sum_ofFn]
  exact Equiv.sum_comp Fin.revPerm (selectionOffset e)

theorem ordered_weight_iff_partition_sum {n N k : ℕ}
    (e : Fin n ↪o Fin N) :
    n ^ 2 + 2 * k = ∑ i : Fin n, (2 * (e i).val + 1) ↔
      k = (selectionPartitionRows e).sum := by
  rw [ordered_weight_iff_offsets, selectionPartitionRows_sum]

theorem selectionOffset_monotone {n N : ℕ}
    (e : Fin n ↪o Fin N) : Monotone (selectionOffset e) := by
  intro i j hij
  have hgap : ∀ (j : Fin n) (i : Fin n), i ≤ j →
      (e i).val + (j.val - i.val) ≤ (e j).val := by
    intro j
    cases n with
    | zero => exact Fin.elim0 j
    | succ q =>
        induction j using Fin.induction with
        | zero =>
            intro i hi
            have hzero : i = 0 := Fin.le_zero_iff.mp hi
            subst i
            simp
        | succ j ih =>
            intro i hi
            by_cases hpre : i ≤ j.castSucc
            · have hprev := ih i hpre
              have hstep : (e j.castSucc).val < (e j.succ).val :=
                e.strictMono Fin.castSucc_lt_succ
              simp only [Fin.val_succ, Fin.val_castSucc] at *
              omega
            · have heq : i = j.succ := by
                apply Fin.ext
                have hv : i.val ≤ j.val + 1 := hi
                have hv' : ¬ i.val ≤ j.val := hpre
                simp only [Fin.val_succ]
                omega
              subst i
              simp
  have h := hgap j i hij
  have hi := orderEmbedding_index_le e i
  simp only [selectionOffset]
  omega

theorem selectionPartitionRows_sorted {n N : ℕ}
    (e : Fin n ↪o Fin N) :
    (selectionPartitionRows e).SortedGE := by
  simp only [selectionPartitionRows, List.sortedGE_ofFn_iff]
  intro i j hij
  exact selectionOffset_monotone e (Fin.rev_le_rev.mpr hij)

private theorem zipIdx_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) :
    (List.ofFn f).zipIdx = List.ofFn (fun i : Fin n => (f i, i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem factorialRho_selectionPartitionRows {n N : ℕ}
    (e : Fin n ↪o Fin N) :
    QuarticOrbitalEleven.factorialRho n (selectionPartitionRows e) =
      OrbitalOddDeterminantBase.normalizer n *
        ∏ i : Fin n,
          ((Nat.factorial (2 * (e i).val + 1) : ℚ)⁻¹) := by
  unfold QuarticOrbitalEleven.factorialRho selectionPartitionRows
  rw [zipIdx_ofFn, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_def]
  have hterm : ∀ i : Fin n,
      ((Nat.factorial (2 * (n - (i.val + 1)) + 1) : ℚ) /
        (Nat.factorial (2 * (selectionOffset e (Fin.rev i) +
          n - (i.val + 1)) + 1) : ℚ)) =
      (Nat.factorial (2 * (Fin.rev i).val + 1) : ℚ) *
        ((Nat.factorial (2 * (e (Fin.rev i)).val + 1) : ℚ)⁻¹) := by
    intro i
    have hrev : (Fin.rev i).val = n - (i.val + 1) := by
      simp [Fin.val_rev]
    have hbound := orderEmbedding_index_le e (Fin.rev i)
    have hsum : selectionOffset e (Fin.rev i) + (Fin.rev i).val =
        (e (Fin.rev i)).val := by
      simp only [selectionOffset]
      omega
    have hnum : 2 * (n - (i.val + 1)) + 1 =
        2 * (Fin.rev i).val + 1 := by omega
    have hden : 2 * (selectionOffset e (Fin.rev i) + n - (i.val + 1)) + 1 =
        2 * (e (Fin.rev i)).val + 1 := by omega
    rw [hnum, hden, div_eq_mul_inv]
  simp_rw [hterm]
  have hprod : (∏ i : Fin n,
      (Nat.factorial (2 * (Fin.rev i).val + 1) : ℚ) *
        ((Nat.factorial (2 * (e (Fin.rev i)).val + 1) : ℚ)⁻¹)) =
      ∏ i : Fin n,
        (Nat.factorial (2 * i.val + 1) : ℚ) *
          ((Nat.factorial (2 * (e i).val + 1) : ℚ)⁻¹) := by
    simpa only [Fin.revPerm_apply] using
      (Equiv.prod_comp Fin.revPerm (fun i : Fin n =>
        (Nat.factorial (2 * i.val + 1) : ℚ) *
          ((Nat.factorial (2 * (e i).val + 1) : ℚ)⁻¹)))
  rw [hprod]
  rw [Finset.prod_mul_distrib]
  rfl

/-- The source-normalized determinant coefficient is an exact sum indexed
by padded partitions obtained from increasing odd-exponent selections. -/
theorem sourceFullFormalOddKernel_coeff_partitionRows {n k : ℕ}
    (x y : Fin n → ℚ) :
    OrbitalOddDeterminantBase.sourceConstant n *
      PowerSeries.coeff (n ^ 2 + 2 * k)
        (sourceFullFormalOddKernel x y).det =
      ∑ e : Fin n ↪o Fin (n + k),
        if k = (selectionPartitionRows e).sum then
          QuarticOrbitalEleven.factorialRho n (selectionPartitionRows e) *
            (selectedOddAlternant x e).det *
              (selectedOddAlternant y e).det
        else 0 := by
  rw [sourceFullFormalOddKernel_coeff_weight,
    fullFormalOddKernel_coeff_weight_ordered, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  unfold pairedOddWeightTerm
  simp only [ordered_weight_iff_partition_sum]
  split_ifs with h
  · rw [factorialRho_selectionPartitionRows]
    ring
  · simp

end
end QuaternionicSymmetry.OrbitalOddOrderedSelections
