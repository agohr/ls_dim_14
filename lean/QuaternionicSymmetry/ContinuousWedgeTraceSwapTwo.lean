import QuaternionicSymmetry.ContinuousWedgeBlockSwapTwo
import QuaternionicSymmetry.ContinuousAlternationTransport
import QuaternionicSymmetry.LocalChernWeilQuadratic

/-! Cyclic trace swaps a two-form block across an arbitrary-degree wedge. -/

namespace QuaternionicSymmetry.ContinuousWedgeTraceSwapTwo

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousAlternationTransport
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeBlockSwapTwo
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalTraceSquareAlgebra

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {q : ℕ}

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

private def rawTraceTwoLeft (T : R →L[ℝ] B)
    (α : E [⋀^Fin 2]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (2 + q) => E) B :=
  (concatenate (traceProduct T) α.toContinuousMultilinearMap
    β.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := 2) (n := q))

private def rawTraceTwoRight (T : R →L[ℝ] B)
    (β : E [⋀^Fin q]→L[ℝ] R) (α : E [⋀^Fin 2]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (q + 2) => E) B :=
  (concatenate (traceProduct T) β.toContinuousMultilinearMap
    α.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := q) (n := 2))

private theorem rawTraceTwo_swap (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (α : E [⋀^Fin 2]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    (rawTraceTwoRight T β α).domDomCongr
        (finCongr (Nat.add_comm q 2)) =
      (rawTraceTwoLeft T α β).domDomCongr (blockSwapTwo q) := by
  ext v
  simp only [rawTraceTwoLeft, rawTraceTwoRight,
    ContinuousMultilinearMap.domDomCongr_apply, concatenate_apply,
    Function.comp_def, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    traceProduct_apply]
  have hα : (fun i : Fin 2 =>
      v (finCongr (Nat.add_comm q 2) (Fin.natAdd q i))) =
      (fun i : Fin 2 => v (blockSwapTwo q (Fin.castAdd q i))) := by
    funext i
    congr 1
    rw [blockSwapTwo_left]
    apply Fin.ext
    simp only [finCongr_apply_coe, Fin.val_natAdd]
  have hβ : (fun j : Fin q =>
      v (finCongr (Nat.add_comm q 2) (Fin.castAdd 2 j))) =
      (fun j : Fin q => v (blockSwapTwo q (Fin.natAdd 2 j))) := by
    funext j
    congr 1
    rw [blockSwapTwo_right]
    apply Fin.ext
    simp
  rw [hα, hβ]
  exact hT _ _

/-- For a cyclic coefficient trace, moving an alternating two-form across an
arbitrary-degree form introduces no sign.  The right side uses the canonical
cast from `Fin (q+2)` to `Fin (2+q)`. -/
theorem wedge_traceProduct_swap_two (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (α : E [⋀^Fin 2]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R)
    (v : Fin (2 + q) → E) :
    wedge (traceProduct T) α β v =
      wedge (traceProduct T) β α
        (v ∘ finCongr (Nat.add_comm q 2)) := by
  change (((2 * q.factorial : ℕ) : ℝ)⁻¹ •
    alternationCLM (rawTraceTwoLeft T α β)) v =
    (((q.factorial * 2 : ℕ) : ℝ)⁻¹ •
      alternationCLM (rawTraceTwoRight T β α))
        (v ∘ finCongr (Nat.add_comm q 2))
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [← alternationCLM_domDomCongr_apply
    (rawTraceTwoRight T β α) (finCongr (Nat.add_comm q 2)) v]
  rw [rawTraceTwo_swap T hT α β,
    alternation_domDomCongr, blockSwapTwo_sign, one_smul]
  simp [mul_comm]

end
end QuaternionicSymmetry.ContinuousWedgeTraceSwapTwo
