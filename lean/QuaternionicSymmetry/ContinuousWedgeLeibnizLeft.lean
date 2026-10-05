import QuaternionicSymmetry.ContinuousWedgeShuffle
import QuaternionicSymmetry.ContinuousWedgeBlockAlternation

/-! The left-slot half of the graded exterior Leibniz identity, in all
degrees, with the explicit canonical reassociation of Fin indices. -/

namespace QuaternionicSymmetry.ContinuousWedgeLeibnizLeft

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeShuffle
  QuaternionicSymmetry.ContinuousWedgeBlockAlternation
  QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousAlternationTransport
  QuaternionicSymmetry.ContinuousMultilinearProduct

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  {p q : ℕ}

/-- Exterior insertion in the left factor commutes with a normalized wedge.
The vector argument on the right is transported from `Fin (p+q+1)` to
`Fin ((p+1)+q)` by the order-preserving equivalence. -/
theorem alternatizeUncurryFin_wedge_left (P : A →L[ℝ] B →L[ℝ] C)
    (D : E →L[ℝ] E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B) (v : Fin (p + q + 1) → E) :
    (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
      wedge P (D (v i)) β (i.removeNth v)) =
      wedge P (ContinuousAlternatingMap.alternatizeUncurryFin D) β
        (v ∘ wedgeLeftIndex p q) := by
  let F := leftDerivativeUncurry D
  let W := (concatenate P F β.toContinuousMultilinearMap).domDomCongr
    (finSumFinEquiv (m := p + 1) (n := q))
  let w : Fin ((p + 1) + q) → E := v ∘ wedgeLeftIndex p q
  have hD : alternationCLM F =
      (p.factorial : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin D :=
    alternation_uncurryLeft_eq_factorial_insertion D
  have hblock := alternation_concatenate_left_fin P F β.toContinuousMultilinearMap
  have hblockAt :
      alternationCLM
        ((concatenate P (alternationCLM F).toContinuousMultilinearMap
          β.toContinuousMultilinearMap).domDomCongr
          (finSumFinEquiv (m := p + 1) (n := q))) w =
        ((p + 1).factorial : ℝ) • alternationCLM W w := by
    simpa only [ContinuousAlternatingMap.smul_apply] using congrArg
      (fun ω : E [⋀^Fin ((p + 1) + q)]→L[ℝ] C => ω w) hblock
  have hbase : (p.factorial : ℝ) •
      wedge P (ContinuousAlternatingMap.alternatizeUncurryFin D) β w =
      ((((p + 1).factorial * q.factorial : ℕ) : ℝ)⁻¹) •
        ((p + 1).factorial : ℝ) • alternationCLM W w := by
    calc
      _ = wedge P ((p.factorial : ℝ) •
          ContinuousAlternatingMap.alternatizeUncurryFin D) β w := by
            rw [wedge_smul_left]
            rfl
      _ = wedge P (alternationCLM F) β w := by rw [hD]
      _ = ((((p + 1).factorial * q.factorial : ℕ) : ℝ)⁻¹) •
          ((p + 1).factorial : ℝ) • alternationCLM W w := by
            change ((((p + 1).factorial * q.factorial : ℕ) : ℝ)⁻¹) •
              alternationCLM
                ((concatenate P (alternationCLM F).toContinuousMultilinearMap
                  β.toContinuousMultilinearMap).domDomCongr
                  (finSumFinEquiv (m := p + 1) (n := q))) w = _
            rw [hblockAt]
  have hfac : (p.factorial : ℝ) ≠ 0 := by positivity
  have hscale :
      wedge P (ContinuousAlternatingMap.alternatizeUncurryFin D) β w =
      (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) • alternationCLM W w := by
    calc
      _ = (p.factorial : ℝ)⁻¹ •
          ((p.factorial : ℝ) •
            wedge P (ContinuousAlternatingMap.alternatizeUncurryFin D) β w) := by
            rw [smul_smul, inv_mul_cancel₀ hfac, one_smul]
      _ = (p.factorial : ℝ)⁻¹ •
          (((((p + 1).factorial * q.factorial : ℕ) : ℝ)⁻¹) •
            (((p + 1).factorial : ℝ) • alternationCLM W w)) := by rw [hbase]
      _ = (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
          alternationCLM W w := by
            simp only [smul_smul]
            congr 1
            have h₁ : ((p + 1).factorial : ℝ) ≠ 0 := by positivity
            have h₂ : (q.factorial : ℝ) ≠ 0 := by positivity
            norm_num only [Nat.cast_mul]
            field_simp
  rw [insertion_wedge_left_fullAlt P D β v,
    leftDerivativeRaw_fullAlt P D β v]
  rw [alternationCLM_domDomCongr_apply]
  exact hscale.symm

end
end QuaternionicSymmetry.ContinuousWedgeLeibnizLeft
