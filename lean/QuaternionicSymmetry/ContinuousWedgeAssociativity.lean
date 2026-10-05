import QuaternionicSymmetry.ContinuousWedgeBlockAlternation

/-! Flattening nested normalized continuous wedges to one full alternation.
These identities retain the order of coefficient multiplication. -/

namespace QuaternionicSymmetry.ContinuousWedgeAssociativity

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeBlockAlternation

noncomputable section

variable {E A B C D Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {p q r : ℕ}

/-- A wedge whose right factor is already a wedge has the single full
alternation normalization `1/(p!q!r!)`. -/
theorem wedge_right_wedge_eq_fullAlternation
    (P : A →L[ℝ] D →L[ℝ] Z)
    (Q : B →L[ℝ] C →L[ℝ] D)
    (α : E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B)
    (γ : E [⋀^Fin r]→L[ℝ] C) :
    wedge P α (wedge Q β γ) =
      (((p.factorial * q.factorial * r.factorial : ℕ) : ℝ)⁻¹) •
        alternationCLM
          ((concatenate P α.toContinuousMultilinearMap
            ((concatenate Q β.toContinuousMultilinearMap
              γ.toContinuousMultilinearMap).domDomCongr
                (finSumFinEquiv (m := q) (n := r)))).domDomCongr
                  (finSumFinEquiv (m := p) (n := q + r))) := by
  let f : ContinuousMultilinearMap ℝ (fun _ : Fin (q + r) => E) D :=
    (concatenate Q β.toContinuousMultilinearMap
      γ.toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := q) (n := r))
  have hscalar :
      (((q.factorial * r.factorial : ℕ) : ℝ)⁻¹) *
          (((p.factorial * (q + r).factorial : ℕ) : ℝ)⁻¹) *
            ((q + r).factorial : ℝ) =
        (((p.factorial * q.factorial * r.factorial : ℕ) : ℝ)⁻¹) := by
    have hp : (p.factorial : ℝ) ≠ 0 := by positivity
    have hq : (q.factorial : ℝ) ≠ 0 := by positivity
    have hr : (r.factorial : ℝ) ≠ 0 := by positivity
    have hqr : ((q + r).factorial : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_mul]
    field_simp
  have hinner : wedge Q β γ =
      (((q.factorial * r.factorial : ℕ) : ℝ)⁻¹) • alternationCLM f := rfl
  rw [hinner, wedge_smul_right]
  change (((q.factorial * r.factorial : ℕ) : ℝ)⁻¹) •
    ((((p.factorial * (q + r).factorial : ℕ) : ℝ)⁻¹) •
      alternationCLM
        ((concatenate P α.toContinuousMultilinearMap
          (alternationCLM f).toContinuousMultilinearMap).domDomCongr
            (finSumFinEquiv (m := p) (n := q + r)))) = _
  rw [alternation_concatenate_right_fin]
  simp only [smul_smul]
  rw [← mul_assoc, hscalar]

/-- A wedge whose left factor is already a wedge has the same single full
alternation normalization. -/
theorem wedge_left_wedge_eq_fullAlternation
    (P : D →L[ℝ] C →L[ℝ] Z)
    (Q : A →L[ℝ] B →L[ℝ] D)
    (α : E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B)
    (γ : E [⋀^Fin r]→L[ℝ] C) :
    wedge P (wedge Q α β) γ =
      (((p.factorial * q.factorial * r.factorial : ℕ) : ℝ)⁻¹) •
        alternationCLM
          ((concatenate P
            ((concatenate Q α.toContinuousMultilinearMap
              β.toContinuousMultilinearMap).domDomCongr
                (finSumFinEquiv (m := p) (n := q)))
            γ.toContinuousMultilinearMap).domDomCongr
              (finSumFinEquiv (m := p + q) (n := r))) := by
  let f : ContinuousMultilinearMap ℝ (fun _ : Fin (p + q) => E) D :=
    (concatenate Q α.toContinuousMultilinearMap
      β.toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := p) (n := q))
  have hscalar :
      (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) *
          (((((p + q).factorial * r.factorial : ℕ) : ℝ)⁻¹)) *
            ((p + q).factorial : ℝ) =
        (((p.factorial * q.factorial * r.factorial : ℕ) : ℝ)⁻¹) := by
    have hp : (p.factorial : ℝ) ≠ 0 := by positivity
    have hq : (q.factorial : ℝ) ≠ 0 := by positivity
    have hr : (r.factorial : ℝ) ≠ 0 := by positivity
    have hpq : ((p + q).factorial : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_mul]
    field_simp
  have hinner : wedge Q α β =
      (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) • alternationCLM f := rfl
  rw [hinner, wedge_smul_left]
  change (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
    (((((p + q).factorial * r.factorial : ℕ) : ℝ)⁻¹) •
      alternationCLM
        ((concatenate P (alternationCLM f).toContinuousMultilinearMap
          γ.toContinuousMultilinearMap).domDomCongr
            (finSumFinEquiv (m := p + q) (n := r)))) = _
  rw [alternation_concatenate_left_fin]
  simp only [smul_smul]
  rw [← mul_assoc, hscalar]

end
end QuaternionicSymmetry.ContinuousWedgeAssociativity
