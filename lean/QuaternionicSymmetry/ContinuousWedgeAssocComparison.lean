import QuaternionicSymmetry.ContinuousWedgeAssociativity
import QuaternionicSymmetry.ContinuousAlternationTransport

/-! Associativity of normalized continuous wedges through associative coefficient pairings. -/

namespace QuaternionicSymmetry.ContinuousWedgeAssocComparison

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousAlternationTransport
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.ContinuousWedgeAssociativity

noncomputable section

variable {E A B C D Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {p q r : ℕ}

private theorem raw_assoc
    (P : A →L[ℝ] B →L[ℝ] D)
    (Q : D →L[ℝ] C →L[ℝ] Z)
    (R : B →L[ℝ] C →L[ℝ] Y)
    (S : A →L[ℝ] Y →L[ℝ] Z)
    (hassoc : ∀ a b c, Q (P a b) c = S a (R b c))
    (α : E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B)
    (γ : E [⋀^Fin r]→L[ℝ] C) :
    (((concatenate Q
      ((concatenate P α.toContinuousMultilinearMap
        β.toContinuousMultilinearMap).domDomCongr
          (finSumFinEquiv (m := p) (n := q)))
      γ.toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := p + q) (n := r))).domDomCongr
          (finCongr (Nat.add_assoc p q r))) =
      ((concatenate S α.toContinuousMultilinearMap
        ((concatenate R β.toContinuousMultilinearMap
          γ.toContinuousMultilinearMap).domDomCongr
            (finSumFinEquiv (m := q) (n := r)))).domDomCongr
              (finSumFinEquiv (m := p) (n := q + r))) := by
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, concatenate_apply,
    Function.comp_def, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  rw [hassoc]
  congr 2
  all_goals
    congr 1
    funext x
    congr 1
    apply Fin.ext
    simp [Nat.add_assoc]

/-- Associativity of normalized wedges, after the canonical reassociation of
the finite slot index.  The coefficient pairings need only associate on
elements; their codomains may differ. -/
theorem wedge_assoc_apply
    (P : A →L[ℝ] B →L[ℝ] D)
    (Q : D →L[ℝ] C →L[ℝ] Z)
    (R : B →L[ℝ] C →L[ℝ] Y)
    (S : A →L[ℝ] Y →L[ℝ] Z)
    (hassoc : ∀ a b c, Q (P a b) c = S a (R b c))
    (α : E [⋀^Fin p]→L[ℝ] A)
    (β : E [⋀^Fin q]→L[ℝ] B)
    (γ : E [⋀^Fin r]→L[ℝ] C)
    (v : Fin ((p + q) + r) → E) :
    wedge Q (wedge P α β) γ v =
      wedge S α (wedge R β γ)
        (v ∘ (finCongr (Nat.add_assoc p q r)).symm) := by
  rw [wedge_left_wedge_eq_fullAlternation,
    wedge_right_wedge_eq_fullAlternation]
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [← raw_assoc P Q R S hassoc α β γ]
  simp only [alternationCLM_domDomCongr_apply, Function.comp_def,
    Equiv.symm_apply_apply]

end
end QuaternionicSymmetry.ContinuousWedgeAssocComparison
