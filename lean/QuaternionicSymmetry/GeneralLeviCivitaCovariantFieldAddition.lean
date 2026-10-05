import QuaternionicSymmetry.GeneralLeviCivitaReflectionEndomorphismCancellation

/-! Linearity of the ordinary Levi-Civita endomorphism jet in its local
endomorphism field. This is purely differential algebra. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaCovariantFieldAddition

open GeneralLeviCivitaReflectionEndomorphismCancellation
open scoped ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covariantEndomorphismJet_add
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (A B : E → E →L[ℝ] E) (y u v : E)
    (hA : DifferentiableAt ℝ A y) (hB : DifferentiableAt ℝ B y) :
    covariantEndomorphismJet Γ (fun z => A z + B z) y u v =
      covariantEndomorphismJet Γ A y u v +
        covariantEndomorphismJet Γ B y u v := by
  have hderiv : fderiv ℝ (fun z => A z + B z) y =
      fderiv ℝ A y + fderiv ℝ B y := by
    simpa only [Pi.add_apply] using (fderiv_add hA hB)
  rw [covariantEndomorphismJet, covariantEndomorphismJet,
    covariantEndomorphismJet, hderiv]
  simp only [ContinuousLinearMap.add_apply, map_add]
  abel

end
end QuaternionicSymmetry.GeneralLeviCivitaCovariantFieldAddition
