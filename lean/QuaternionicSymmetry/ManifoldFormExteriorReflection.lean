import QuaternionicSymmetry.ManifoldFormExteriorEvaluation
import QuaternionicSymmetry.ManifoldFormPowers

/-! Exterior evaluation preserves powers and reflects scalar equality of
actual tangent forms when the chosen frame is invertible. -/
namespace QuaternionicSymmetry.ManifoldFormExteriorReflection
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldFormPowers
open ManifoldFormExteriorEvaluation ExteriorContinuousPairing ExteriorContinuousPowers
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem value_formPower (p : M) (y : E) (L : E →L[ℝ] E) {d : ℕ}
    (α : Form 𝓘(ℝ,E) M d) (n : ℕ) :
    value p y L (d*n) (formPower α n) = (value p y L d α) ^ n := by
  have hp : representative p y L (d*n) (formPower α n) =
      powPower (representative p y L d α) n := by
    apply toContinuous_injective
    rw [representative_pairing, toContinuous_powPower, representative_pairing]
    change (inChartModel p (formPower α n) y).compContinuousLinearMap L = _
    rw [inChartModel_formPower]
    exact wedgePower_comp L _ n
  exact congrArg Subtype.val hp

theorem tangent_eq_of_value_eq {n : ℕ} (x : M) (L : E ≃L[ℝ] E)
    (α β : Form 𝓘(ℝ,E) M n) (c : ℝ)
    (h : value x (extChartAt 𝓘(ℝ,E) x x) L.toContinuousLinearMap n α =
      c • value x (extChartAt 𝓘(ℝ,E) x x) L.toContinuousLinearMap n β) :
    α x = c • β x := by
  have hr : representative x (extChartAt 𝓘(ℝ,E) x x) L.toContinuousLinearMap n α =
      c • representative x (extChartAt 𝓘(ℝ,E) x x) L.toContinuousLinearMap n β :=
    Subtype.ext h
  have hl : localForm x (extChartAt 𝓘(ℝ,E) x x) L.toContinuousLinearMap n α =
      c • localForm x (extChartAt 𝓘(ℝ,E) x x) L.toContinuousLinearMap n β := by
    rw [← representative_pairing, ← representative_pairing, hr, toContinuous_smul]
  have hc : inChartModel x α (extChartAt 𝓘(ℝ,E) x x) =
      inChartModel x (c • β) (extChartAt 𝓘(ℝ,E) x x) := by
    rw [inChartModel_smul]
    ext v
    have hv := congrArg (fun γ => γ (fun i => L.symm (v i))) hl
    simp only [localForm, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousLinearEquiv.coe_coe] at hv
    have hvec : (⇑L ∘ fun i => L.symm (v i)) = v := by
      funext i
      exact L.apply_symm_apply (v i)
    rw [hvec] at hv
    exact hv
  have ht := congrArg (fun γ : E [⋀^Fin n]→L[ℝ] ℝ =>
    γ.compContinuousLinearMap (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) x) x)) hc
  exact (inChartModel_center_transport α x).symm.trans
    (ht.trans (inChartModel_center_transport (c • β) x))

end
end QuaternionicSymmetry.ManifoldFormExteriorReflection
