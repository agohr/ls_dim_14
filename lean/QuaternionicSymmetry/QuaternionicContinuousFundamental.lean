import QuaternionicSymmetry.ExteriorContinuousWedge
import QuaternionicSymmetry.QuaternionicFundamentalDegree
import QuaternionicSymmetry.VectorBundleFrameTransitions
import QuaternionicSymmetry.LocalConnectionForms

/-! The exterior quaternionic fundamental form equals the normalized sum of
Kähler wedge squares as a continuous alternating four-form. -/
namespace QuaternionicSymmetry.QuaternionicContinuousFundamental

open Module QuaternionicFundamental ExteriorContinuousPairing ExteriorContinuousWedge
  ContinuousWedge VectorBundleFrameTransitions

noncomputable section
set_option maxHeartbeats 800000
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def omegaPower (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (t : Fin 3) : Power V 2 :=
  ⟨(omega Q b t).val, omega_mem_degree Q b t⟩

def fundamentalPower (Q : QuaternionicStructure V) (b : Basis ι ℝ V) : Power V 4 :=
  ⟨(form Q b).val, form_mem_degree Q b⟩

def kahler (Q : QuaternionicStructure V) (t : Fin 3) : V [⋀^Fin 2]→L[ℝ] ℝ :=
  (1 / 2 : ℝ) • LocalConnectionForms.alternatingPart
    ((innerSL ℝ).comp (quaternionicGenerator Q t))

def fundamental (Q : QuaternionicStructure V) : V [⋀^Fin 4]→L[ℝ] ℝ :=
  ∑ t : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ) (kahler Q t) (kahler Q t)

theorem toContinuous_metric_two (b : Basis ι ℝ V) (A : V →L[ℝ] V) :
    toContinuous 2 (HyperholomorphicExterior.form b A.toLinearMap) =
      (1 / 2 : ℝ) • LocalConnectionForms.alternatingPart ((innerSL ℝ).comp A) := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  change toContinuous 2
    (BilinearExterior.ofBilinear b (HyperholomorphicExterior.innerBilinear A.toLinearMap))
      ![v 0, v 1] = _
  rw [toContinuous_ofBilinear]
  simp only [HyperholomorphicExterior.innerBilinear_apply,
    ContinuousAlternatingMap.smul_apply, LocalConnectionForms.alternatingPart_apply,
    ContinuousLinearMap.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.coe_coe, smul_eq_mul]
  change (_ - _) / 2 = (1 / 2 : ℝ) * (inner ℝ (A (v 0)) (v 1) - inner ℝ (A (v 1)) (v 0))
  ring

theorem toContinuous_omegaPower (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (t : Fin 3) : toContinuous 2 (omegaPower Q b t) = kahler Q t := by
  have he : omegaPower Q b t =
      HyperholomorphicExterior.form b (quaternionicGenerator Q t).toLinearMap := by
    fin_cases t <;> rfl
  rw [he]
  exact toContinuous_metric_two b _

omit [FiniteDimensional ℝ V] in
theorem fundamentalPower_eq (Q : QuaternionicStructure V) (b : Basis ι ℝ V) :
    fundamentalPower Q b = ∑ t : Fin 3, mulPower (omegaPower Q b t) (omegaPower Q b t) := by
  apply Subtype.ext
  simp only [fundamentalPower, Submodule.coe_sum, mulPower, omegaPower]
  change ((∑ t : Fin 3, omega Q b t ^ 2 : E V) : ExteriorAlgebra ℝ (Module.Dual ℝ V)) = _
  simp only [AddSubmonoidClass.coe_finset_sum, pow_two]
  apply Finset.sum_congr rfl
  intro t ht
  rfl

theorem toContinuous_fundamentalPower (Q : QuaternionicStructure V) (b : Basis ι ℝ V) :
    toContinuous 4 (fundamentalPower Q b) = fundamental Q := by
  rw [fundamentalPower_eq]
  change (toContinuousLinear 4) (∑ t : Fin 3, mulPower (omegaPower Q b t) (omegaPower Q b t)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  change toContinuous (2+2) (mulPower (omegaPower Q b t) (omegaPower Q b t)) = _
  rw [toContinuous_mulPower, toContinuous_omegaPower]

end
end QuaternionicSymmetry.QuaternionicContinuousFundamental
