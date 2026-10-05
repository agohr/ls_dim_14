import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-! Full alternation as a bounded linear operator. This supplies the analytic
operator needed to construct and differentiate exterior products. -/

namespace QuaternionicSymmetry.ContinuousAlternation

noncomputable section

variable {ι E F G : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def alternationLinear : ContinuousMultilinearMap ℝ (fun _ : ι => E) F →ₗ[ℝ]
    E [⋀^ι]→L[ℝ] F where
  toFun := ContinuousMultilinearMap.alternatization
  map_add' := map_add ContinuousMultilinearMap.alternatization
  map_smul' r f := by
    ext v
    simp only [ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousAlternatingMap.smul_apply,
      RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    exact smul_comm _ _ _

theorem norm_alternation_le (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) :
    ‖alternationLinear f‖ ≤ (Fintype.card ι).factorial * ‖f‖ := by
  change ‖∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ‖ ≤ _
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f.domDomCongr σ‖ := norm_sum_le _ _
    _ = (Fintype.card ι).factorial * ‖f‖ := by
      simp [norm_units_zsmul, Fintype.card_perm]

def alternationCLM : ContinuousMultilinearMap ℝ (fun _ : ι => E) F →L[ℝ]
    E [⋀^ι]→L[ℝ] F :=
  (alternationLinear (ι := ι) (E := E) (F := F)).mkContinuous
    ((Fintype.card ι).factorial : ℝ) (fun f => norm_alternation_le f)

theorem alternationCLM_apply (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F)
    (v : ι → E) :
    alternationCLM f v = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ) :=
  ContinuousMultilinearMap.alternatization_apply_apply f v

theorem alternation_of_alternating (f : E [⋀^ι]→L[ℝ] F) :
    alternationCLM f.toContinuousMultilinearMap = (Fintype.card ι).factorial • f := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change (ContinuousMultilinearMap.alternatization f.toContinuousMultilinearMap).toAlternatingMap = _
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  exact AlternatingMap.coe_alternatization f.toAlternatingMap

theorem alternation_comp (L : F →L[ℝ] G)
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) F) :
    alternationCLM (L.compContinuousMultilinearMap f) =
      L.compContinuousAlternatingMap (alternationCLM f) := by
  ext v
  simp [alternationCLM_apply, map_sum]

theorem differentiableAt_alternation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ContinuousMultilinearMap ℝ (fun _ : ι => E) F) (x : X)
    (hf : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun y => alternationCLM (f y)) x :=
  (alternationCLM (ι := ι) (E := E) (F := F)).differentiableAt.comp x hf

theorem fderiv_alternation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ContinuousMultilinearMap ℝ (fun _ : ι => E) F) (x : X)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => alternationCLM (f y)) x = alternationCLM.comp (fderiv ℝ f x) :=
  ((alternationCLM (ι := ι) (E := E) (F := F)).hasFDerivAt.comp x hf.hasFDerivAt).fderiv

end
end QuaternionicSymmetry.ContinuousAlternation
