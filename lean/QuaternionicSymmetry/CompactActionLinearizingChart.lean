import QuaternionicSymmetry.CompactParameterSmoothIntegration
import QuaternionicSymmetry.SmoothInverseChart
import Mathlib.MeasureTheory.Group.Integral

/-! The averaged local chart of a compact action has identity differential
and intertwines the action with its actual tangent representation. -/
namespace QuaternionicSymmetry.CompactActionLinearizingChart
open MeasureTheory Set
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000

variable {A E K : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [ChartedSpace A K] [IsManifold 𝓘(ℝ,A) ∞ K] [LieGroup 𝓘(ℝ,A) ∞ K]
  [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
  (a : K × E → E) (ρ : K →* E →L[ℝ] E)
  {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
  (ha : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ a (univ ×ˢ U))
  (hρ : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,E →L[ℝ] E) ∞ ρ)

def averagedChart (x : E) : E := ∫ g, ρ g⁻¹ (a (g,x)) ∂μ

include ha hρ in
lemma integrand_smooth :
    ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : K × E => ρ p.1⁻¹ (a p)) (univ ×ˢ U) := by
  exact ((hρ.comp (contMDiff_inv 𝓘(ℝ,A) ∞)).comp contMDiff_fst).contMDiffOn.clm_apply ha

include hU ha hρ in
lemma averaged_smooth : ContDiffOn ℝ ∞ (averagedChart μ a ρ) U :=
  CompactParameterSmoothIntegration.integral_contDiffOn μ hU (integrand_smooth a ρ ha hρ)

lemma averaged_zero (hz : ∀ g, a (g,0) = 0) : averagedChart μ a ρ 0 = 0 := by
  simp only [averagedChart,hz,map_zero,integral_zero]

include hU h0 ha hρ in
lemma averaged_derivative (hd : ∀ g, HasFDerivAt (fun x => a (g,x)) (ρ g) 0) :
    HasFDerivAt (averagedChart μ a ρ) (ContinuousLinearMap.id ℝ E) 0 := by
  have hh := CompactParameterSmoothIntegration.integral_hasFDerivAt μ hU
    (integrand_smooth a ρ ha hρ) h0
  have hd' (g : K) :
      fderiv ℝ (fun x => ρ g⁻¹ (a (g,x))) 0 = ContinuousLinearMap.id ℝ E := by
    have hc := (ρ g⁻¹).hasFDerivAt.comp 0 (hd g)
    have heq : (ρ g⁻¹).comp (ρ g) = ContinuousLinearMap.id ℝ E := by
      change ρ g⁻¹ * ρ g = 1
      rw [← map_mul,inv_mul_cancel,map_one]
    simpa only [heq] using hc.fderiv
  simpa only [hd', integral_const, probReal_univ, one_smul] using hh

include ha hρ in
lemma averaged_equivariant
    (hmul : ∀ g h x, x ∈ U → a (g,a (h,x)) = a (g*h,x))
    (h : K) {x : E} (hx : x ∈ U) :
    averagedChart μ a ρ (a (h,x)) = ρ h (averagedChart μ a ρ x) := by
  have hcont : Continuous (fun g => ρ g⁻¹ (a (g,x))) :=
    ((integrand_smooth a ρ ha hρ).continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _,hx⟩))
  have hi := hcont.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  rw [averagedChart,averagedChart,← (ρ h).integral_comp_comm hi]
  calc
    (∫ g, ρ g⁻¹ (a (g,a (h,x))) ∂μ) =
        ∫ g, ρ h (ρ (g*h)⁻¹ (a (g*h,x))) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      rw [hmul g h x hx]
      have heq : ρ h * ρ (g*h)⁻¹ = ρ g⁻¹ := by
        rw [← map_mul]
        congr 1
        simp
      exact (congrArg (fun D : E →L[ℝ] E => D (a (g*h,x))) heq).symm
    _ = ∫ g, ρ h (ρ g⁻¹ (a (g,x))) ∂μ := integral_mul_right_eq_self (μ := μ) (fun g => ρ h (ρ g⁻¹ (a (g,x)))) h

include hU h0 ha hρ in
lemma exists_averaged_inverse_chart
    (hz : ∀ g, a (g,0) = 0)
    (hd : ∀ g, HasFDerivAt (fun x => a (g,x)) (ρ g) 0) :
    ∃ e : OpenPartialHomeomorph E E, 0 ∈ e.source ∧ e.source ⊆ U ∧
      (e : E → E) = averagedChart μ a ρ ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨e,he0,heU,heq,hesm,hesym⟩ := SmoothInverseChart.exists_inverse_chart hU
    (averaged_smooth μ a ρ hU ha hρ) h0 (ContinuousLinearEquiv.refl ℝ E)
    (averaged_derivative μ a ρ hU h0 ha hρ hd)
  exact ⟨e,he0,heU,heq,by rw [heq]; exact averaged_zero μ a ρ hz,hesm,hesym⟩

end
end QuaternionicSymmetry.CompactActionLinearizingChart
