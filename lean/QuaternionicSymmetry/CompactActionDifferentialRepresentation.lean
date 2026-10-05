import QuaternionicSymmetry.CompactActionFixedLocalChart

/-! The tangent representation and its smoothness are derived from the actual
joint action, rather than supplied as extra fixed-point hypotheses. -/
namespace QuaternionicSymmetry.CompactActionDifferentialRepresentation
open Set Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {A E K : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Group K] [TopologicalSpace K] [ChartedSpace A K]
  [IsManifold 𝓘(ℝ,A) ∞ K]
  (a : K × E → E) {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
  (ha : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ a (univ ×ˢ U))
  (hz : ∀ g, a (g,0) = 0)
  (h1 : ∀ x, x ∈ U → a (1,x) = x)
  (hmul : ∀ g h x, x ∈ U → a (g,a (h,x)) = a (g*h,x))

include hU h0 ha in
lemma action_hasFDerivAt (g : K) :
    HasFDerivAt (fun x => a (g,x)) (fderiv ℝ (fun x => a (g,x)) 0) 0 := by
  have h : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x => a (g,x)) 0 := (ha.contMDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,h0⟩)).comp 0
    (contMDiffAt_const.prodMk contMDiffAt_id)
  exact (h.contDiffAt.differentiableAt (by simp)).hasFDerivAt

/-- Derivative of a genuine local group action at its fixed origin. -/
def tangentRepresentation : K →* E →L[ℝ] E where
  toFun g := fderiv ℝ (fun x => a (g,x)) 0
  map_one' := by
    have heq : (fun x => a (1,x)) =ᶠ[𝓝 0] id := by
      filter_upwards [hU.mem_nhds h0] with x hx
      exact h1 x hx
    simpa using heq.fderiv_eq (𝕜 := ℝ)
  map_mul' g h := by
    have heq : (fun x => a (g*h,x)) =ᶠ[𝓝 0] (fun x => a (g,a (h,x))) := by
      filter_upwards [hU.mem_nhds h0] with x hx
      exact (hmul g h x hx).symm
    rw [heq.fderiv_eq]
    have hg := action_hasFDerivAt a hU h0 ha g
    have hh := action_hasFDerivAt a hU h0 ha h
    have hg' : HasFDerivAt (fun x => a (g,x)) (fderiv ℝ (fun x => a (g,x)) 0) (a (h,0)) := by
      rwa [hz]
    exact (hg'.comp 0 hh).fderiv

lemma tangentRepresentation_smooth :
    ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,E →L[ℝ] E) ∞
      (tangentRepresentation a (hU := hU) (h0 := h0) (ha := ha) (hz := hz) (h1 := h1) (hmul := hmul)) := by
  intro g
  change ContMDiffAt 𝓘(ℝ,A) 𝓘(ℝ,E →L[ℝ] E) ∞ (fun g => fderiv ℝ (fun x => a (g,x)) 0) g
  have hd := CompactParameterSmoothIntegration.partial_fderiv_smooth hU ha
  have hd' := hd.contMDiffAt (x := (g,0)) ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ g,h0⟩)
  exact ContMDiffAt.comp (f := fun g : K => (g,(0 : E))) g hd'
    (contMDiffAt_id.prodMk contMDiffAt_const)

end
end QuaternionicSymmetry.CompactActionDifferentialRepresentation
