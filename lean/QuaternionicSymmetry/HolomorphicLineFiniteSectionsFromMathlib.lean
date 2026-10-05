import QuaternionicSymmetry.HolomorphicSectionSamplingBounds
import QuaternionicSymmetry.HolomorphicLineFiniteSectionsSource

/-! Finite-dimensionality of actual holomorphic line sections on a compact
complex manifold, proved by finite sampling and local Schwarz estimates. -/
namespace QuaternionicSymmetry.HolomorphicLineFiniteSectionsFromMathlib
open HolomorphicSectionSamplingCharts HolomorphicSectionSamplingBounds
open HolomorphicLineCoreClasses HolomorphicLineCorePullback FiniteHolomorphicSampling
open scoped Manifold ContDiff
noncomputable section

theorem compactHolomorphicLineSectionFiniteness :
    HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness := by
  intro B F _ _ _ _ _ _ _ _ _ L
  classical
  cases isEmpty_or_nonempty B with
  | inl h =>
    letI := h
    letI : Subsingleton (GlobalSections 𝓘(ℂ,F) L) := ⟨by
      intro s t
      ext x
      exact isEmptyElim x⟩
    infer_instance
  | inr h =>
    letI := h
    obtain ⟨I,hfin,c,hcover⟩ := finite_sampling_cover L
    letI := hfin
    letI : Nonempty I := ⟨(hcover (Classical.arbitrary B)).choose⟩
    obtain ⟨C,hC,hbound⟩ := uniform_outer_bound L c hcover
    exact finiteDimensional_of_sampling
      (fun i => (c i).center) (fun i => (c i).radius) (fun i => (c i).radius_pos)
      (fun i => (c i).evaluation) (fun s i => (c i).holomorphic_evaluation s)
      C hC hbound (section_eq_zero_of_inner_evaluations L c hcover)

end
end QuaternionicSymmetry.HolomorphicLineFiniteSectionsFromMathlib
