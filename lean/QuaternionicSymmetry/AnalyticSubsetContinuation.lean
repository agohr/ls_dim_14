import QuaternionicSymmetry.HolomorphicEmbeddingLocalEquations
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Analytic continuation of a holomorphic curve into a closed analytic
subset. This uses local defining equations and the one-variable identity
theorem, without algebraicity of the subset. -/
namespace QuaternionicSymmetry.AnalyticSubsetContinuation
open HolomorphicEmbeddingLocalEquations
open Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
variable {F B : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace B] [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]

lemma eventually_mem_of_frequently
    {A : Set B} (hA : LocalHolomorphicEquations (F := F) A)
    {f : ℂ → B} (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,F) ∞ f)
    {z : ℂ} (hz : f z ∈ A)
    (hfreq : ∃ᶠ w in 𝓝[≠] z, f w ∈ A) :
    ∀ᶠ w in 𝓝 z, f w ∈ A := by
  obtain ⟨V, hV, hzV, d, h, hh, heq⟩ := hA (f z) hz
  have hnear : ∀ᶠ w in 𝓝 z, f w ∈ V := hf.continuous.continuousAt (hV.mem_nhds hzV)
  have hc : ContDiffAt ℂ 1 (h ∘ f) z :=
    (hh.comp z (hf.contMDiffAt.of_le (by simp))).contDiffAt
  have han : AnalyticAt ℂ (h ∘ f) z := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hc.eventually (by simp)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hzero : ∃ᶠ w in 𝓝[≠] z, (h ∘ f) w = 0 := by
    apply (hfreq.and_eventually (hnear.filter_mono nhdsWithin_le_nhds)).mono
    intro w hw
    have hmem : f w ∈ A ∩ V := hw
    rw [heq] at hmem
    exact hmem.2
  have hznear := han.frequently_zero_iff_eventually_zero.mp hzero
  filter_upwards [hnear, hznear] with w hw hz0
  have hmem : f w ∈ V ∩ h ⁻¹' {0} := ⟨hw,hz0⟩
  rw [← heq] at hmem
  exact hmem.1

/-- A non-isolated intersection with a closed analytic set forces an
entire holomorphic curve to lie in that set. -/
theorem mapsTo_of_frequently
    {A : Set B} (hA : LocalHolomorphicEquations (F := F) A) (hClosed : IsClosed A)
    {f : ℂ → B} (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,F) ∞ f)
    {z : ℂ} (hz : f z ∈ A)
    (hfreq : ∃ᶠ w in 𝓝[≠] z, f w ∈ A) : ∀ w, f w ∈ A := by
  let S := f ⁻¹' A
  let U := interior S
  have hS : IsClosed S := hClosed.preimage hf.continuous
  have hzu : z ∈ U := mem_interior_iff_mem_nhds.mpr
    (eventually_mem_of_frequently hA hf hz hfreq)
  have hclosedU : IsClosed U := by
    apply isClosed_of_closure_subset
    intro w hw
    have hwS : w ∈ S := (closure_minimal interior_subset hS) hw
    by_cases hwu : w ∈ U
    · exact hwu
    · have hwcl : w ∈ closure (U \ {w}) := by
        have heq : U \ {w} = U := by ext t; simp only [Set.mem_diff, Set.mem_singleton_iff]; exact ⟨And.left, fun ht => ⟨ht, fun heq => hwu (heq ▸ ht)⟩⟩
        rwa [heq]
      have hfr : ∃ᶠ t in 𝓝[≠] w, f t ∈ A :=
        (mem_closure_ne_iff_frequently_within.mp hwcl).mono
          (fun t ht => (interior_subset : U ⊆ S) ht)
      exact mem_interior_iff_mem_nhds.mpr (eventually_mem_of_frequently hA hf hwS hfr)
  have hUall : U = univ := IsClopen.eq_univ ⟨hclosedU,isOpen_interior⟩ ⟨z,hzu⟩
  intro w
  exact (interior_subset : U ⊆ S) (show w ∈ U by rw [hUall]; trivial)

end
end QuaternionicSymmetry.AnalyticSubsetContinuation
