import QuaternionicSymmetry.ComplexLocallyAnalyticRealIdentity
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The one-variable identity theorem for genuine holomorphic line sections.
The proof uses the line core's local trivializations, not a purported global
holomorphicity of its preferred fiber coordinate. -/

namespace QuaternionicSymmetry.HolomorphicLineSectionIdentity

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.ComplexLocallyAnalyticZeroSet
open scoped Manifold ContDiff Topology
noncomputable section
universe u

variable (L : LineCore.{u} (B := ℂ) 𝓘(ℂ, ℂ))

/-- The actual zero set of a holomorphic line section on `ℂ` is locally
defined by analytic scalar functions in the bundle's genuine charts. -/
theorem locallyAnalytic_zeroSet (s : GlobalSections 𝓘(ℂ, ℂ) L) :
    LocallyAnalyticZeroSet {z : ℂ | s z = 0} := by
  letI := L.holomorphic
  intro z
  let i := L.core.indexAt z
  let e := trivializationAt ℂ L.core.Fiber z
  have hz : z ∈ e.baseSet := L.core.mem_baseSet_at z
  let f : ℂ → ℂ := fun w => (e ⟨w, s w⟩).2
  have hs : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ f z :=
    (e.contMDiffAt_section_iff hz).1 (s.contMDiff z)
  have hs1 : ContDiffAt ℂ 1 f z := hs.contDiffAt.of_le (by simp)
  refine ⟨f, Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_, ?_⟩
  · exact (hs1.eventually (by simp)).mono (fun _ h => h.differentiableAt_one)
  · filter_upwards [(L.core.isOpen_baseSet i).mem_nhds hz] with w hw
    change s w = 0 ↔ L.core.coordChange (L.core.indexAt w) i w (s w) = 0
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      have hc := L.core.coordChange_comp (L.core.indexAt w) i
        (L.core.indexAt w) w ⟨⟨L.core.mem_baseSet_at w, hw⟩,
          L.core.mem_baseSet_at w⟩ (s w)
      rw [h, map_zero, L.core.coordChange_self _ _ (L.core.mem_baseSet_at w)] at hc
      exact hc.symm

/-- Accumulation of actual zero fibers forces the section to vanish
everywhere, even when its line core has no chosen global trivialization. -/
theorem zero_of_frequently (s : GlobalSections 𝓘(ℂ, ℂ) L) {z : ℂ}
    (hz : ∃ᶠ w in 𝓝[≠] z, s w = 0) : ∀ w, s w = 0 := by
  have hall := eq_univ_of_frequently (locallyAnalytic_zeroSet L s) hz
  intro w
  exact show w ∈ {z : ℂ | s z = 0} from hall ▸ Set.mem_univ w

/-- Vanishing on the real axis is enough for a genuine holomorphic section
on the complex plane to vanish everywhere. -/
theorem zero_of_real (s : GlobalSections 𝓘(ℂ, ℂ) L)
    (hreal : ∀ t : ℝ, s (t : ℂ) = 0) : ∀ w, s w = 0 := by
  have hall := eq_univ_of_real (locallyAnalytic_zeroSet L s) hreal
  intro w
  exact show w ∈ {z : ℂ | s z = 0} from hall ▸ Set.mem_univ w

/-- Finite-dimensional real-axis uniqueness, proved using actual pullback
line cores on every complex coordinate line. -/
theorem zero_of_real_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : LineCore.{u} (B := ι → ℂ) 𝓘(ℂ, ι → ℂ))
    (s : GlobalSections 𝓘(ℂ, ι → ℂ) K)
    (hreal : ∀ t : ι → ℝ, s (fun i => (t i : ℂ)) = 0) : ∀ z, s z = 0 := by
  have hslice : ∀ (z : ι → ℂ) (i : ι),
      LocallyAnalyticZeroSet {w : ℂ | s (Function.update z i w) = 0} := by
    intro z i
    have hu : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ι → ℂ) ∞ (Function.update z i) :=
      (contDiff_update ∞ z i).contMDiff
    let K' := pullbackLineCore 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ℂ) K (Function.update z i) hu
    let s' := restrictSection 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, ℂ) K (Function.update z i) hu s
    exact locallyAnalytic_zeroSet K' s'
  have hall := eq_univ_of_real_pi (ι := ι) (S := {w | s w = 0}) hslice hreal
  intro z
  exact show z ∈ {w | s w = 0} from hall ▸ Set.mem_univ z

end
end QuaternionicSymmetry.HolomorphicLineSectionIdentity
