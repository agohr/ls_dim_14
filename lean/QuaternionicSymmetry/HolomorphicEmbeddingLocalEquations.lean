import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Local holomorphic equations for an embedded immersion. Only a holomorphic
`C¹` germ of each defining function is needed for one-variable continuation.
The equations are constructed by a left inverse of the immersion derivative
and the inverse function theorem; no proper-image theorem is used. -/
namespace QuaternionicSymmetry.HolomorphicEmbeddingLocalEquations
open Filter Set Function
open scoped Manifold ContDiff Topology
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ,F) ∞ N]

/-- Local zero-locus equations whose germs are complex `C¹`. -/
def LocalHolomorphicEquations (A : Set N) : Prop :=
  ∀ x ∈ A, ∃ V : Set N, IsOpen V ∧ x ∈ V ∧
    ∃ (d : ℕ) (h : N → Fin d → ℂ),
      ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,Fin d → ℂ) 1 h x ∧
      A ∩ V = V ∩ h ⁻¹' {0}

/-- An embedded holomorphic immersion has local holomorphic equations. -/
theorem range_localHolomorphicEquations {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ∞ f)
    (hEmb : Topology.IsEmbedding f)
    (hImm : ∀ x, Function.Injective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x)) :
    LocalHolomorphicEquations (F := F) (range f) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  rintro _ ⟨x,rfl⟩
  let e := extChartAt 𝓘(ℂ,E) x
  let c := extChartAt 𝓘(ℂ,F) (f x)
  let a := e x
  let b := c (f x)
  let g := writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,F) x f
  have hga : g a = b := by simp [g, writtenInExtChartAt, a, b, e, c]
  have hg : ContDiffAt ℂ ∞ g a := by
    simpa [g, a, e] using (contMDiffAt_iff.mp (hf x)).2
  have hgD : HasFDerivAt g (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x) a := by
    simpa [g, a, e] using (hf.mdifferentiable (by simp) x).hasMFDerivAt.2
  have hinj : Function.Injective (fderiv ℂ g a) := by rw [hgD.fderiv]; exact hImm x
  obtain ⟨L,hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hφ : ContDiffAt ℂ ∞ (L ∘ g) a := L.contDiff.contDiffAt.comp a hg
  have hφD : HasFDerivAt (L ∘ g) (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E) a := by
    convert L.hasFDerivAt.comp a hgD using 1
    apply ContinuousLinearMap.ext
    intro v
    simpa only [hgD.fderiv] using (hL v).symm
  let ψ := hφ.localInverse hφD (by simp)
  have hψb : ψ (L b) = a := by simpa [ψ, hga] using hφ.localInverse_apply_image hφD (by simp)
  have hψ : ContDiffAt ℂ ∞ ψ (L b) := by simpa [ψ, hga] using hφ.to_localInverse hφD (by simp)
  have hleft : ∀ᶠ v in 𝓝 a, ψ (L (g v)) = v :=
    (hφ.hasStrictFDerivAt' hφD (by simp)).eventually_left_inverse
  have hSource : ∀ᶠ u in 𝓝 x, u ∈ e.source ∧ ψ (L (c (f u))) = e u := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ,E)) x,
      (continuousAt_extChartAt (I := 𝓘(ℂ,E)) x).eventually hleft] with u hu hv
    refine ⟨hu, ?_⟩
    change ψ (L (c (f (e.symm (e u))))) = e u at hv
    rwa [e.left_inv hu] at hv
  rw [hEmb.isInducing.nhds_eq_comap] at hSource
  have hSource' : ∀ᶠ y in 𝓝 (f x), ∀ u, f u = y →
      u ∈ e.source ∧ ψ (L (c (f u))) = e u := Filter.mem_comap'.mp hSource
  let H : F → F := fun v => v - g (ψ (L v))
  have hH : ContDiffAt ℂ ∞ H b := by
    apply contDiffAt_id.sub
    have hg' : ContDiffAt ℂ ∞ g (ψ (L b)) := hψb.symm ▸ hg
    exact ContDiffAt.comp (f := ψ ∘ (L : F → E)) (g := g) b hg'
      (hψ.comp b L.contDiff.contDiffAt)
  let R : N → N := fun y => f (e.symm (ψ (L (c y))))
  have hRbase : R (f x) = f x := by simp [R, b, hψb, a, e]
  have hR : ContinuousAt R (f x) := by
    have hi : ContinuousAt (fun y => ψ (L (c y))) (f x) :=
      ContinuousAt.comp (f := fun y => L (c y)) (g := ψ) hψ.continuousAt
        (ContinuousAt.comp (f := c) (g := (L : F → E))
          L.continuous.continuousAt (continuousAt_extChartAt (I := 𝓘(ℂ,F)) (f x)))
    have he : ContinuousAt e.symm (ψ (L (c (f x)))) := by
      rw [show c (f x) = b from rfl, hψb]
      exact continuousAt_extChartAt_symm (I := 𝓘(ℂ,E)) x
    exact ContinuousAt.comp (f := fun y => e.symm (ψ (L (c y)))) (g := f)
      hf.continuous.continuousAt (ContinuousAt.comp (f := fun y => ψ (L (c y)))
        (g := e.symm) he hi)
  have hTarget : ∀ᶠ y in 𝓝 (f x), y ∈ c.source ∧ R y ∈ c.source := by
    have hc : ∀ᶠ y in 𝓝 (f x), y ∈ c.source :=
      extChartAt_source_mem_nhds (I := 𝓘(ℂ,F)) (f x)
    have hr : ∀ᶠ y in 𝓝 (f x), R y ∈ c.source := hR (hRbase.symm ▸ hc)
    exact hc.and hr
  obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp (hSource'.and hTarget)
  let Q := (Module.finBasis ℂ F).equivFun.toContinuousLinearEquiv
  refine ⟨V,hV,hxV,Module.finrank ℂ F,(fun y => Q (H (c y))), ?_, ?_⟩
  · apply ContMDiffAt.of_le (n := ∞) _ (by simp)
    exact Q.contDiff.contMDiff.contMDiffAt.comp (f x)
      (hH.contMDiffAt.comp (f x) (contMDiffAt_extChartAt (I := 𝓘(ℂ,F)) (x := f x)))
  · ext y
    constructor
    · rintro ⟨⟨u,rfl⟩,hy⟩
      have hu := (hVsub hy).1 u rfl
      refine ⟨hy, ?_⟩
      change Q (c (f u) - g (ψ (L (c (f u))))) = 0
      rw [hu.2]
      change Q (c (f u) - c (f (e.symm (e u)))) = 0
      rw [e.left_inv hu.1, sub_self, map_zero]
    · intro hy
      have hz : H (c y) = 0 := Q.injective (by simpa using hy.2)
      have heq : c y = c (R y) := sub_eq_zero.mp hz
      have hmem := (hVsub hy.1).2
      have hyR : y = R y := c.injOn hmem.1 hmem.2 heq
      exact ⟨hyR.symm ▸ mem_range_self (e.symm (ψ (L (c y)))),hy.1⟩

end
end QuaternionicSymmetry.HolomorphicEmbeddingLocalEquations
