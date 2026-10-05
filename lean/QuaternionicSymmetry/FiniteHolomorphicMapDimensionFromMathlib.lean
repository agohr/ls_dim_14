import QuaternionicSymmetry.HolomorphicFiniteMapDimensionSource
import QuaternionicSymmetry.ManifoldFiniteFiberRank

/-! The finite-map dimension contract follows from the internal local rank
argument. Holomorphic maps are real smooth in the same charts; finite fibers
are locally isolated. Properness is not needed for this conclusion. -/

namespace QuaternionicSymmetry.FiniteHolomorphicMapDimensionFromMathlib

open FiniteFiberDifferentialRank ManifoldFiniteFiberRank ComplexProjectiveTopology
open scoped Manifold ContDiff Topology
open Filter Function Set Module
noncomputable section

theorem finiteHolomorphicMapDimension :
    HolomorphicFiniteMapDimensionSource.FiniteHolomorphicMapDimensionTheorem := by
  intro B F _ _ _ _ _ _ _ _ _ d f hf _hProper hFinite
  let a : B := Classical.choice inferInstance
  let e := chartAt F a
  let e' := chartAt (Fin d → ℂ) (f a)
  let U := coordinateDomain e e' (f := f)
  let g := e' ∘ f ∘ e.symm
  have hU : IsOpen U := isOpen_coordinateDomain e e' hf.continuous
  have hne : U.Nonempty := by
    refine ⟨e a, e.map_source (mem_chart_source F a), ?_⟩
    change f (e.symm (e a)) ∈ e'.source
    rw [e.left_inv (mem_chart_source F a)]
    exact mem_chart_source (Fin d → ℂ) (f a)
  have hg : ContDiffOn ℂ ∞ g U := by
    simpa [g, U, e, e', coordinateDomain] using (contMDiff_iff.mp hf).2 a (f a)
  have hIso : ∀ u ∈ U, ∀ᶠ x in 𝓝 u, g x = g u → x = u := by
    intro u hu
    exact isolated_fiber_in_coordinates e e' hu
      (eventually_eq_of_mem_finite (hFinite (f (e.symm u))) (e.symm u)) hf.continuous
  have hdim := finrank_le_of_locally_isolated_fibers hU hne (hg.restrict_scalars ℝ) hIso
  have hF : 2 * finrank ℂ F = finrank ℝ F := by
    simpa using Module.finrank_mul_finrank ℝ ℂ F
  have hTarget : finrank ℝ (Fin d → ℂ) = d * 2 := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [hTarget, ← hF] at hdim
  omega

end
end QuaternionicSymmetry.FiniteHolomorphicMapDimensionFromMathlib
