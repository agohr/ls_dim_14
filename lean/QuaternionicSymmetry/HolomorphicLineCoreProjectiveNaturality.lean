import QuaternionicSymmetry.HolomorphicLineCoreProjectiveFaithfulness

/-! Exact naturality of the complete evaluation functional under a genuine
linearized self-map of a represented holomorphic line.  The scalar is the
image of `1` in the actual one-dimensional fiber.  This is the compact-side
identity needed before discussing any complex-torus preservation of the
projective image; it does not assert algebraicity or preservation by a
complexified action. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveNaturality

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{u} (B := B) IB)

/-- Pulling the evaluation functional back by the inverse section map is
exactly evaluation at the moved point, up to the true fiber multiplier. -/
theorem evaluation_naturality
    (f : B → B)
    (Φ : ∀ x : B, L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (f x))
    (T : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB L)
    (hT : ∀ (s : GlobalSections IB L) (x : B),
      (T s) (f x) = Φ x (s x))
    (x : B) :
    ∃ c : ℂˣ, evaluation IB L (f x) =
      (c : ℂ) • (evaluation IB L x).comp T.symm.toLinearMap := by
  let φ : ℂ ≃ₗ[ℂ] ℂ := Φ x
  have hc : φ 1 ≠ 0 := by
    intro h
    have h' : (1 : ℂ) = 0 := φ.injective (by simpa using h)
    exact one_ne_zero h'
  refine ⟨Units.mk0 (φ 1) hc, ?_⟩
  apply LinearMap.ext
  intro s
  let ev : GlobalSections IB L → B → ℂ := fun u y => u y
  have hs := hT (T.symm s) x
  simp only [LinearEquiv.apply_symm_apply] at hs
  have hΦ : φ (ev (T.symm s) x) = φ 1 * ev (T.symm s) x := by
    have h := φ.map_smul (ev (T.symm s) x) (1 : ℂ)
    simpa [smul_eq_mul, mul_comm] using h
  change ev s (f x) = φ (ev (T.symm s) x) at hs
  exact hs.trans hΦ

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveNaturality
