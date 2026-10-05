import QuaternionicSymmetry.CompactLieOneParameterSubgroup
import QuaternionicSymmetry.SmoothLieHomDerivativeBracket

/-! Naturality of the actual one-parameter subgroup under smooth homomorphisms. -/
namespace QuaternionicSymmetry.CompactLieOneParameterNaturality
open CompactLieOneParameterSubgroup
open scoped Manifold ContDiff
noncomputable section
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [T2Space G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H]
  [IsManifold 𝓘(ℝ,F) ∞ H] [LieGroup 𝓘(ℝ,F) ∞ H] [CompactSpace H] [T2Space H]

theorem map_curve (f : G →* H) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (v : GroupLieAlgebra 𝓘(ℝ,E) G) (t : ℝ) :
    f (curve v t) = curve (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1 v) t := by
  let w : GroupLieAlgebra 𝓘(ℝ,F) H := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1 v
  have hi : IsMIntegralCurve (fun s => f (curve v s)) (mulInvariantVectorField w) := by
    intro s
    have hd := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp s (curve_integral v s)
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f (curve v s)
      (a • mulInvariantVectorField v (curve v s)) =
      a • mulInvariantVectorField w (f (curve v s))
    rw [map_smul, SmoothLieHomDerivativeBracket.mfderiv_mulInvariantVectorField f hf]
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (field_c1 w)
    hi (curve_integral w) (t₀ := 0) (by simp)
  exact congrFun he t

end
end QuaternionicSymmetry.CompactLieOneParameterNaturality
