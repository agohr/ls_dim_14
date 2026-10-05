import QuaternionicSymmetry.ManifoldTangentMapContinuousAt

/-! A pointwise C∞ manifold map is C¹, hence differentiable, throughout
some neighborhood of its base point. -/
namespace QuaternionicSymmetry.ManifoldLocalC1Neighborhood

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {F H N F' H' N' : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [TopologicalSpace H'] [TopologicalSpace N'] [ChartedSpace H' N']
  {I : ModelWithCorners ℝ F H} {I' : ModelWithCorners ℝ F' H'}
  [IsManifold I 1 N] [IsManifold I' 1 N']

theorem eventually_mdifferentiableAt_of_contMDiffAt
    {f : N → N'} {x : N}
    (hf : ContMDiffAt I I' ∞ f x) :
    ∀ᶠ y in nhds x, MDifferentiableAt I I' f y := by
  have h1 : ContMDiffAt I I' 1 f x := hf.of_le (by simp)
  exact ((contMDiffAt_iff_contMDiffAt_nhds (I := I) (I' := I')
    (n := (1 : WithTop ℕ∞)) (by simp)).mp h1).mono
      (fun _ hy => hy.mdifferentiableAt (by simp))

end
end QuaternionicSymmetry.ManifoldLocalC1Neighborhood
