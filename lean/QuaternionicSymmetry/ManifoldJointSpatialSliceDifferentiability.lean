import QuaternionicSymmetry.ManifoldLocalC1Neighborhood

/-! Nearby spatial slices of a pointwise C∞ joint family are
differentiable, even when the parameter subspace has no manifold atlas. -/
namespace QuaternionicSymmetry.ManifoldJointSpatialSliceDifferentiability

open Manifold
open ManifoldLocalC1Neighborhood
open scoped Manifold ContDiff
noncomputable section

variable {FG HG G FB HB B FC HC C P : Type*}
  [NormedAddCommGroup FG] [NormedSpace ℝ FG]
  [TopologicalSpace HG] [TopologicalSpace G] [ChartedSpace HG G]
  [NormedAddCommGroup FB] [NormedSpace ℝ FB]
  [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FC] [NormedSpace ℝ FC]
  [TopologicalSpace HC] [TopologicalSpace C] [ChartedSpace HC C]
  [TopologicalSpace P]
  {IG : ModelWithCorners ℝ FG HG}
  {IB : ModelWithCorners ℝ FB HB}
  {IC : ModelWithCorners ℝ FC HC}
  [IsManifold IG 1 G] [IsManifold IB 1 B] [IsManifold IC 1 C]

theorem eventually_mdifferentiableAt_spatial_slices
    {F : G × B → C} {g₀ : G} {b₀ : B}
    (hF : ContMDiffAt (IG.prod IB) IC ∞ F (g₀,b₀))
    {gp : P → G} {bp : P → B} {p₀ : P}
    (hgp : ContinuousAt gp p₀) (hbp : ContinuousAt bp p₀)
    (hgp0 : gp p₀ = g₀) (hbp0 : bp p₀ = b₀) :
    ∀ᶠ p in nhds p₀,
      MDifferentiableAt IB IC (fun b => F (gp p,b)) (bp p) := by
  have hpair : ContinuousAt (fun p : P => (gp p,bp p)) p₀ :=
    hgp.prodMk hbp
  have hnear : ∀ᶠ p in nhds p₀,
      MDifferentiableAt (IG.prod IB) IC F (gp p,bp p) := by
    have h := eventually_mdifferentiableAt_of_contMDiffAt hF
    rw [← hgp0, ← hbp0] at h
    exact hpair.tendsto.eventually h
  filter_upwards [hnear] with p hp
  have hinsert : MDifferentiableAt IB (IG.prod IB)
      (fun b : B => (gp p,b)) (bp p) :=
    ((contMDiff_const.prodMk contMDiff_id :
      ContMDiff IB (IG.prod IB) 1 (fun b : B => (gp p,b))).mdifferentiableAt (by simp))
  exact hp.comp (bp p) hinsert

end
end QuaternionicSymmetry.ManifoldJointSpatialSliceDifferentiability
