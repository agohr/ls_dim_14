import QuaternionicSymmetry.ManifoldTwistorRawComplexCovariance

/-!
# Derivative of the raw twistor chart at its center

At the twistor point whose base center is the chosen chart center, the
derivative of the raw base–sphere chart is the identity on the actual product
tangent model. The proof uses the preferred bundle trivialization derivative
and the derivative of the base chart at its center.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [Nontrivial E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem mfderiv_extChartAt_center (x : M) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) x) x =
      ContinuousLinearMap.id ℝ E := by
  simp only [mfderiv, mfld_simps]
  have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) x) x :=
    contMDiffAt_extChartAt
  have hmd : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E x) x := by
    simpa only [extChartAt, mfld_simps] using hs.mdifferentiableAt (by simp)
  rw [if_pos hmd]
  rw [fderivWithin_univ]
  have heq : ((chartAt E x) ∘ (chartAt E x).symm) =ᶠ[𝓝 ((chartAt E x) x)] id := by
    filter_upwards [(chartAt E x).open_target.mem_nhds
      (mem_chart_target E x)] with y hy
    exact (chartAt E x).right_inv hy
  rw [heq.fderiv_eq]
  simp

theorem fixedRawChart_center_mfderiv (z : SphereBundleTotal Q) :
    mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2))
      (fixedRawChart Q z.1) z =
        ContinuousLinearMap.id ℝ
          (TangentSpace ((𝓘(ℝ,E)).prod (𝓡 2)) z) := by
  let x := z.1
  let s : geometricSphere := z.2
  let L : SphereBundleTotal Q → M × geometricSphere :=
    fun w => (sphereCore Q).localTriv (achart E x) w
  let B : M × geometricSphere → E × geometricSphere :=
    fun w => ((extChartAt 𝓘(ℝ,E) x) w.1,w.2)
  have hL : MDifferentiableAt ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) L z := by
    have hx : x ∈ (sphereCore Q).baseSet (achart E x) :=
      (sphereCore Q).mem_baseSet_at x
    exact (fixedTriv_smoothAt Q x z hx).mdifferentiableAt (by simp)
  have hBbase : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) x) x := by
    have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
        (extChartAt 𝓘(ℝ,E) x) x := contMDiffAt_extChartAt
    exact hs.mdifferentiableAt (by simp)
  have hB : MDifferentiableAt ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) B (x,s) :=
    hBbase.prodMap mdifferentiableAt_id
  have hval : L z = (x,s) := by
    apply Prod.ext
    · rfl
    · change euclideanSphereCoordChange Q (achart E x) (achart E x) x s = s
      exact euclideanSphereCoordChange_self Q (achart E x) x
        (mem_chart_source E x) s
  have hfunc : fixedRawChart Q x = B ∘ L := rfl
  have hB' : MDifferentiableAt ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) B (L z) := by
    simpa only [hval] using hB
  have hBderiv : mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2)) B (x,s) =
      ContinuousLinearMap.id ℝ (E × TangentSpace (𝓡 2) s) := by
    change mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
      ((𝓘(ℝ,E)).prod (𝓡 2))
      (Prod.map (extChartAt 𝓘(ℝ,E) x) id) (x,s) = _
    rw [mfderiv_prodMap hBbase mdifferentiableAt_id,
      mfderiv_extChartAt_center x, mfderiv_id]
    apply ContinuousLinearMap.ext
    rintro ⟨u,v⟩
    rfl
  rw [hfunc, mfderiv_comp z hB' hL, hval, hBderiv]
  have hLderiv := preferredTriv_mfderiv Q z
  change mfderiv ((𝓘(ℝ,E)).prod (𝓡 2))
    ((𝓘(ℝ,E)).prod (𝓡 2)) L z = _ at hLderiv
  rw [hLderiv]
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
