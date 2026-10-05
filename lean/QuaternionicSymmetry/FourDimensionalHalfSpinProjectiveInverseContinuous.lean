import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveForwardContinuous

/-! Continuity of the inverse fiberwise Hopf map on the independently
constructed associated total spaces, checked in actual local trivializations. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveInverseContinuous

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinHopfDiffeomorph
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinProjective
  ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem localTriv_inverse_hopf (i : atlas ℍ M) (p : SphereBundleTotal Q)
    (hi : p.1 ∈ (sphereCore Q).baseSet i) :
    (((projectiveSpinorCore Q).localTriv i (sphereToSpinor Q p)).2) =
      projectiveHopfGeometricHomeomorph.symm
        (((sphereCore Q).localTriv i p).2) := by
  apply projectiveHopfGeometricHomeomorph.injective
  rw [projectiveHopfGeometricHomeomorph.apply_symm_apply]
  have h : (sphereToSpinor Q p).1 ∈ (projectiveSpinorCore Q).baseSet i := hi
  have hlocal := localTriv_hopf Q i (sphereToSpinor Q p) h
  have hback : spinorToSphere Q (sphereToSpinor Q p) = p :=
    (spinorSphereEquiv Q).right_inv p
  rw [hback] at hlocal
  exact hlocal.symm

private theorem continuousOn_sphereToSpinor (i : atlas ℍ M) :
    ContinuousOn (sphereToSpinor Q)
      {p : SphereBundleTotal Q | p.1 ∈ (sphereCore Q).baseSet i} := by
  rw [continuousOn_iff_continuous_restrict]
  let Zs := sphereCore Q
  let Zp := projectiveSpinorCore Q
  let S : Set (SphereBundleTotal Q) := {p | p.1 ∈ Zs.baseSet i}
  have htriv : Continuous (fun p : S => Zs.localTriv i p.1) :=
    (Zs.localTriv i).continuousOn.restrict
  have hbase : Continuous (fun p : S => p.1.1) :=
    (FiberBundle.continuous_proj geometricSphere Zs.Fiber).comp
      continuous_subtype_val
  have hfiber : Continuous (fun p : S =>
      projectiveHopfGeometricHomeomorph.symm (Zs.localTriv i p.1).2) :=
    projectiveHopfGeometricHomeomorph.symm.continuous.comp
      (continuous_snd.comp htriv)
  have hpair : Continuous (fun p : S =>
      (p.1.1, projectiveHopfGeometricHomeomorph.symm
        (Zs.localTriv i p.1).2)) :=
    hbase.prodMk hfiber
  have hloc : Continuous (fun p : S =>
      (Zp.localTriv i).toOpenPartialHomeomorph.symm
        (p.1.1, projectiveHopfGeometricHomeomorph.symm
          (Zs.localTriv i p.1).2)) :=
    (Zp.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      hpair (by intro p; exact ⟨p.2, Set.mem_univ _⟩)
  exact hloc.congr (by
    intro p
    have htrivEq : Zp.localTriv i (sphereToSpinor Q p.1) =
        (p.1.1, projectiveHopfGeometricHomeomorph.symm
          (Zs.localTriv i p.1).2) := by
      apply Prod.ext
      · rfl
      · exact localTriv_inverse_hopf Q i p.1 p.2
    change (Zp.localTriv i).toOpenPartialHomeomorph.symm _ =
      sphereToSpinor Q p.1
    rw [← htrivEq]
    exact (Zp.localTriv i).toOpenPartialHomeomorph.left_inv
      (by change p.1.1 ∈ Zp.baseSet i; exact p.2))

theorem sphereToSpinor_continuous : Continuous (sphereToSpinor Q) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Zs := sphereCore Q
  have hopen : IsOpen
      {q : SphereBundleTotal Q | q.1 ∈ Zs.baseSet (Zs.indexAt p.1)} :=
    (Zs.isOpen_baseSet (Zs.indexAt p.1)).preimage Zs.continuous_proj
  exact (continuousOn_sphereToSpinor Q (Zs.indexAt p.1)).continuousAt
    (hopen.mem_nhds (Zs.mem_baseSet_at _))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveInverseContinuous
