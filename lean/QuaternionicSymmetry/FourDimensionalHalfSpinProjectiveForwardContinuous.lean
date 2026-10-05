import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleEquiv

/-! Continuity of the literal fiberwise Hopf map between the independently
topologized projective and geometric-sphere associated total spaces, proved
on genuine bundle trivialization neighborhoods. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveForwardContinuous

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

private theorem continuousOn_spinorToSphere (i : atlas ℍ M) :
    ContinuousOn (spinorToSphere Q)
      {p : SpinorBundleTotal Q | p.1 ∈ (projectiveSpinorCore Q).baseSet i} := by
  rw [continuousOn_iff_continuous_restrict]
  let Zp := projectiveSpinorCore Q
  let Zs := sphereCore Q
  let S : Set (SpinorBundleTotal Q) := {p | p.1 ∈ Zp.baseSet i}
  have htriv : Continuous (fun p : S => Zp.localTriv i p.1) :=
    (Zp.localTriv i).continuousOn.restrict
  have hbase : Continuous (fun p : S => p.1.1) :=
    (FiberBundle.continuous_proj
      FourDimensionalHalfSpinProjective.ProjectiveSpinor Zp.Fiber).comp
      continuous_subtype_val
  have hfiber : Continuous (fun p : S =>
      projectiveHopfGeometric (Zp.localTriv i p.1).2) :=
    projectiveHopfGeometricHomeomorph.continuous.comp
      (continuous_snd.comp htriv)
  have hpair : Continuous (fun p : S =>
      (p.1.1, projectiveHopfGeometric (Zp.localTriv i p.1).2)) :=
    hbase.prodMk hfiber
  have hloc : Continuous (fun p : S =>
      (Zs.localTriv i).toOpenPartialHomeomorph.symm
        (p.1.1, projectiveHopfGeometric (Zp.localTriv i p.1).2)) :=
    (Zs.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      hpair (by intro p; exact ⟨p.2, Set.mem_univ _⟩)
  exact hloc.congr (by
    intro p
    have htrivEq : Zs.localTriv i (spinorToSphere Q p.1) =
        (p.1.1, projectiveHopfGeometric (Zp.localTriv i p.1).2) := by
      apply Prod.ext
      · rfl
      · exact localTriv_hopf Q i p.1 p.2
    change (Zs.localTriv i).toOpenPartialHomeomorph.symm _ =
      spinorToSphere Q p.1
    rw [← htrivEq]
    exact (Zs.localTriv i).toOpenPartialHomeomorph.left_inv
      (by change p.1.1 ∈ Zs.baseSet i; exact p.2))

theorem spinorToSphere_continuous : Continuous (spinorToSphere Q) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Zp := projectiveSpinorCore Q
  have hopen : IsOpen
      {q : SpinorBundleTotal Q | q.1 ∈ Zp.baseSet (Zp.indexAt p.1)} :=
    (Zp.isOpen_baseSet (Zp.indexAt p.1)).preimage Zp.continuous_proj
  exact (continuousOn_spinorToSphere Q (Zp.indexAt p.1)).continuousAt
    (hopen.mem_nhds (Zp.mem_baseSet_at _))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveForwardContinuous
