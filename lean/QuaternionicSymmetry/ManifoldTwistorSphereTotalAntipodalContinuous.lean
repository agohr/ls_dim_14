import QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalChart

/-! Continuity of the actual twistor sphere total-space antipode, proved in
the independently topologized sphere-bundle trivializations. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalContinuous

open scoped Manifold ContDiff
open ManifoldTwistorSphereBundle ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere
  ManifoldQuaternionicTwistorAntipodalWeight
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldTwistorSphereTotalAntipodalChart

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private theorem sphereAntipodal_continuousOn (i : atlas E M) :
    ContinuousOn (sphereAntipodal Q)
      {z : SphereBundleTotal Q | z.1 ∈ (sphereCore Q).baseSet i} := by
  rw [continuousOn_iff_continuous_restrict]
  let Z := sphereCore Q
  let S : Set (SphereBundleTotal Q) := {z | z.1 ∈ Z.baseSet i}
  have htriv : Continuous (fun z : S => Z.localTriv i z.1) :=
    (Z.localTriv i).continuousOn.restrict
  have hbase : Continuous (fun z : S => z.1.1) :=
    (FiberBundle.continuous_proj geometricSphere Z.Fiber).comp
      continuous_subtype_val
  have hfiber : Continuous (fun z : S =>
      geometricAntipodal (Z.localTriv i z.1).2) :=
    geometricAntipodal_smooth.continuous.comp
      (continuous_snd.comp htriv)
  have hpair : Continuous (fun z : S =>
      (z.1.1, geometricAntipodal (Z.localTriv i z.1).2)) :=
    hbase.prodMk hfiber
  have hloc : Continuous (fun z : S =>
      (Z.localTriv i).toOpenPartialHomeomorph.symm
        (z.1.1, geometricAntipodal (Z.localTriv i z.1).2)) :=
    (Z.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      hpair (by intro z; exact ⟨z.2, Set.mem_univ _⟩)
  exact hloc.congr (by
    intro z
    have htrivEq := sphereAntipodal_localTriv Q i z.1 z.2
    change (Z.localTriv i).toOpenPartialHomeomorph.symm _ = sphereAntipodal Q z.1
    rw [← htrivEq]
    exact (Z.localTriv i).toOpenPartialHomeomorph.left_inv
      (by change z.1.1 ∈ Z.baseSet i; exact z.2))

theorem sphereAntipodal_continuous : Continuous (sphereAntipodal Q) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let Z := sphereCore Q
  have hopen : IsOpen
      {w : SphereBundleTotal Q | w.1 ∈ Z.baseSet (Z.indexAt z.1)} :=
    (Z.isOpen_baseSet (Z.indexAt z.1)).preimage Z.continuous_proj
  exact (sphereAntipodal_continuousOn Q (Z.indexAt z.1)).continuousAt
    (hopen.mem_nhds (Z.mem_baseSet_at _))

end
end QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalContinuous
