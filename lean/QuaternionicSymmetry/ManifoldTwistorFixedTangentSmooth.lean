import QuaternionicSymmetry.ManifoldTwistorFixedTrivializationSmooth

/-!
# Smooth tangent map of a fixed twistor trivialization

On the open source of any fixed sphere-bundle trivialization, its actual
manifold tangent map is smooth. The proof applies Mathlib's differentiability
theorem for tangent maps on open domains to the preceding local
diffeomorphism result.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereManifold
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

theorem fixedTriv_smoothOn (p : M) :
    ContMDiffOn (I (E := E)) (I (E := E)) ∞
      (fun z : SphereBundleTotal Q => (sphereCore Q).localTriv (achart E p) z)
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source := by
  intro z hz
  have hz' : z.1 ∈ (sphereCore Q).baseSet (achart E p) := by
    simpa using hz
  exact (fixedTriv_smoothAt Q p z hz').contMDiffWithinAt

theorem fixedTriv_tangent_smoothOn (p : M) :
    ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMap (M := SphereBundleTotal Q) (M' := M × geometricSphere)
        (I (E := E)) (I (E := E))
        (fun z : SphereBundleTotal Q => (sphereCore Q).localTriv (achart E p) z))
      ((fun v : TangentBundle (I (E := E)) (SphereBundleTotal Q) => v.1) ⁻¹'
        ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) := by
  let s : Set (SphereBundleTotal Q) :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source
  have hs : IsOpen s := ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source
  have h : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMapWithin (M := SphereBundleTotal Q) (M' := M × geometricSphere)
        (I (E := E)) (I (E := E))
        (fun z : SphereBundleTotal Q => (sphereCore Q).localTriv (achart E p) z) s)
      ((fun v : TangentBundle (I (E := E)) (SphereBundleTotal Q) => v.1) ⁻¹' s) :=
    (fixedTriv_smoothOn Q p).contMDiffOn_tangentMapWithin (by simp)
      hs.uniqueMDiffOn
  apply h.congr
  intro v hv
  simp only [tangentMapWithin, tangentMap]
  rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hv)]

theorem fixedTriv_tangent_smoothAt (p : M)
    (v : TangentBundle (I (E := E)) (SphereBundleTotal Q))
    (hv : v.1 ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) :
    ContMDiffAt (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMap (M := SphereBundleTotal Q) (M' := M × geometricSphere)
        (I (E := E)) (I (E := E))
        (fun z : SphereBundleTotal Q => (sphereCore Q).localTriv (achart E p) z)) v := by
  have hOpen : IsOpen
      (((fun v : TangentBundle (I (E := E)) (SphereBundleTotal Q) => v.1) ⁻¹'
        ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)) :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.preimage
      (FiberBundle.continuous_proj (E × EuclideanSpace ℝ (Fin 2))
        (TangentSpace (I (E := E)) (M := SphereBundleTotal Q)))
  exact (fixedTriv_tangent_smoothOn Q p).contMDiffAt (hOpen.mem_nhds hv)

theorem fixedTriv_inv_smoothOn (p : M) :
    ContMDiffOn (I (E := E)) (I (E := E)) ∞
      (fun w : M × geometricSphere =>
        (show SphereBundleTotal Q from
          ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.symm w))
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.target := by
  intro w hw
  exact (fixedTriv_inv_smoothAt Q p w hw).contMDiffWithinAt

theorem fixedTriv_inv_tangent_smoothOn (p : M) :
    ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMap (M := M × geometricSphere) (M' := SphereBundleTotal Q)
        (I (E := E)) (I (E := E))
        (fun w : M × geometricSphere =>
          (show SphereBundleTotal Q from
            ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.symm w)))
      ((fun v : TangentBundle (I (E := E)) (M × geometricSphere) => v.1) ⁻¹'
        ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.target) := by
  let s : Set (M × geometricSphere) :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.target
  have hs : IsOpen s :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_target
  have h : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMapWithin (M := M × geometricSphere) (M' := SphereBundleTotal Q)
        (I (E := E)) (I (E := E))
        (fun w : M × geometricSphere =>
          (show SphereBundleTotal Q from
            ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.symm w)) s)
      ((fun v : TangentBundle (I (E := E)) (M × geometricSphere) => v.1) ⁻¹' s) :=
    (fixedTriv_inv_smoothOn Q p).contMDiffOn_tangentMapWithin (by simp)
      hs.uniqueMDiffOn
  apply h.congr
  intro v hv
  simp only [tangentMapWithin, tangentMap]
  rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hv)]

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
