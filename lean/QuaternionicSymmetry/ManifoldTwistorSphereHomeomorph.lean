import QuaternionicSymmetry.ManifoldTwistorSphereManifold

/-! The smooth associated sphere bundle is homeomorphic to the unit sphere
subbundle of the actual quaternionic rank-three vector bundle. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereManifold
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
private theorem local_eq (i : atlas E M) (p : SphereBundleTotal Q)
 (hi : p.1 ∈ (sphereCore Q).baseSet i) :
 coefficientSphereHomeomorph (localCoordinate Q i (toOriginalSphere Q p) hi) =
   ((sphereCore Q).localTriv i p).2 := by
  let Z := Q.quaternionicRankThreeCore
  have hidx : p.1 ∈ Z.baseSet (Z.indexAt p.1) := Z.mem_baseSet_at _
  have hco : localCoordinate Q i (toOriginalSphere Q p) hi =
      sphereTransition Q (Z.indexAt p.1) i p.1 hidx hi
        (coefficientSphereHomeomorph.symm p.2) := by
    apply Subtype.ext
    change Z.coordChange (Z.indexAt p.1) i p.1
      (Z.coordChange (Z.indexAt p.1) (Z.indexAt p.1) p.1
        (coefficientSphereHomeomorph.symm p.2).1) =
      Z.coordChange (Z.indexAt p.1) i p.1
        (coefficientSphereHomeomorph.symm p.2).1
    rw [Z.coordChange_self _ _ hidx]
  rw [hco, (sphereCore Q).localTriv_apply]
  change coefficientSphereHomeomorph (sphereTransition Q (Z.indexAt p.1) i p.1 hidx hi (coefficientSphereHomeomorph.symm p.2)) = euclideanSphereCoordChange Q (Z.indexAt p.1) i p.1 p.2
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos ⟨hidx, hi⟩]
private theorem continuous_toOriginal_on (i : atlas E M) :
 ContinuousOn (toOriginalSphere Q)
   {p : SphereBundleTotal Q | p.1 ∈ (sphereCore Q).baseSet i} := by
  rw [continuousOn_iff_continuous_restrict]
  let Z := sphereCore Q
  let S : Set (SphereBundleTotal Q) := {p | p.1 ∈ Z.baseSet i}
  have htriv : Continuous (fun p : S => Z.localTriv i p.1) := by
    exact (Z.localTriv i).continuousOn.restrict
  have hbase : Continuous (fun p : S =>
      (⟨p.1.1, p.2⟩ : {x : M // x ∈ Z.baseSet i})) := by
    exact ((FiberBundle.continuous_proj geometricSphere Z.Fiber).comp
      continuous_subtype_val).subtype_mk _
  have hfiber : Continuous (fun p : S =>
      coefficientSphereHomeomorph.symm (Z.localTriv i p.1).2) :=
    coefficientSphereHomeomorph.symm.continuous.comp (continuous_snd.comp htriv)
  have hloc : Continuous (fun p : S =>
      ((localTrivializationHomeomorph Q i).symm
        (⟨p.1.1, p.2⟩,
          coefficientSphereHomeomorph.symm (Z.localTriv i p.1).2)).1) :=
    continuous_subtype_val.comp
      ((localTrivializationHomeomorph Q i).symm.continuous.comp
        (hbase.prodMk hfiber))
  exact hloc.congr (by
    intro p
    change pointOfLocal Q i p.1.1 p.2
      (coefficientSphereHomeomorph.symm (Z.localTriv i p.1).2) =
        toOriginalSphere Q p.1
    rw [← local_eq Q i p.1 p.2]
    simpa using (pointOfLocal_localCoordinate Q i (toOriginalSphere Q p.1) p.2))
private theorem continuous_toOriginal : Continuous (toOriginalSphere Q) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Z := sphereCore Q
  have hopen : IsOpen {q : SphereBundleTotal Q | q.1 ∈ Z.baseSet (Z.indexAt p.1)} :=
    (Z.isOpen_baseSet (Z.indexAt p.1)).preimage Z.continuous_proj
  exact (continuous_toOriginal_on Q (Z.indexAt p.1)).continuousAt
    (hopen.mem_nhds (Z.mem_baseSet_at _))
private theorem continuous_fromOriginal_on (i : atlas E M) :
 ContinuousOn (fromOriginalSphere Q)
   {z : TwistorSphere Q | projection Q z ∈ (sphereCore Q).baseSet i} := by
  rw [continuousOn_iff_continuous_restrict]
  let Z := sphereCore Q
  let T : Set (TwistorSphere Q) :=
    {z | projection Q z ∈ Z.baseSet i}
  have hcoord : Continuous (fun z : T =>
      coefficientSphereHomeomorph
        (localCoordinate Q i z.1 z.2)) := by
    exact coefficientSphereHomeomorph.continuous.comp
      (continuous_snd.comp (localTrivializationHomeomorph Q i).continuous)
  have hbase : Continuous (fun z : T => projection Q z.1) :=
    (projection_continuous Q).comp continuous_subtype_val
  have hpair : Continuous (fun z : T =>
      (projection Q z.1,
       coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2))) :=
    hbase.prodMk hcoord
  have hloc : Continuous (fun z : T =>
      (Z.localTriv i).toOpenPartialHomeomorph.symm
        (projection Q z.1,
         coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2))) :=
    (Z.localTriv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous hpair (by
      intro z
      exact ⟨z.2, Set.mem_univ _⟩)
  exact hloc.congr (by
    intro z
    let p := fromOriginalSphere Q z.1
    have hp : p.1 ∈ Z.baseSet i := z.2
    have heq := local_eq Q i p hp
    have hright : toOriginalSphere Q p = z.1 := (sphereTotalEquiv Q).right_inv z.1
    have hcoord : localCoordinate Q i z.1 z.2 =
        localCoordinate Q i (toOriginalSphere Q p) hp := by
      apply Subtype.ext
      simp only [localCoordinate]
      rw [hright]
    have hc : coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2) =
        (Z.localTriv i p).2 := by rw [hcoord]; exact heq
    have htriv : Z.localTriv i p =
        (projection Q z.1,
         coefficientSphereHomeomorph (localCoordinate Q i z.1 z.2)) := by
      apply Prod.ext
      · rfl
      · exact hc.symm
    change (Z.localTriv i).toOpenPartialHomeomorph.symm _ = p
    rw [← htriv]
    exact (Z.localTriv i).toOpenPartialHomeomorph.left_inv (by simpa using hp))
private theorem continuous_fromOriginal : Continuous (fromOriginalSphere Q) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let Z := sphereCore Q
  have hopen : IsOpen {w : TwistorSphere Q | projection Q w ∈ Z.baseSet (Z.indexAt (projection Q z))} :=
    (Z.isOpen_baseSet (Z.indexAt (projection Q z))).preimage (projection_continuous Q)
  exact (continuous_fromOriginal_on Q (Z.indexAt (projection Q z))).continuousAt
    (hopen.mem_nhds (Z.mem_baseSet_at _))

/-- The smooth associated sphere total space has exactly the topology of the
unit sphere subbundle of the genuine rank-three quaternionic bundle. -/
def sphereTotalHomeomorph : SphereBundleTotal Q ≃ₜ TwistorSphere Q where
  toEquiv := sphereTotalEquiv Q
  continuous_toFun := continuous_toOriginal Q
  continuous_invFun := continuous_fromOriginal Q
end
end QuaternionicSymmetry.ManifoldTwistorSphereManifold
