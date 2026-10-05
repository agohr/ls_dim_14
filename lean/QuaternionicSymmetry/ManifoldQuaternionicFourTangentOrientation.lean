import QuaternionicSymmetry.ManifoldQuaternionicFourOrientationTransitions

/-! The compatible local quaternionic orientations give a pointwise
orientation of the genuine tangent fibers. The local-coordinate theorem below
is the overlap certificate; no comparison with a spinor convention is made. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourTangentOrientation

open ManifoldQuaternionicMetric
open ManifoldQuaternionicReduction
open ManifoldQuaternionicFourOrientationTransitions
open FourDimensionalQuaternionicPointwiseOrientation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

/-- The actual inverse tangent-frame gauge as a linear equivalence on its
chart domain. The target is definitionally the genuine tangent fiber. -/
def fromFrameEquiv (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    E ≃ₗ[ℝ] TangentSpace 𝓘(ℝ,E) x where
  toFun := Q.frames.fromFrame i x
  invFun := Q.frames.toFrame i x
  map_add' := by intros; simp
  map_smul' := by intros; simp
  left_inv := Q.frames.to_from i x hi
  right_inv := Q.frames.from_to i x hi

/-- The global pointwise tangent orientation, defined using the core's
chosen chart at each point. Chart-independence is certified separately. -/
def tangentQuaternionicOrientation (x : M) :
    Orientation ℝ (TangentSpace 𝓘(ℝ,E) x) (Fin 4) :=
  let i := Q.frames.adaptedCore.indexAt x
  Orientation.map (Fin 4)
    (fromFrameEquiv Q i x (Q.frames.adaptedCore.mem_baseSet_at x))
    (pointwiseQuaternionicOrientation (Q.reduction.Q i) hdim)

/-- The coordinate map from any adapted tangent frame into the actual tangent
fiber, routed through the core's preferred chart at `x`. -/
def localToTangentEquiv (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    E ≃ₗ[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  let k := Q.frames.adaptedCore.indexAt x
  (Q.frameTransition i k x hi (Q.frames.adaptedCore.mem_baseSet_at x)).toLinearEquiv.trans
    (fromFrameEquiv Q k x (Q.frames.adaptedCore.mem_baseSet_at x))

/-- The preceding map is literally the tangent core's chart-coordinate
conversion of the adapted frame vector into the preferred tangent fiber
coordinate at `x`. -/
theorem localToTangentEquiv_apply (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (v : E) :
    localToTangentEquiv Q i x hi v =
      (tangentBundleCore 𝓘(ℝ,E) M).coordChange i
        (Q.frames.adaptedCore.indexAt x) x
        (Q.frames.fromFrame i x v) := by
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  change Q.frames.fromFrame k x (Q.frames.coordChange i k x v) = _
  rw [Q.frames.coordChange_apply, Q.frames.from_to k x hk]

private theorem orientation_map_trans {U V W : Type*}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (e : U ≃ₗ[ℝ] V) (f : V ≃ₗ[ℝ] W)
    (o : Orientation ℝ U (Fin 4)) :
    Orientation.map (Fin 4) f (Orientation.map (Fin 4) e o) =
      Orientation.map (Fin 4) (e.trans f) o := by
  induction o using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply]
    congr 1

/-- Every actual adapted tangent chart gives the same orientation on the
genuine tangent fiber. This is the pointwise gluing law, not a separately
asserted `Continuous` property for the field of orientations. -/
theorem local_orientation_eq_tangent (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    Orientation.map (Fin 4) (localToTangentEquiv Q i x hi)
      (pointwiseQuaternionicOrientation (Q.reduction.Q i) hdim) =
    tangentQuaternionicOrientation Q hdim x := by
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  have h := adaptedTransition_preserves_pointwiseOrientation Q hdim i k x hi hk
  change Orientation.map (Fin 4)
      ((Q.frameTransition i k x hi hk).toLinearEquiv.trans
        (fromFrameEquiv Q k x hk))
      (pointwiseQuaternionicOrientation (Q.reduction.Q i) hdim) =
    Orientation.map (Fin 4) (fromFrameEquiv Q k x hk)
      (pointwiseQuaternionicOrientation (Q.reduction.Q k) hdim)
  rw [← orientation_map_trans, h]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourTangentOrientation
