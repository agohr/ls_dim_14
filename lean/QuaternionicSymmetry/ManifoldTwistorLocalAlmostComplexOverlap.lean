import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
import QuaternionicSymmetry.ManifoldTwistorVerticalCovariance
import QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
import QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
/-! The local almost complex operator commutes with the derivative of the
actual rotating sphere transition. Base directions are raw chart directions;
the adapted quaternionic action is transported through the solder frame. -/
namespace QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
open QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open QuaternionicSymmetry.VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private def basePoint (p : M) (y : E) := (extChartAt 𝓘(ℝ,E) p).symm y

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem basePoint_mem_p (p q : M) (y : E)
 (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
 basePoint p y ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
 simpa only [basePoint, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
   tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
   (extChartAt 𝓘(ℝ,E) p).map_target hy.1

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem basePoint_mem_q (p q : M) (y : E)
 (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
 basePoint p y ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
 simpa only [basePoint, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
   tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy.2

def rotatedCoefficient (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) : coefficientSphere :=
 sphereTransition Q (achart E p) (achart E q) (basePoint p y)
   (basePoint_mem_p Q p q y hy) (basePoint_mem_q Q p q y hy) a

theorem chartBaseComplex_overlap (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) (u : E) :
  fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y
    (chartBaseComplex Q p y a u) =
  chartBaseComplex Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
    (rotatedCoefficient Q p q y hy a)
    (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u) := by
  let x := basePoint p y
  let i := achart E p
  let j := achart E q
  have hi := basePoint_mem_p Q p q y hy
  have hj := basePoint_mem_q Q p q y hy
  have hqy : (extChartAt 𝓘(ℝ,E) q).symm
      (chartTransition (I := 𝓘(ℝ,E)) p q y) = x :=
    (extChartAt 𝓘(ℝ,E) q).left_inv hy.2
  have hsolder (v : E) :
      Q.frames.toFrame j x (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y v) =
        adaptedGauge Q p q y (Q.frames.toFrame i x v) := by
    have h := congrArg (fun L : E →L[ℝ] E => L v)
      (solder_chartTransition Q p q y hy)
    simp only [ContinuousLinearMap.comp_apply] at h
    have hqval : solder Q q (chartTransition (I := 𝓘(ℝ,E)) p q y) =

        Q.frames.toFrame j x := by
      unfold chartTransition
      rw [solder_eq_toFrame Q q _ ((extChartAt 𝓘(ℝ,E) q).map_source hy.2), (extChartAt 𝓘(ℝ,E) q).left_inv hy.2]
      rfl
    have hpval : solder Q p y = Q.frames.toFrame i x :=
      solder_eq_toFrame Q p y hy.1
    rw [hqval, hpval] at h
    exact h
  have hframe (v : E) :
      Q.frames.toFrame i x (chartBaseComplex Q p y a v) =
        baseComplex (Q.reduction.Q i) a (Q.frames.toFrame i x v) := by
    change Q.frames.toFrame i x (Q.frames.fromFrame i x
      (baseComplex (Q.reduction.Q i) a (Q.frames.toFrame i x v))) = _
    rw [Q.frames.to_from i x hi]
  have hframeq (v : E) :
      Q.frames.toFrame j x
        (chartBaseComplex Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
          (rotatedCoefficient Q p q y hy a) v) =
      baseComplex (Q.reduction.Q j) (rotatedCoefficient Q p q y hy a)
        (Q.frames.toFrame j x v) := by
    unfold chartBaseComplex
    unfold chartTransition
    simp only [ContinuousLinearMap.comp_apply]
    rw [(extChartAt 𝓘(ℝ,E) q).left_inv hy.2]
    exact Q.frames.to_from j x hj _
  have heq : Q.frames.toFrame j x
      (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y
        (chartBaseComplex Q p y a u)) =
      Q.frames.toFrame j x
        (chartBaseComplex Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
          (rotatedCoefficient Q p q y hy a)
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u)) := by
    rw [hsolder, hframe, hframeq, hsolder]
    change Q.frames.coordChange i j x
       (synth (Q.reduction.Q i) a.1 (Q.frames.toFrame i x u)) =
      synth (Q.reduction.Q j)
        (Q.reduction.rankThreeCoordChange i j x a.1)
        (Q.frames.coordChange i j x (Q.frames.toFrame i x u))
    exact (synth_rankThreeCoordChange_eval Q i j x hi hj a.1
      (Q.frames.toFrame i x u)).symm
  have h := congrArg (Q.frames.fromFrame j x) heq
  simpa only [Q.frames.from_to j x hj] using h
def splitTransition (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) :
  (E × verticalSubmodule a) →ₗ[ℝ]
    (E × verticalSubmodule (rotatedCoefficient Q p q y hy a)) where
  toFun uv :=
    (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y uv.1,
      verticalTransition Q (achart E p) (achart E q) (basePoint p y)
        (basePoint_mem_p Q p q y hy) (basePoint_mem_q Q p q y hy) a uv.2)
  map_add' u v := by
    apply Prod.ext
    · exact (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y).map_add u.1 v.1
    · exact (verticalTransition Q (achart E p) (achart E q) (basePoint p y)
        (basePoint_mem_p Q p q y hy) (basePoint_mem_q Q p q y hy) a).map_add u.2 v.2
  map_smul' r u := by
    apply Prod.ext
    · exact (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y).map_smul r u.1
    · exact (verticalTransition Q (achart E p) (achart E q) (basePoint p y)
        (basePoint_mem_p Q p q y hy) (basePoint_mem_q Q p q y hy) a).map_smul r u.2

theorem splitTransition_complex (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) (uv : E × verticalSubmodule a) :
  splitTransition Q p q y hy a (chartSplitComplex Q p y a uv) =
  chartSplitComplex Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
    (rotatedCoefficient Q p q y hy a)
    (splitTransition Q p q y hy a uv) := by
  apply Prod.ext
  · exact chartBaseComplex_overlap Q p q y hy a uv.1
  · exact verticalTransition_complex Q (achart E p) (achart E q)
      (basePoint p y) (basePoint_mem_p Q p q y hy)
      (basePoint_mem_q Q p q y hy) a uv.2

variable (D : CompatibleTangentConnection Q)

/-- The tangent transition obtained by applying the two connection splittings
to the base derivative and the verified vertical frame rotation. -/
def localTangentTransition (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) :
  (E × verticalSubmodule a) →ₗ[ℝ]
    (E × verticalSubmodule (rotatedCoefficient Q p q y hy a)) :=
  (connectionSplit Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
    ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
    (rotatedCoefficient Q p q y hy a)).symm.toLinearMap.comp
      ((splitTransition Q p q y hy a).comp
        (connectionSplit Q D p y hy.1 a).toLinearMap)

theorem localTangentTransition_complex (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) (uv : E × verticalSubmodule a) :
  localTangentTransition Q D p q y hy a
    (localTwistorComplex Q D p y hy.1 a uv) =
  localTwistorComplex Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
    ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
    (rotatedCoefficient Q p q y hy a)
    (localTangentTransition Q D p q y hy a uv) := by
  simp only [localTangentTransition, localTwistorComplex,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.apply_symm_apply, splitTransition_complex]
  simp

theorem localTangentTransition_eq_ambient (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) (uv : E × verticalSubmodule a) :
  ((localTangentTransition Q D p q y hy a uv).1,
   (localTangentTransition Q D p q y hy a uv).2.1) =
    ambientTransition Q p q y a.1 (uv.1, uv.2.1) := by
  have hsplit := (connectionSplit Q D q
    (chartTransition (I := 𝓘(ℝ,E)) p q y)
    ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
    (rotatedCoefficient Q p q y hy a)).apply_symm_apply
      (splitTransition Q p q y hy a
        (connectionSplit Q D p y hy.1 a uv))
  have hcov := covariantVertical_overlap Q D p q y a.1 (uv.1, uv.2.1) hy
  apply Prod.ext
  · simp [localTangentTransition, splitTransition, connectionSplit, ambientTransition]
  · change (localTangentTransition Q D p q y hy a uv).2.1 =
      (ambientTransition Q p q y a.1 (uv.1, uv.2.1)).2
    have hfirst : (localTangentTransition Q D p q y hy a uv).1 =
        fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y uv.1 := by
      simp [localTangentTransition, splitTransition, connectionSplit]
    have hrot : (rotatedCoefficient Q p q y hy a).1 =
        rankThreeGauge Q p q y a.1 := rfl
    have hsplit2 : (connectionSplit Q D q
        (chartTransition (I := 𝓘(ℝ,E)) p q y)
        ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
        (rotatedCoefficient Q p q y hy a))
        (localTangentTransition Q D p q y hy a uv) =
      splitTransition Q p q y hy a
        (connectionSplit Q D p y hy.1 a uv) := by
      simpa only [localTangentTransition, LinearMap.comp_apply,
        LinearEquiv.coe_coe] using hsplit
    have hsplit3 := congrArg
      (fun w : E × verticalSubmodule (rotatedCoefficient Q p q y hy a) => w.2.1)
      hsplit2
    have hs : (localTangentTransition Q D p q y hy a uv).2.1 +
        inducedForm Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y uv.1)
          (rankThreeGauge Q p q y a.1) =
        rankThreeGauge Q p q y (uv.2.1 + inducedForm Q D p y uv.1 a.1) := by
      dsimp [connectionSplit, splitTransition, connectionVertical,
        verticalTransition] at hsplit3
      simpa only [hfirst, hrot, map_add] using hsplit3
    dsimp [covariantVertical] at hcov
    rw [← hs] at hcov
    exact (add_right_cancel hcov.symm)

theorem localTangentTransition_eq_fderiv (p q : M) (y : E)
  (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
  (a : coefficientSphere) (uv : E × verticalSubmodule a) :
  ((localTangentTransition Q D p q y hy a uv).1,
   (localTangentTransition Q D p q y hy a uv).2.1) =
    fderiv ℝ (ambientSphereTransition Q p q) (y,a.1)
      (uv.1,uv.2.1) := by
  rw [localTangentTransition_eq_ambient Q D p q y hy a uv,
    ambientSphereTransition_fderiv Q p q y a.1 hy]

end
end QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
