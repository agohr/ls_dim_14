import QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance
import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryAction

/-! Local twistor coordinates of the genuine derivative-induced isometry
action, on an arbitrary overlap of adapted tangent charts. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalAction

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- A point put into chart `i` and read in chart `j` has exactly the
rank-three quaternionic frame-transition coefficient. -/
theorem localCoordinate_pointOfLocal_other
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : coefficientSphere) :
    (localCoordinate Q j (pointOfLocal Q i x hi a)
      (by simpa only [projection_pointOfLocal] using hj)).1 =
      Q.reduction.rankThreeCoordChange i j x a.1 := by
  change Q.quaternionicRankThreeCore.coordChange
      (Q.quaternionicRankThreeCore.indexAt x) j x
      (Q.quaternionicRankThreeCore.coordChange i
        (Q.quaternionicRankThreeCore.indexAt x) x a.1) =
    Q.reduction.rankThreeCoordChange i j x a.1
  exact Q.quaternionicRankThreeCore.coordChange_comp i
    (Q.quaternionicRankThreeCore.indexAt x) j x
      ⟨⟨hi, Q.quaternionicRankThreeCore.mem_baseSet_at x⟩, hj⟩ a.1

/-- In arbitrary adapted source and target charts, the actual lifted
isometry has exactly the fixed-chart coefficient formula. -/
theorem twistorMap_localCoordinate
    (f : QuaternionicIsometries Q) (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : f • x ∈ Q.frames.adaptedCore.baseSet j)
    (a : coefficientSphere) :
    (localCoordinate Q j (twistorMap Q f (pointOfLocal Q i x hi a))
      (by simpa only [projection_twistorMap, projection_pointOfLocal] using hj)).1 =
    Q.reduction.rankThreeCoordChange (achart E (f • x)) j (f • x)
      (coefficientAction Q f x
        (Q.reduction.rankThreeCoordChange i (achart E x) x a.1)) := by
  let k := achart E x
  let l := achart E (f • x)
  let z := pointOfLocal Q i x hi a
  let b := localCoordinate Q k z
    (by simpa only [projection_pointOfLocal] using
      Q.frames.adaptedCore.mem_baseSet_at x)
  have hk := Q.frames.adaptedCore.mem_baseSet_at x
  have hl := Q.frames.adaptedCore.mem_baseSet_at (f • x)
  have hb : b.1 = Q.reduction.rankThreeCoordChange i k x a.1 :=
    localCoordinate_pointOfLocal_other Q i k x hi hk a
  have hz : z = preferredPoint Q x b := by
    simpa only [preferredPoint, projection_pointOfLocal] using
      (pointOfLocal_localCoordinate Q k z
        (by simpa only [projection_pointOfLocal] using hk)).symm
  have htw : twistorMap Q f z =
      preferredPoint Q (f • x) (coefficientSphereAction Q f x b) := by
    rw [hz]
    exact twistorMap_preferredPoint Q f x b
  change Q.quaternionicRankThreeCore.coordChange
      (Q.quaternionicRankThreeCore.indexAt (f • x)) j (f • x)
      (twistorMap Q f z).1.2 = _
  rw [htw]
  have h := localCoordinate_pointOfLocal_other Q l j (f • x) hl hj
    (coefficientSphereAction Q f x b)
  change (localCoordinate Q j
      (pointOfLocal Q l (f • x) hl (coefficientSphereAction Q f x b))
      (by simpa only [projection_pointOfLocal] using hj)).1 =
    Q.reduction.rankThreeCoordChange l j (f • x)
      (coefficientAction Q f x b.1) at h
  rw [hb] at h
  simpa only [preferredPoint, coefficientSphereAction] using h

/-- The actual sphere-bundle trivialization reads exactly the coefficient
of the corresponding point in the original unit-sphere bundle. -/
theorem sphereLocalCoordinate_eq (i : atlas E M)
    (z : SphereBundleTotal Q)
    (hi : z.1 ∈ (sphereCore Q).baseSet i) :
    coefficientSphereHomeomorph
      (localCoordinate Q i (toOriginalSphere Q z) hi) =
    ((sphereCore Q).localTriv i z).2 := by
  let Z := Q.quaternionicRankThreeCore
  have hidx : z.1 ∈ Z.baseSet (Z.indexAt z.1) := Z.mem_baseSet_at _
  have hco : localCoordinate Q i (toOriginalSphere Q z) hi =
      sphereTransition Q (Z.indexAt z.1) i z.1 hidx hi
        (coefficientSphereHomeomorph.symm z.2) := by
    apply Subtype.ext
    change Z.coordChange (Z.indexAt z.1) i z.1
      (Z.coordChange (Z.indexAt z.1) (Z.indexAt z.1) z.1
        (coefficientSphereHomeomorph.symm z.2).1) =
      Z.coordChange (Z.indexAt z.1) i z.1
        (coefficientSphereHomeomorph.symm z.2).1
    rw [Z.coordChange_self _ _ hidx]
  rw [hco, (sphereCore Q).localTriv_apply]
  change coefficientSphereHomeomorph
      (sphereTransition Q (Z.indexAt z.1) i z.1 hidx hi
        (coefficientSphereHomeomorph.symm z.2)) =
    euclideanSphereCoordChange Q (Z.indexAt z.1) i z.1 z.2
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos ⟨hidx, hi⟩]

/-- The smooth local coefficient formula is the actual lift's coordinate
on every fixed-chart overlap, for an arbitrary original twistor point. -/
theorem twistorMap_fixedLocalCoordinate
    (f : QuaternionicIsometries Q) (p : M)
    (z : TwistorSphere Q)
    (hx : projection Q z ∈ (chartAt E p).source)
    (hy : f • projection Q z ∈ (chartAt E (f • p)).source) :
    (localCoordinate Q (achart E (f • p)) (twistorMap Q f z)
      (by simpa only [projection_twistorMap] using hy)).1 =
    ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
      Q f p (projection Q z)
        (localCoordinate Q (achart E p) z hx).1 := by
  let x := projection Q z
  let i := achart E p
  let j := achart E (f • p)
  let a := localCoordinate Q i z hx
  have hz : pointOfLocal Q i x hx a = z :=
    pointOfLocal_localCoordinate Q i z hx
  have hcoord := twistorMap_localCoordinate Q f i j x hx hy a
  change Q.quaternionicRankThreeCore.coordChange
    (Q.quaternionicRankThreeCore.indexAt (f • x)) j (f • x)
    (twistorMap Q f (pointOfLocal Q i x hx a)).1.2 =
      localTrueCoefficientAction Q f p x a.1 at hcoord
  rw [hz] at hcoord
  change Q.quaternionicRankThreeCore.coordChange
    (Q.quaternionicRankThreeCore.indexAt (f • x)) j (f • x)
    (twistorMap Q f z).1.2 =
      ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
        Q f p x a.1
  rw [localCoefficientRotation_eq_true_on_overlap Q f p x hx hy]
  exact hcoord

/-- The three real components of a geometric-sphere bundle chart. -/
def sphereChartCoefficient (i : atlas E M) (z : SphereBundleTotal Q) :
    Fin 3 → ℝ :=
  (coefficientSphereHomeomorph.symm ((sphereCore Q).localTriv i z).2).1

theorem sphereChartCoefficient_eq_localCoordinate
    (i : atlas E M) (z : SphereBundleTotal Q)
    (hi : z.1 ∈ (sphereCore Q).baseSet i) :
    sphereChartCoefficient Q i z =
      (localCoordinate Q i (toOriginalSphere Q z) hi).1 := by
  unfold sphereChartCoefficient
  rw [← sphereLocalCoordinate_eq Q i z hi]
  simp only [coefficientSphereHomeomorph.symm_apply_apply]

theorem toOriginal_sphereTotalMap
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    toOriginalSphere Q (sphereTotalMap Q f z) =
      twistorMap Q f (toOriginalSphere Q z) := by
  change (sphereTotalEquiv Q)
    ((sphereTotalEquiv Q).symm
      (twistorMap Q f ((sphereTotalEquiv Q) z))) = _
  exact (sphereTotalEquiv Q).apply_symm_apply _

/-- A point-level lift of the actual twistor action has the smooth local
coefficient formula in the geometric-sphere bundle chart. -/
theorem sphereChartCoefficient_of_lift
    (f : QuaternionicIsometries Q) (p : M)
    (z w : SphereBundleTotal Q)
    (hx : z.1 ∈ (chartAt E p).source)
    (hy : f • z.1 ∈ (chartAt E (f • p)).source)
    (hw : w.1 ∈ (sphereCore Q).baseSet (achart E (f • p)))
    (hbase : w.1 = f • z.1)
    (horig : toOriginalSphere Q w =
      twistorMap Q f (toOriginalSphere Q z)) :
    sphereChartCoefficient Q (achart E (f • p)) w =
    ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
      Q f p z.1 (sphereChartCoefficient Q (achart E p) z) := by
  rw [sphereChartCoefficient_eq_localCoordinate Q (achart E (f • p))
    w hw,
    sphereChartCoefficient_eq_localCoordinate Q (achart E p) z hx]
  change Q.quaternionicRankThreeCore.coordChange
    (Q.quaternionicRankThreeCore.indexAt w.1)
      (achart E (f • p)) w.1
      (toOriginalSphere Q w).1.2 = _
  rw [hbase, horig]
  exact twistorMap_fixedLocalCoordinate Q f p (toOriginalSphere Q z) hx hy

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalAction
