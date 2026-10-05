import QuaternionicSymmetry.ManifoldTwistorContactPullbackCoordinatesSmooth

/-! The actual global connection-horizontal lift agrees in every fixed
twistor sphere chart with the explicit smooth local lift built from the
pullback tangent-bundle fiber coordinate. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

private theorem localHorizontalProjection_eq_of_data (p : M)
    (r s : X (E := E)) (hbase : r.1 = s.1) (hsphere : r.2.1 = s.2.1) :
    localHorizontalProjection Q D p r = localHorizontalProjection Q D p s := by
  cases r with
  | mk b t =>
    cases s with
    | mk b' t' =>
      cases hbase
      cases t with
      | mk s v =>
        cases t' with
        | mk s' v' =>
          cases hsphere
          rfl

theorem contactHorizontalLift_fixedChart (p : M)
    (t : Bundle.TotalSpace E (contactPullbackFiber Q))
    (ht : t.1 ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) :
    contactHorizontalLift Q D t =
      localContactBundleLift Q D p (contactPullbackCoordinates Q p t) := by
  let w := contactHorizontalLift Q D t
  let r := rawTangentCoordinates Q p w
  let s := localContactLiftInput (contactPullbackCoordinates Q p t)
  have hpos : (r.1.1,r.2.1) = fixedRawChart Q p t.1 := by
    rfl
  have hdir : r.1.2 = (contactPullbackCoordinates Q p t).2 :=
    (contactPullbackCoordinates_baseDirection Q D p t ht).symm
  have hbase : r.1 = s.1 := by
    apply Prod.ext
    · change r.1.1 = (fixedRawChart Q p t.1).1
      exact congrArg Prod.fst hpos
    · exact hdir
  have hsphere : r.2.1 = s.2.1 := congrArg Prod.snd hpos
  have hP := horizontalProjection_rawChart_conjugacy Q D p t.1 ht w.2
  have hfix : horizontalProjection Q D t.1 w.2 = w.2 :=
    horizontalProjection_fix Q D t.1 w.2 (contactHorizontalLift_mem Q D t)
  rw [hfix] at hP
  have hleft := rawTangentCoordinatesInv_left Q p t.1 ht w.2
  calc
    contactHorizontalLift Q D t = rawTangentCoordinatesInv Q p r := hleft.symm
    _ = rawTangentCoordinatesInv Q p (localHorizontalProjection Q D p r) :=
      congrArg (rawTangentCoordinatesInv Q p) hP
    _ = rawTangentCoordinatesInv Q p (localHorizontalProjection Q D p s) :=
      congrArg (rawTangentCoordinatesInv Q p)
        (localHorizontalProjection_eq_of_data Q D p r s hbase hsphere)
    _ = localContactBundleLift Q D p (contactPullbackCoordinates Q p t) := rfl

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
