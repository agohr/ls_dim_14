import QuaternionicSymmetry.ManifoldTwistorContactQuotientNaturality

/-! The fixed sphere-bundle tangent coordinates and their inverse are
actual two-sided inverses over each chart target. This is the tangent
chart fact needed for explicit contact-plane bundle local trivializations. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff Topology

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

theorem rawTangentCoordinatesInv_right (p : M) (r : X (E := E))
    (hr : r ∈ localDomain (E := E) p) :
    rawTangentCoordinates Q p (rawTangentCoordinatesInv Q p r) = r := by
  let f := fixedRawChartInv Q p
  let g := fixedRawChart Q p
  let ys : E × geometricSphere := (r.1.1,r.2.1)
  have hys : ys ∈ fixedRawTarget (E := E) p := ⟨hr,Set.mem_univ _⟩
  have hf : MDifferentiableAt (I (E := E)) (I (E := E)) f ys := by
    have ht : IsOpen (fixedRawTarget (E := E) p) :=
      (isOpen_extChartAt_target p).prod isOpen_univ
    exact ((fixedRawChartInv_smoothOn Q p).contMDiffAt
      (ht.mem_nhds hys)).mdifferentiableAt (by simp)
  have hz : f ys ∈
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source := by
    have hx : (extChartAt 𝓘(ℝ,E) p).symm ys.1 ∈
        (extChartAt 𝓘(ℝ,E) p).source :=
      (extChartAt 𝓘(ℝ,E) p).map_target hys.1
    apply ((sphereCore Q).mem_localTriv_source (achart E p) _).mpr
    rw [← (sphereCore Q).baseSet_at]
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hx
  have hg : MDifferentiableAt (I (E := E)) (I (E := E)) g (f ys) :=
    ((fixedRawChart_smoothOn Q p).contMDiffAt
      (((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have hEq : (g ∘ f) =ᶠ[𝓝 ys] id := by
    filter_upwards [((isOpen_extChartAt_target p).prod isOpen_univ).mem_nhds hys]
      with w hw
    exact fixedRawChartInv_right Q p w hw
  have hDer := Filter.EventuallyEq.mfderiv_eq (I := I (E := E))
    (I' := I (E := E)) hEq
  rw [mfderiv_comp ys hg hf, mfderiv_id] at hDer
  have hPoint := fixedRawChartInv_right Q p ys hys
  have ht : tangentMap (I (E := E)) (I (E := E)) g
      (tangentMap (I (E := E)) (I (E := E)) f
        (productTangentCoordinatesInv r)) = productTangentCoordinatesInv r := by
    apply Bundle.TotalSpace.ext
    · exact hPoint
    · apply heq_of_eq
      change (mfderiv (I (E := E)) (I (E := E)) g (f ys))
        ((mfderiv (I (E := E)) (I (E := E)) f ys) (r.1.2,r.2.2)) =
          (r.1.2,r.2.2)
      exact congrArg (fun L : TangentSpace (I (E := E)) ys →L[ℝ]
        TangentSpace (I (E := E)) (g (f ys)) => L (r.1.2,r.2.2)) hDer
  change productTangentCoordinates
    (tangentMap (I (E := E)) (I (E := E)) g
      (tangentMap (I (E := E)) (I (E := E)) f
        (productTangentCoordinatesInv r))) = r
  rw [ht]
  exact productTangentCoordinates_right_inverse r

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
