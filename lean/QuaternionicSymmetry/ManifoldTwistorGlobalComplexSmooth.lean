import QuaternionicSymmetry.ManifoldTwistorRawChartConjugacy

/-! The pointwise twistor complex operator is a smooth bundle endomorphism
of the tangent bundle of the genuine smooth sphere total space. The proof
uses the derivative of every fixed local sphere trivialization, rather than
identifying a preferred tangent model only at the chart center. -/

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

def rawTangentCoordinatesInv (p : M) (r : X (E := E)) :
    TangentBundle (I (E := E)) (SphereBundleTotal Q) :=
  tangentMap (I (E := E)) (I (E := E)) (fixedRawChartInv Q p)
    (productTangentCoordinatesInv r)

theorem fixedRawChartInv_tangent_smoothOn (p : M) :
    ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMap (I (E := E)) (I (E := E)) (fixedRawChartInv Q p))
      ((fun v : TangentBundle (I (E := E)) (E × geometricSphere) => v.1) ⁻¹'
        fixedRawTarget (E := E) p) := by
  let t : Set (E × geometricSphere) := fixedRawTarget (E := E) p
  have ht : IsOpen t := (isOpen_extChartAt_target p).prod isOpen_univ
  have h : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentMapWithin (I (E := E)) (I (E := E)) (fixedRawChartInv Q p) t)
      ((fun v : TangentBundle (I (E := E)) (E × geometricSphere) => v.1) ⁻¹' t) :=
    (fixedRawChartInv_smoothOn Q p).contMDiffOn_tangentMapWithin (by simp)
      ht.uniqueMDiffOn
  apply h.congr
  intro v hv
  simp only [tangentMapWithin, tangentMap]
  rw [mfderivWithin_of_mem_nhds (ht.mem_nhds hv)]

theorem rawTangentCoordinatesInv_smoothOn (p : M) :
    ContMDiffOn (IX (E := E)) (I (E := E)).tangent ∞
      (rawTangentCoordinatesInv Q p) (localDomain (E := E) p) := by
  have hmaps : Set.MapsTo (productTangentCoordinatesInv (E := E))
      (localDomain (E := E) p)
      ((fun v : TangentBundle (I (E := E)) (E × geometricSphere) => v.1) ⁻¹'
        fixedRawTarget (E := E) p) := by
    intro r hr
    exact ⟨hr,Set.mem_univ _⟩
  exact (fixedRawChartInv_tangent_smoothOn Q p).comp
    productTangentCoordinatesInv_smooth.contMDiffOn hmaps

theorem rawTangentCoordinates_smoothOn (p : M) :
    ContMDiffOn (I (E := E)).tangent (IX (E := E)) ∞
      (rawTangentCoordinates Q p)
      ((fun v : TangentBundle (I (E := E)) (SphereBundleTotal Q) => v.1) ⁻¹'
        ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) :=
  productTangentCoordinates_smooth.comp_contMDiffOn
    (fixedRawChart_tangent_smoothOn Q p)

theorem rawTangentCoordinatesInv_left (p : M) (z : SphereBundleTotal Q)
    (hz : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)
    (v : TangentSpace (I (E := E)) z) :
    rawTangentCoordinatesInv Q p (rawTangentCoordinates Q p ⟨z,v⟩) =
      (⟨z,v⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q)) := by
  let f := fixedRawChart Q p
  let g := fixedRawChartInv Q p
  have hF : MDifferentiableAt (I (E := E)) (I (E := E)) f z :=
    ((fixedRawChart_smoothOn Q p).contMDiffAt
      (((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have hTarget : f z ∈ fixedRawTarget (E := E) p := by
    have hx : z.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hz' := ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hz
      rw [← (sphereCore Q).baseSet_at] at hz'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hz'
    exact ⟨(extChartAt 𝓘(ℝ,E) p).map_source hx,Set.mem_univ _⟩
  have hG : MDifferentiableAt (I (E := E)) (I (E := E)) g (f z) := by
    have hopen : IsOpen (fixedRawTarget (E := E) p) :=
      (isOpen_extChartAt_target p).prod isOpen_univ
    exact ((fixedRawChartInv_smoothOn Q p).contMDiffAt
      (hopen.mem_nhds hTarget)).mdifferentiableAt (by simp)
  have hEq : (g ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.mem_nhds hz]
      with w hw
    exact fixedRawChartInv_left Q p w hw
  have hDer := Filter.EventuallyEq.mfderiv_eq (I := I (E := E))
    (I' := I (E := E)) hEq
  rw [mfderiv_comp z hG hF, mfderiv_id] at hDer
  have hPoint := fixedRawChartInv_left Q p z hz
  change tangentMap (I (E := E)) (I (E := E)) g
    (productTangentCoordinatesInv
      (productTangentCoordinates
        (tangentMap (I (E := E)) (I (E := E)) f ⟨z,v⟩))) = _
  rw [productTangentCoordinates_left_inverse]
  apply Bundle.TotalSpace.ext
  · exact hPoint
  · apply heq_of_eq
    change (mfderiv (I (E := E)) (I (E := E)) g (f z))
      ((mfderiv (I (E := E)) (I (E := E)) f z) v) = v
    exact congrArg (fun L : TangentSpace (I (E := E)) z →L[ℝ]
      TangentSpace (I (E := E)) (g (f z)) => L v) hDer

def tangentComplexBundleMap (D : CompatibleTangentConnection Q)
    (t : TangentBundle (I (E := E)) (SphereBundleTotal Q)) :
    TangentBundle (I (E := E)) (SphereBundleTotal Q) :=
  ⟨t.1,tangentComplex Q D t.1 t.2⟩

theorem tangentComplexBundleMap_sq (D : CompatibleTangentConnection Q)
    (t : TangentBundle (I (E := E)) (SphereBundleTotal Q)) :
    tangentComplexBundleMap Q D (tangentComplexBundleMap Q D t) =
      (⟨t.1, -t.2⟩ : TangentBundle (I (E := E)) (SphereBundleTotal Q)) := by
  apply Bundle.TotalSpace.ext
  · rfl
  · apply heq_of_eq
    exact tangentComplex_sq Q D t.1 t.2

theorem tangentComplexBundleMap_smooth (D : CompatibleTangentConnection Q) :
    ContMDiff (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentComplexBundleMap Q D) := by
  intro t
  let p := t.1.1
  let U : Set (TangentBundle (I (E := E)) (SphereBundleTotal Q)) :=
    (fun v => v.1) ⁻¹'
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source
  have ht : t ∈ U :=
    ((sphereCore Q).mem_localTriv_source (achart E p) t.1).mpr
      (by rw [← (sphereCore Q).baseSet_at]; exact (sphereCore Q).mem_baseSet_at p)
  have hOpen : IsOpen U :=
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.preimage
      (FiberBundle.continuous_proj (E × EuclideanSpace ℝ (Fin 2))
        (TangentSpace (I (E := E)) (M := SphereBundleTotal Q)))
  have hC := rawTangentCoordinates_smoothOn Q p
  have hMapC : Set.MapsTo (rawTangentCoordinates Q p) U
      (localDomain (E := E) p) := by
    intro v hv
    have hx : v.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hv' := ((sphereCore Q).mem_localTriv_source (achart E p) v.1).mp hv
      rw [← (sphereCore Q).baseSet_at] at hv'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hv'
    exact (extChartAt 𝓘(ℝ,E) p).map_source hx
  have hJC : ContMDiffOn (I (E := E)).tangent (IX (E := E)) ∞
      (localComplexTrivialized Q D p ∘ rawTangentCoordinates Q p) U :=
    (localComplexTrivialized_smooth Q D p).comp hC hMapC
  have hMapJ : Set.MapsTo
      (localComplexTrivialized Q D p ∘ rawTangentCoordinates Q p)
      U (localDomain (E := E) p) := by
    intro v hv
    exact hMapC hv
  have hFinal : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (rawTangentCoordinatesInv Q p ∘
        (localComplexTrivialized Q D p ∘ rawTangentCoordinates Q p)) U :=
    (rawTangentCoordinatesInv_smoothOn Q p).comp hJC hMapJ
  have hEq : ∀ v ∈ U,
      tangentComplexBundleMap Q D v =
        rawTangentCoordinatesInv Q p
          (localComplexTrivialized Q D p (rawTangentCoordinates Q p v)) := by
    intro v hv
    have hc := tangentComplex_rawChart_conjugacy Q D p v.1 hv v.2
    have hi := rawTangentCoordinatesInv_left Q p v.1 hv
      (tangentComplex Q D v.1 v.2)
    exact hi.symm.trans (congrArg (rawTangentCoordinatesInv Q p) hc)
  have hOn : ContMDiffOn (I (E := E)).tangent (I (E := E)).tangent ∞
      (tangentComplexBundleMap Q D) U :=
    hFinal.congr (fun v hv => by simpa only [Function.comp_apply] using hEq v hv)
  exact hOn.contMDiffAt (hOpen.mem_nhds ht)

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
