import QuaternionicSymmetry.ManifoldTwistorLocalComplexBundleSmooth

/-!
# Smoothness of each fixed twistor sphere trivialization

The associated sphere-bundle chart is a smooth local diffeomorphism between
the actual total space and the base–sphere product.  Both directions are
deduced from the verified smooth total-space atlas, using a chart of the
base–sphere product to exhibit the trivialization as a maximal-atlas member.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereManifold
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open StructureGroupoid IsManifold
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev H := ModelProd E (EuclideanSpace ℝ (Fin 2))

local instance : ChartedSpace (H (E := E)) (SphereBundleTotal Q) := by
  letI : ChartedSpace (H (E := E)) (M × geometricSphere) := inferInstance
  exact ChartedSpace.comp _ (M × geometricSphere) _

theorem fixedTriv_smoothAt (p : M) (z : SphereBundleTotal Q)
    (hz : z.1 ∈ (sphereCore Q).baseSet (achart E p)) :
    ContMDiffAt (I (E := E)) (I (E := E)) ∞
      (fun z : SphereBundleTotal Q => (sphereCore Q).localTriv (achart E p) z) z := by
  let L := (sphereCore Q).localTriv (achart E p)
  let w := L z
  let c := chartAt (H (E := E)) w
  let e : OpenPartialHomeomorph (SphereBundleTotal Q) (H (E := E)) :=
    L.toOpenPartialHomeomorph.trans c
  have heA : e ∈ atlas (H (E := E)) (SphereBundleTotal Q) := by
    change e ∈ Set.image2 OpenPartialHomeomorph.trans
      (atlas (M × geometricSphere) (SphereBundleTotal Q))
      (atlas (H (E := E)) (M × geometricSphere))
    exact ⟨L.toOpenPartialHomeomorph,
      ⟨L, ⟨achart E p,rfl⟩, rfl⟩,
      c, chart_mem_atlas _ w, rfl⟩
  have he : e ∈ maximalAtlas (I (E := E)) ∞ (SphereBundleTotal Q) :=
    (contDiffGroupoid ∞ (I (E := E))).subset_maximalAtlas heA
  have hzE : z ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa [L] using hz,
      show L z ∈ c.source from mem_chart_source _ w⟩
  have hs : ContMDiffAt (I (E := E)) (I (E := E)) ∞ e z :=
    contMDiffAt_of_mem_maximalAtlas (M := SphereBundleTotal Q) he hzE
  have hc : ContMDiffAt (I (E := E)) (I (E := E)) ∞ c.symm (e z) :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas w)
      (c.map_source hzE.2)
  have hcomp := hc.comp z hs
  have heq : (fun x : SphereBundleTotal Q => c.symm (e x)) =ᶠ[𝓝 z]
      (fun x => L x) := by
    filter_upwards [e.open_source.mem_nhds hzE] with x hx
    have hx' : L x ∈ c.source := hx.2
    change c.symm (c (L x)) = L x
    exact c.left_inv hx'
  exact hcomp.congr_of_eventuallyEq heq.symm

theorem fixedTriv_inv_smoothAt (p : M) (w : M × geometricSphere)
    (hw : w ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.target) :
    ContMDiffAt (I (E := E)) (I (E := E)) ∞
      (fun w : M × geometricSphere =>
        (show SphereBundleTotal Q from
          ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.symm w)) w := by
  let L := (sphereCore Q).localTriv (achart E p)
  let c := chartAt (H (E := E)) w
  let e : OpenPartialHomeomorph (SphereBundleTotal Q) (H (E := E)) :=
    L.toOpenPartialHomeomorph.trans c
  have heA : e ∈ atlas (H (E := E)) (SphereBundleTotal Q) := by
    change e ∈ Set.image2 OpenPartialHomeomorph.trans
      (atlas (M × geometricSphere) (SphereBundleTotal Q))
      (atlas (H (E := E)) (M × geometricSphere))
    exact ⟨L.toOpenPartialHomeomorph,
      ⟨L, ⟨achart E p,rfl⟩, rfl⟩,
      c, chart_mem_atlas _ w, rfl⟩
  have he : e ∈ maximalAtlas (I (E := E)) ∞ (SphereBundleTotal Q) :=
    (contDiffGroupoid ∞ (I (E := E))).subset_maximalAtlas heA
  have hzE : L.toOpenPartialHomeomorph.symm w ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source]
    exact ⟨L.toOpenPartialHomeomorph.map_target hw,
      by
        change L.toOpenPartialHomeomorph
          (L.toOpenPartialHomeomorph.symm w) ∈ c.source
        rw [L.toOpenPartialHomeomorph.right_inv hw]
        exact mem_chart_source _ w⟩
  have hc : ContMDiffAt (I (E := E)) (I (E := E)) ∞ c w :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas w) (mem_chart_source _ w)
  have hesymm : ContMDiffAt (I (E := E)) (I (E := E)) ∞ e.symm (c w) := by
    apply contMDiffAt_symm_of_mem_maximalAtlas he
    convert e.map_source hzE using 1
    change c w = c (L.toOpenPartialHomeomorph
      (L.toOpenPartialHomeomorph.symm w))
    rw [L.toOpenPartialHomeomorph.right_inv hw]
  have hcomp := hesymm.comp w hc
  have heq : (fun x : M × geometricSphere => e.symm (c x)) =ᶠ[𝓝 w]
      (fun x => L.toOpenPartialHomeomorph.symm x) := by
    filter_upwards [L.toOpenPartialHomeomorph.open_target.mem_nhds hw,
      c.open_source.mem_nhds (mem_chart_source _ w)] with x hxL hxc
    change L.toOpenPartialHomeomorph.symm (c.symm (c x)) =
      L.toOpenPartialHomeomorph.symm x
    rw [c.left_inv hxc]
  exact hcomp.congr_of_eventuallyEq heq.symm
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
