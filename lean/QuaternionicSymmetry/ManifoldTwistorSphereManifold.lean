import QuaternionicSymmetry.ManifoldTwistorSphereSmoothTransition

/-! Smooth manifold structure on the actual quaternionic twistor sphere
bundle, assembled from the verified smooth rotating overlap maps. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereManifold

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereSmoothTransition
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

private abbrev productModel := (𝓘(ℝ, E)).prod (𝓡 2)

/-- Smooth self transformations of the already smooth base–sphere product. -/
private def smoothProductPregroupoid : Pregroupoid (M × geometricSphere) where
  property f s := ContMDiffOn (productModel (E := E)) (productModel (E := E)) ∞ f s
  comp {f g u v} hf hg _ _ _ := by
    refine hg.comp (hf.mono ?_) ?_
    · intro x hx
      exact hx.1
    · intro x hx
      exact hx.2
  id_mem := contMDiffOn_id
  locality {f u} _ H := contMDiffOn_of_locally_contMDiffOn H
  congr {f g u} _ fg hf := hf.congr (fun x hx => fg x hx)

private theorem sphereBundle_hasSmoothProductGroupoid :
    HasGroupoid (SphereBundleTotal Q) (smoothProductPregroupoid (E := E) (M := M)).groupoid := by
  apply hasGroupoid_of_pregroupoid
  intro e e' he he'
  let Z := sphereCore Q
  change e ∈ (fun t : Trivialization geometricSphere
      (Bundle.TotalSpace.proj (F := geometricSphere) (E := Z.Fiber)) =>
      t.toOpenPartialHomeomorph) '' Set.range Z.localTriv at he
  change e' ∈ (fun t : Trivialization geometricSphere
      (Bundle.TotalSpace.proj (F := geometricSphere) (E := Z.Fiber)) =>
      t.toOpenPartialHomeomorph) '' Set.range Z.localTriv at he'
  rcases he with ⟨_, ⟨i, rfl⟩, rfl⟩
  rcases he' with ⟨_, ⟨j, rfl⟩, rfl⟩
  change ContMDiffOn (productModel (E := E)) (productModel (E := E)) ∞
    (↑((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
      (Z.localTriv j).toOpenPartialHomeomorph))
    ((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
      (Z.localTriv j).toOpenPartialHomeomorph).source
  have hsource :
      ((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
        (Z.localTriv j).toOpenPartialHomeomorph).source =
        ((Z.baseSet i ∩ Z.baseSet j) ×ˢ Set.univ) := by
    ext p
    simp
  rw [hsource]
  apply (sphereCore_trivChange_contMDiffOn Q i j).congr
  intro p hp
  have hi : p.1 ∈ Z.baseSet i := hp.1.1
  have hj : p.1 ∈ Z.baseSet j := hp.1.2
  change ((Z.localTriv j).toOpenPartialHomeomorph
    ((Z.localTriv i).toOpenPartialHomeomorph.symm p)) =
      (p.1, Z.coordChange i j p.1 p.2)
  simp only [Z.localTriv_symm_apply]
  change (p.1, Z.coordChange (Z.indexAt p.1) j p.1
      (Z.coordChange i (Z.indexAt p.1) p.1 p.2)) =
    (p.1, Z.coordChange i j p.1 p.2)
  congr 1
  exact Z.coordChange_comp i (Z.indexAt p.1) j p.1
    ⟨⟨hi, Z.mem_baseSet_at _⟩, hj⟩ p.2

/-- The associated twistor two-sphere bundle is a genuine smooth manifold,
with smooth compatibility inherited from the actual quaternionic frame
rotations and Mathlib's stereographic charts on each sphere fiber. -/
instance sphereBundle_isManifold :
    IsManifold (productModel (E := E)) ∞ (SphereBundleTotal Q) := by
  letI : HasGroupoid (SphereBundleTotal Q)
      (smoothProductPregroupoid (E := E) (M := M)).groupoid :=
    sphereBundle_hasSmoothProductGroupoid Q
  refine { StructureGroupoid.HasGroupoid.comp
    (smoothProductPregroupoid (E := E) (M := M)).groupoid ?_ with }
  intro e he
  rw [mem_groupoid_of_pregroupoid] at he
  rwa [isLocalStructomorphOn_contDiffGroupoid_iff]

/-- In total-space coordinates, the bundle projection is the first chart
coordinate. -/
private theorem projection_chart_expression (z : SphereBundleTotal Q)
    (y : E × EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ (extChartAt (productModel (E := E)) z).target) :
    (extChartAt (𝓘(ℝ, E)) z.1)
        ((extChartAt (productModel (E := E)) z).symm y).1 = y.1 := by
  simp only [extChartAt, chartAt_comp, prodChartedSpace_chartAt,
    mfld_simps] at hy ⊢
  rw [FiberBundle.chartedSpace'_chartAt (F := geometricSphere) z] at hy ⊢
  rw [(trivializationAt geometricSphere (sphereCore Q).Fiber z.1).proj_symm_apply hy.2]
  exact (chartAt E z.1).right_inv (by
    simpa only [mfld_simps, FiberBundle.trivializationAt_proj_fst] using hy.1.1)

/-- The projection of the actual smooth twistor sphere bundle is smooth. -/
theorem sphereProjection_smooth :
    ContMDiff (productModel (E := E)) (𝓘(ℝ, E)) ∞
      (fun z : SphereBundleTotal Q => z.1) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨(FiberBundle.continuous_proj geometricSphere (sphereCore Q).Fiber).continuousAt, ?_⟩
  have hfst : ContDiffWithinAt ℝ ∞ (fun y : E × EuclideanSpace ℝ (Fin 2) => y.1)
      (Set.range (productModel (E := E)))
      ((extChartAt (productModel (E := E)) z) z) :=
    contDiff_fst.contDiffWithinAt
  apply hfst.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin
      (I := productModel (E := E)) z] with y hy
    exact projection_chart_expression Q z y hy
  · exact projection_chart_expression Q z _
      ((extChartAt (productModel (E := E)) z).map_source
        (mem_extChartAt_source z))

end
end QuaternionicSymmetry.ManifoldTwistorSphereManifold
