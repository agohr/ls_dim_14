import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereChartOverlap
import QuaternionicSymmetry.ManifoldTwistorSphereSmoothTransition

/-! Smooth overlap certification for the independently constructed native
negative-Hodge sphere atlas. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereSmoothAtlas

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSpherePartialChart
open ManifoldQuaternionicFourNativeSphereCharted
open ManifoldQuaternionicFourNativeSphereChartOverlap
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereSmoothTransition
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace
local instance : TopologicalSpace (NativeSphereBundleTotal Q) := by
  unfold NativeSphereBundleTotal
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (nativeLocalSphereTotal Q i) := by
  unfold nativeLocalSphereTotal
  infer_instance

private abbrev productModel := (𝓘(ℝ,E)).prod (𝓡 2)

private def smoothProductPregroupoid : Pregroupoid (M × geometricSphere) where
  property f s := ContMDiffOn (productModel (E := E)) (productModel (E := E)) ∞ f s
  comp {f g u v} hf hg _ _ _ := by
    refine hg.comp (hf.mono ?_) ?_
    · intro x hx; exact hx.1
    · intro x hx; exact hx.2
  id_mem := contMDiffOn_id
  locality {f u} _ H := contMDiffOn_of_locally_contMDiffOn H
  congr {f g u} _ fg hf := hf.congr (fun x hx => fg x hx)

private theorem nativeOverlap_smooth (i j : atlas E M)
    (pᵢ : nativeLocalSphereTotal Q i) (pⱼ : nativeLocalSphereTotal Q j) :
    ContMDiffOn (productModel (E := E)) (productModel (E := E)) ∞
      (↑((nativeSpherePartialChart Q hdim i pᵢ).symm.trans
        (nativeSpherePartialChart Q hdim j pⱼ)))
      ((nativeSpherePartialChart Q hdim i pᵢ).symm.trans
        (nativeSpherePartialChart Q hdim j pⱼ)).source := by
  let eᵢ := nativeSpherePartialChart Q hdim i pᵢ
  let eⱼ := nativeSpherePartialChart Q hdim j pⱼ
  let f := eᵢ.symm.trans eⱼ
  have hsubset : f.source ⊆
      ((Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ) := by
    intro q hq
    have hqi : q ∈ eᵢ.target := hq.1
    have hpj : eᵢ.symm q ∈ eⱼ.source := hq.2
    have hpi : eᵢ.symm q ∈ eᵢ.source := eᵢ.map_target hqi
    have hi : (eᵢ.symm q).1.1 ∈ Q.frames.adaptedCore.baseSet i := by
      simpa [eᵢ, nativeSpherePartialChart_source, nativeChartSource] using hpi
    have hj : (eᵢ.symm q).1.1 ∈ Q.frames.adaptedCore.baseSet j := by
      simpa [eⱼ, nativeSpherePartialChart_source, nativeChartSource] using hpj
    have hbase : q.1 = (eᵢ.symm q).1.1 := by
      have hright := eᵢ.right_inv hqi
      rw [nativeSpherePartialChart_apply Q hdim i pᵢ (eᵢ.symm q) hi] at hright
      exact (congrArg Prod.fst hright).symm
    exact ⟨⟨hbase ▸ hi,hbase ▸ hj⟩,Set.mem_univ _⟩
  have hsmooth := (sphereCore_trivChange_contMDiffOn Q i j).mono hsubset
  apply hsmooth.congr
  intro q hq
  have hqi : q ∈ eᵢ.target := hq.1
  have hpj : eᵢ.symm q ∈ eⱼ.source := hq.2
  have hpi : eᵢ.symm q ∈ eᵢ.source := eᵢ.map_target hqi
  have hi : (eᵢ.symm q).1.1 ∈ Q.frames.adaptedCore.baseSet i := by
    simpa [eᵢ, nativeSpherePartialChart_source, nativeChartSource] using hpi
  have hj : (eᵢ.symm q).1.1 ∈ Q.frames.adaptedCore.baseSet j := by
    simpa [eⱼ, nativeSpherePartialChart_source, nativeChartSource] using hpj
  have hright := eᵢ.right_inv hqi
  have hcoeff : q.2 = (eᵢ (eᵢ.symm q)).2 := (congrArg Prod.snd hright).symm
  rw [nativeSpherePartialChart_apply Q hdim i pᵢ (eᵢ.symm q) hi] at hright
  have hbase : q.1 = (eᵢ.symm q).1.1 := (congrArg Prod.fst hright).symm
  change eⱼ (eᵢ.symm q) =
    (q.1, (sphereCore Q).coordChange i j q.1 q.2)
  rw [nativeSpherePartialChart_transition Q hdim i j pᵢ pⱼ (eᵢ.symm q) hi hj]
  rw [← hbase, ← hcoeff]
  rfl

private theorem nativeSphere_hasSmoothProductGroupoid :
    @HasGroupoid (M × geometricSphere) _ (NativeSphereBundleTotal Q) _
      (nativeSphereChartedSpace Q hdim)
      (smoothProductPregroupoid (E := E) (M := M)).groupoid := by
  letI := nativeSphereChartedSpace Q hdim
  apply hasGroupoid_of_pregroupoid
  intro e e' he he'
  change e ∈ Set.range (nativeSphereChartAt Q hdim) at he
  change e' ∈ Set.range (nativeSphereChartAt Q hdim) at he'
  rcases he with ⟨p,rfl⟩
  rcases he' with ⟨q,rfl⟩
  exact nativeOverlap_smooth Q hdim
    (Q.frames.adaptedCore.indexAt p.1.1)
    (Q.frames.adaptedCore.indexAt q.1.1)
    ⟨p,Q.frames.adaptedCore.mem_baseSet_at _⟩
    ⟨q,Q.frames.adaptedCore.mem_baseSet_at _⟩

/-- The literal native negative-Hodge sphere subset is a smooth manifold
in its independently constructed native-form chart atlas. -/
theorem nativeSphere_isManifold :
    letI := nativeSphereModelChartedSpace Q hdim
    IsManifold (productModel (E := E)) ∞ (NativeSphereBundleTotal Q) := by
  letI := nativeSphereChartedSpace Q hdim
  letI := nativeSphereModelChartedSpace Q hdim
  letI : HasGroupoid (NativeSphereBundleTotal Q)
      (smoothProductPregroupoid (E := E) (M := M)).groupoid :=
    nativeSphere_hasSmoothProductGroupoid Q hdim
  refine { StructureGroupoid.HasGroupoid.comp
    (smoothProductPregroupoid (E := E) (M := M)).groupoid ?_ with }
  intro e he
  rw [mem_groupoid_of_pregroupoid] at he
  rwa [isLocalStructomorphOn_contDiffGroupoid_iff]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereSmoothAtlas
