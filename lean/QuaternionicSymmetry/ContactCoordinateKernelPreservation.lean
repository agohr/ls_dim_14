import QuaternionicSymmetry.HolomorphicChartDerivative

/-! Actual tangent-kernel preservation passes to fixed contact coordinates. -/
namespace QuaternionicSymmetry.ContactCoordinateKernelPreservation
open HolomorphicLineOneFormCoordinates HolomorphicChartDerivative
open scoped Manifold ContDiff
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)
local notation "T" => tangentBundleCore 𝓘(ℂ,V) M

theorem coordinate_kernel (i : atlas V M) (a : ι) (y v : V)
    (hy : y ∈ i.1.target) (ha : i.1.symm y ∈ L.baseSet a)
    (hv : coordinateForm L θ i a y v = 0) :
    θ (i.1.symm y) ((T).coordChange i (achart V (i.1.symm y)) (i.1.symm y) v) = 0 := by
  have hh := congrArg (L.coordChange a (L.indexAt (i.1.symm y)) (i.1.symm y)) hv
  change L.coordChange a (L.indexAt (i.1.symm y)) (i.1.symm y)
    (L.coordChange (L.indexAt (i.1.symm y)) a (i.1.symm y)
      (θ (i.1.symm y) ((T).coordChange i (achart V (i.1.symm y)) (i.1.symm y) v))) = _ at hh
  rw [L.coordChange_comp,L.coordChange_self,map_zero] at hh
  · exact hh
  · exact L.mem_baseSet_at _
  · exact ⟨⟨L.mem_baseSet_at _,ha⟩,L.mem_baseSet_at _⟩

theorem conjugate_preserves (f : M → M) (hf : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ f)
    (hPres : ∀ x v, θ x v = 0 → θ (f x) (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) f x v) = 0)
    (i : atlas V M) (a : ι) (y v : V) (hy : y ∈ i.1.target)
    (ha : i.1.symm y ∈ L.baseSet a) (ho : f (i.1.symm y) ∈ i.1.source)
    (hv : coordinateForm L θ i a y v = 0) :
    coordinateForm L θ i a (i.1 (f (i.1.symm y)))
      (fderiv ℂ (fun z => i.1 (f (i.1.symm z))) y v) = 0 := by
  have hker := coordinate_kernel L θ i a y v hy ha hv
  have hp := hPres (i.1.symm y) _ hker
  rw [conjugate_derivative f hf i i y hy ho]
  simp only [ContinuousLinearMap.comp_apply]
  unfold coordinateForm localForm
  simp only [ContinuousLinearMap.comp_apply,LinearMap.coe_toContinuousLinearMap,i.1.left_inv ho]
  rw [(T).coordChange_comp (achart V (f (i.1.symm y))) i (achart V (f (i.1.symm y)))
    (f (i.1.symm y)) ⟨⟨mem_chart_source V _,ho⟩,mem_chart_source V _⟩,
    (T).coordChange_self (achart V (f (i.1.symm y))) (f (i.1.symm y)) (mem_chart_source V _)]
  have ht : (θ (i.1.symm (i.1 (f (i.1.symm y)))) : V →ₗ[ℂ] ℂ) = θ (f (i.1.symm y)) := by
    congr 1
    exact i.1.left_inv ho
  change L.coordChange (L.indexAt (f (i.1.symm y))) a (f (i.1.symm y))
    ((θ (i.1.symm (i.1 (f (i.1.symm y)))) : V →ₗ[ℂ] ℂ)
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) f (i.1.symm y)
        ((T).coordChange i (achart V (i.1.symm y)) (i.1.symm y) v))) = 0
  rw [ht]
  exact (congrArg (fun z : ℂ => L.coordChange (L.indexAt (f (i.1.symm y))) a (f (i.1.symm y)) z) hp).trans (map_zero _)

end
end QuaternionicSymmetry.ContactCoordinateKernelPreservation
