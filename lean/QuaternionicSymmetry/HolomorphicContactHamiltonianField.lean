import QuaternionicSymmetry.HolomorphicContactHamiltonianCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-! Actual global holomorphic Hamiltonian vector fields, obtained by
intrinsic gluing of the local bordered Levi solutions. -/
namespace QuaternionicSymmetry.HolomorphicContactHamiltonianField
open HolomorphicContactHamiltonianCoordinates HolomorphicLineOneFormCoordinates
open HolomorphicLineSectionCoordinates ContactHamiltonianLocalSmooth
open ContactDeterminantAlgebra ContactExteriorDerivativeCalculus Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)
  (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
    (fun t : TangentBundle 𝓘(ℂ,V) M => (⟨t.1,θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
  (s : ∀ x, L.Fiber x)
  (hs : ContMDiff 𝓘(ℂ,V) ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
    (fun x => (⟨x,s x⟩ : Bundle.TotalSpace ℂ L.Fiber)))
  (hN : ∀ (i : atlas V M) (a : ι) (x : M), x ∈ i.1.source → x ∈ L.baseSet a →
    (border (coordinateForm L θ i a (i.1 x)).toLinearMap
      (exteriorDerivative (coordinateForm L θ i a) (i.1 x))).Nondegenerate)

def field (x : M) : TangentSpace 𝓘(ℂ,V) x :=
  (coordinateHamiltonian (V := V) L θ s (achart V x) (L.indexAt x) ((chartAt V x) x) : V)

include hθ hs hN

theorem field_eq_local (i : atlas V M) (a : ι) (x : M)
    (hi : x ∈ i.1.source) (ha : x ∈ L.baseSet a) :
    field L θ s x = (tangentBundleCore 𝓘(ℂ,V) M).coordChange i (achart V x) x
      (coordinateHamiltonian L θ s i a (i.1 x)) :=
  coordinateHamiltonian_covariance L θ hθ s hs hN i (achart V x) a (L.indexAt x) x
    hi (mem_chart_source V x) ha (L.mem_baseSet_at x)

theorem field_contMDiff : ContMDiff 𝓘(ℂ,V) (𝓘(ℂ,V)).tangent ∞
    (fun x => (⟨x,field L θ s x⟩ : TangentBundle 𝓘(ℂ,V) M)) := by
  intro x
  let i := achart V x
  let a := L.indexAt x
  let T := tangentBundleCore 𝓘(ℂ,V) M
  letI : IsManifold 𝓘(ℂ,V) (∞ + 1) M := by simpa using (inferInstance : IsManifold 𝓘(ℂ,V) ∞ M)
  letI : T.IsContMDiff 𝓘(ℂ,V) ∞ := tangentBundleCore.isContMDiff
  letI : MemTrivializationAtlas (T.localTriv i) := ⟨⟨i,rfl⟩⟩
  have hi : x ∈ i.1.source := mem_chart_source V x
  have ha : x ∈ L.baseSet a := L.mem_baseSet_at x
  apply ((T.localTriv i).contMDiffAt_section_iff hi).2
  have hy : i.1 x ∈ coordinateDomain L i a := ⟨i.1.map_source hi,by simpa [i.1.left_inv hi] using ha⟩
  have hk := (coordinateHamiltonian_contDiffOn L θ hθ s hs hN i a).contDiffAt
    ((i.1.isOpen_inter_preimage_symm (L.isOpen_baseSet a)).mem_nhds hy)
  have hc : ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (fun y => coordinateHamiltonian L θ s i a (i.1 y)) x :=
    hk.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
      (IsManifold.subset_maximalAtlas i.2) hi)
  apply hc.congr_of_eventuallyEq
  filter_upwards [i.1.open_source.mem_nhds hi,(L.isOpen_baseSet a).mem_nhds ha] with y hyi hya
  change T.coordChange (achart V y) i y (field L θ s y) = _
  rw [field_eq_local L θ hθ s hs hN i a y hyi hya,
    T.coordChange_comp i (achart V y) i y ⟨⟨hyi,mem_chart_source V y⟩,hyi⟩,
    T.coordChange_self i y hyi]

def tangentSection : ContMDiffSection 𝓘(ℂ,V) V ∞ (TangentSpace 𝓘(ℂ,V) : M → Type _) :=
  ⟨field L θ s,field_contMDiff L θ hθ s hs hN⟩

theorem contraction (x : M) : θ x (tangentSection L θ hθ s hs hN x) = s x := by
  let i := achart V x
  let a := L.indexAt x
  have hi : x ∈ i.1.source := mem_chart_source V x
  have ha : x ∈ L.baseSet a := L.mem_baseSet_at x
  have h := localSolution_value (coordinateForm L θ i a) (coordinateSection L s i a) (i.1 x)
    (hN i a x hi ha)
  change coordinateForm L θ i a (i.1 x) (field L θ s x) = coordinateSection L s i a (i.1 x) at h
  simp only [coordinateForm,localForm,coordinateSection,localSection,i.1.left_inv hi,
    ContinuousLinearMap.comp_apply,LinearMap.coe_toContinuousLinearMap] at h
  rw [(tangentBundleCore 𝓘(ℂ,V) M).coordChange_self i x hi,
    L.coordChange_self a x ha] at h
  let θ' : M → V →ₗ[ℂ] ℂ := fun z => θ z
  let s' : M → ℂ := fun z => s z
  change (θ' (i.1.symm (i.1 x))).toContinuousLinearMap (field L θ s x) =
    L.coordChange (L.indexAt x) a x (s' (i.1.symm (i.1 x))) at h
  rw [i.1.left_inv hi] at h
  change θ x (field L θ s x) = L.coordChange a a x (s x) at h
  rw [L.coordChange_self a x ha] at h
  exact h

end
end QuaternionicSymmetry.HolomorphicContactHamiltonianField
