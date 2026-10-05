import QuaternionicSymmetry.HolomorphicFamilyCoordinateDerivatives
import QuaternionicSymmetry.ContactCoordinateKernelPreservation
import QuaternionicSymmetry.ContactFamilyInfinitesimal
import QuaternionicSymmetry.HolomorphicContactHamiltonianBijection

/-! A holomorphic family preserving a contact kernel has contact infinitesimal fields. -/
namespace QuaternionicSymmetry.HolomorphicKernelFamilyContact
open HolomorphicFamilyCoordinateDerivatives HolomorphicFamilyInfinitesimalLinear
open HolomorphicLineOneFormCoordinates HolomorphicTangentSectionCoordinates
open HolomorphicContactHamiltonianBijection Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E V G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace G] [ChartedSpace E G] [IsManifold 𝓘(ℂ,E) ∞ G]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)
  (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
    (fun t : TangentBundle 𝓘(ℂ,V) M => (⟨t.1,θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
  (A : G × M → M) (g₀ : G)
  (hA : ContMDiff (𝓘(ℂ,E).prod 𝓘(ℂ,V)) 𝓘(ℂ,V) ∞ A)
  (hId : ∀ x, A (g₀,x) = x)
  (hPres : ∀ g x v, θ x v = 0 → θ (A (g,x))
    (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) (fun z => A (g,z)) x v) = 0)
include hθ hPres

theorem infinitesimal_isContact (u : E) :
    IsContact L θ (infinitesimalActionLinear A g₀ hA hId u) := by
  intro i a x hx ha Y hY hYker
  let j := achart E g₀
  let p := j.1 g₀
  let y := i.1 x
  let F := family A j i
  let X := infinitesimalActionLinear A g₀ hA hId u
  have hj : p ∈ j.1.target := j.1.map_source (mem_chart_source E g₀)
  have hj0 : j.1.symm p = g₀ := j.1.left_inv (mem_chart_source E g₀)
  have hy : y ∈ i.1.target := i.1.map_source hx
  have hi0 : i.1.symm y = x := i.1.left_inv hx
  have hbase (z : V) (hz : z ∈ i.1.target) : A (j.1.symm p,i.1.symm z) ∈ i.1.source := by
    rw [hj0,hId]
    exact i.1.map_target hz
  have hF : ContDiffAt ℂ ∞ F (p,y) := family_contDiffAt A hA j i p y hj hy (hbase y hy)
  have hEq : (fun z => fderiv ℂ F (p,z) (u,0)) =ᶠ[𝓝 y] coordinateField X i := by
    filter_upwards [i.1.open_target.mem_nhds hy] with z hz
    have hh := parameter_derivative A hA j i p z u hj hz (hbase z hz)
    rw [hj0,hId] at hh
    have hself := (tangentBundleCore 𝓘(ℂ,E) G).coordChange_self j g₀ (mem_chart_source E g₀) u
    simpa only [j,hself,coordinateField,X,infinitesimalActionLinear_apply] using hh
  have hIdF : (fun z => F (p,z)) =ᶠ[𝓝 y] id := by
    filter_upwards [i.1.open_target.mem_nhds hy] with z hz
    simp only [F,family,hj0,hId,i.1.right_inv hz,id_eq]
  have hFx : F (p,y) = y := hIdF.self_of_nhds
  have hDx : fderiv ℂ F (p,y) (0,Y y) = Y y := by
    have hin : HasFDerivAt (fun z : V => (p,z)) (ContinuousLinearMap.inr ℂ E V) y :=
      (hasFDerivAt_const p y).prodMk (hasFDerivAt_id y)
    have hh := ((hF.differentiableAt (by simp)).hasFDerivAt.comp y hin).fderiv
    change fderiv ℂ (fun z => F (p,z)) y = _ at hh
    rw [hIdF.fderiv_eq,fderiv_id] at hh
    exact (congrArg (fun B : V →L[ℂ] V => B (Y y)) hh).symm
  have hPresF : (fun q => coordinateForm L θ i a (F (q,y))
      (fderiv ℂ F (q,y) (0,Y y))) =ᶠ[𝓝 p] fun _ => 0 := by
    have hcont : ContinuousAt (fun q => A (j.1.symm q,i.1.symm y)) p :=
      (hA.comp (contMDiff_id.prodMk contMDiff_const)).continuous.continuousAt.comp
        (j.1.symm.continuousAt hj)
    have hout : ∀ᶠ q in 𝓝 p, A (j.1.symm q,i.1.symm y) ∈ i.1.source :=
      hcont.eventually (i.1.open_source.mem_nhds (hbase y hy))
    filter_upwards [j.1.open_target.mem_nhds hj,hout] with q hq ho
    have hf : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (fun z => A (j.1.symm q,z)) :=
      hA.comp (contMDiff_const.prodMk contMDiff_id)
    have hp := ContactCoordinateKernelPreservation.conjugate_preserves L θ
      (fun z => A (j.1.symm q,z)) hf (hPres (j.1.symm q)) i a y (Y y) hy
      (by simpa only [hi0] using ha) ho hYker.self_of_nhds
    have hs := spatial_derivative A hA j i q y (Y y) hq hy ho
    have hc := HolomorphicChartDerivative.conjugate_derivative (fun z => A (j.1.symm q,z)) hf i i y hy ho
    have hd : fderiv ℂ F (q,y) (0,Y y) =
        fderiv ℂ (fun z => i.1 (A (j.1.symm q,i.1.symm z))) y (Y y) := by
      rw [hc]
      exact hs
    rw [hd]
    exact hp
  have hh := ContactFamilyInfinitesimal.lieBracket_horizontal F (coordinateForm L θ i a) p u y Y
    (hF.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast))
    ((coordinateForm_contDiffAt L θ hθ i a x hx ha).differentiableAt (by simp))
    hY hFx hDx hYker hPresF
  change coordinateForm L θ i a y (VectorField.lieBracket ℂ (coordinateField X i) Y y) = 0
  simpa only [VectorField.lieBracket,hEq.self_of_nhds,hEq.fderiv_eq] using hh

end
end QuaternionicSymmetry.HolomorphicKernelFamilyContact
