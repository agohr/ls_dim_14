import QuaternionicSymmetry.HolomorphicLineOneFormCoordinates
import QuaternionicSymmetry.ContactExteriorDerivativeCalculus
import QuaternionicSymmetry.HolomorphicLineGauge

/-! A holomorphic density for the squared contact canonical relation. -/
namespace QuaternionicSymmetry.HolomorphicContactDeterminantDensity
open HolomorphicLineOneFormCoordinates ContactExteriorDerivativeCalculus
  HolomorphicLinePowers HolomorphicLineGauge
open scoped Manifold ContDiff Topology
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)
  (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V) M =>
        (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))

def density (i : atlas V M) (a : ι) (x : M) : ℂ :=
  determinantDensity (Module.finBasis ℂ V) (coordinateForm L θ i a) (i.1 x)

include hθ

theorem density_contMDiffAt (i : atlas V M) (a : ι) (x : M)
    (hi : x ∈ i.1.source) (ha : x ∈ L.baseSet a) :
    ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,ℂ) ∞ (density L θ i a) x := by
  have h := determinantDensity_contDiffAt (Module.finBasis ℂ V)
    (coordinateForm L θ i a) (i.1 x)
    (coordinateForm_contDiffAt L θ hθ i a x hi ha)
  exact h.contMDiffAt.comp x
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas i.2) hi)

theorem density_covariance (i j : atlas V M) (a b : ι) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source)
    (ha : x ∈ L.baseSet a) (hb : x ∈ L.baseSet b) :
    ((tangentBundleCore 𝓘(ℂ,V) M).coordChange i j x).det ^ 2 * density L θ j b x =
      transitionScalar L a b x ^ (Module.finrank ℂ V + 1) * density L θ i a x := by
  let G : V → V := j.1 ∘ i.1.symm
  let g : V → ℂ := fun y => transitionScalar L a b (i.1.symm y)
  have hGx : G (i.1 x) = j.1 x := by simp [G, i.1.left_inv hi]
  have hinv := contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓘(ℂ,V)) (n := ∞) (IsManifold.subset_maximalAtlas i.2) (i.1.map_source hi)
  have hjhol := contMDiffAt_of_mem_maximalAtlas
    (I := 𝓘(ℂ,V)) (n := ∞) (IsManifold.subset_maximalAtlas j.2) hj
  have hG : ContDiffAt ℂ ∞ G (i.1 x) :=
    contMDiffAt_iff_contDiffAt.mp (hjhol.comp_of_eq hinv (i.1.left_inv hi))
  have hline : ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,ℂ) ∞ (transitionScalar L a b) x :=
    (((L.contMDiffOn_coordChange 𝓘(ℂ,V) a b).clm_apply contMDiffOn_const) x
      ⟨ha,hb⟩).contMDiffAt
      (((L.isOpen_baseSet a).inter (L.isOpen_baseSet b)).mem_nhds ⟨ha,hb⟩)
  have hg : ContDiffAt ℂ ∞ g (i.1 x) :=
    contMDiffAt_iff_contDiffAt.mp (hline.comp_of_eq hinv (i.1.left_inv hi))
  have hg0 : g (i.1 x) ≠ 0 := by
    simpa only [g, i.1.left_inv hi] using
      (GaugeIso.refl (IB := 𝓘(ℂ,V)) L).forward_ne_zero a b x ⟨ha,hb⟩
  have hai := (coordinateForm_contDiffAt L θ hθ i a x hi ha).differentiableAt (by simp)
  have hbj : DifferentiableAt ℂ (coordinateForm L θ j b) (G (i.1 x)) := by
    rw [hGx]
    exact (coordinateForm_contDiffAt L θ hθ j b x hj hb).differentiableAt (by simp)
  have h := determinantDensity_covariance (Module.finBasis ℂ V)
    (coordinateForm L θ i a) (coordinateForm L θ j b) G g (i.1 x)
    hai hbj (hG.of_le (by decide)) (hg.differentiableAt (by simp)) hg0
    (coordinateForm_covariance_eventually L θ i j a b x hi hj ha hb)
  rw [tangent_coordChange_eq_fderiv]
  simpa only [hGx, g, i.1.left_inv hi, Fintype.card_fin, density] using h

end
end QuaternionicSymmetry.HolomorphicContactDeterminantDensity
