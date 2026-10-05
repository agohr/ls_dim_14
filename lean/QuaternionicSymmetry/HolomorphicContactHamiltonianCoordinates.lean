import QuaternionicSymmetry.HolomorphicLineSectionCoordinates
import QuaternionicSymmetry.HolomorphicContactDeterminantDensity
import QuaternionicSymmetry.ContactHamiltonianLocalCovariance

/-! Holomorphic Hamiltonian coordinates for a contact line section. The
local vectors transform by the genuine tangent-coordinate derivative. -/
namespace QuaternionicSymmetry.HolomorphicContactHamiltonianCoordinates
open HolomorphicLineOneFormCoordinates HolomorphicLineSectionCoordinates
open HolomorphicLinePowers HolomorphicLineGauge
open ContactDeterminantAlgebra ContactExteriorDerivativeCalculus
open ContactHamiltonianLocalSmooth ContactHamiltonianLocalCovariance
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

def coordinateDomain (i : atlas V M) (a : ι) : Set V := i.1.target ∩ i.1.symm ⁻¹' L.baseSet a

def coordinateHamiltonian (i : atlas V M) (a : ι) (y : V) : V :=
  (localSolution (coordinateForm L θ i a) (coordinateSection L s i a) y).1

variable (hN : ∀ (i : atlas V M) (a : ι) (x : M), x ∈ i.1.source → x ∈ L.baseSet a →
  (border (coordinateForm L θ i a (i.1 x)).toLinearMap
    (exteriorDerivative (coordinateForm L θ i a) (i.1 x))).Nondegenerate)
include hθ hs hN

theorem coordinateHamiltonian_contDiffOn (i : atlas V M) (a : ι) :
    ContDiffOn ℂ ∞ (coordinateHamiltonian L θ s i a) (coordinateDomain L i a) := by
  apply ContDiffOn.fst
  apply localSolution_contDiffOn _ _ _ (i.1.isOpen_inter_preimage_symm (L.isOpen_baseSet a))
  · intro y hy
    have h := coordinateForm_contDiffAt L θ hθ i a (i.1.symm y) (i.1.map_target hy.1) hy.2
    rw [i.1.right_inv hy.1] at h
    exact h.contDiffWithinAt
  · intro y hy
    have h := coordinateSection_contDiffAt L s hs i a (i.1.symm y) (i.1.map_target hy.1) hy.2
    rw [i.1.right_inv hy.1] at h
    exact h.contDiffWithinAt
  · intro y hy
    have h := hN i a (i.1.symm y) (i.1.map_target hy.1) hy.2
    simpa only [i.1.right_inv hy.1] using h

theorem coordinateHamiltonian_covariance (i j : atlas V M) (a b : ι) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (ha : x ∈ L.baseSet a) (hb : x ∈ L.baseSet b) :
    coordinateHamiltonian L θ s j b (j.1 x) =
      (tangentBundleCore 𝓘(ℂ,V) M).coordChange i j x (coordinateHamiltonian L θ s i a (i.1 x)) := by
  let G : V → V := j.1 ∘ i.1.symm
  let g : V → ℂ := fun y => transitionScalar L a b (i.1.symm y)
  have hGx : G (i.1 x) = j.1 x := by simp [G,i.1.left_inv hi]
  have hinv := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
    (IsManifold.subset_maximalAtlas i.2) (i.1.map_source hi)
  have hG : ContDiffAt ℂ ∞ G (i.1 x) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
      (IsManifold.subset_maximalAtlas j.2) hj).comp_of_eq hinv (i.1.left_inv hi))
  have hline : ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,ℂ) ∞ (transitionScalar L a b) x :=
    (((L.contMDiffOn_coordChange 𝓘(ℂ,V) a b).clm_apply contMDiffOn_const) x ⟨ha,hb⟩).contMDiffAt
      (((L.isOpen_baseSet a).inter (L.isOpen_baseSet b)).mem_nhds ⟨ha,hb⟩)
  have hg : ContDiffAt ℂ ∞ g (i.1 x) := contMDiffAt_iff_contDiffAt.mp
    (hline.comp_of_eq hinv (i.1.left_inv hi))
  have hg0 : g (i.1 x) ≠ 0 := by
    simpa only [g,i.1.left_inv hi] using (GaugeIso.refl (IB := 𝓘(ℂ,V)) L).forward_ne_zero a b x ⟨ha,hb⟩
  have hInv : (fderiv ℂ G (i.1 x)).IsInvertible := by
    rw [← tangent_coordChange_eq_fderiv]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (tangentBundleCore 𝓘(ℂ,V) M).coordChange j i x)
    · ext v
      exact ((tangentBundleCore 𝓘(ℂ,V) M).coordChange_comp j i j x ⟨⟨hj,hi⟩,hj⟩ v).trans
        ((tangentBundleCore 𝓘(ℂ,V) M).coordChange_self j x hj v)
    · ext v
      exact ((tangentBundleCore 𝓘(ℂ,V) M).coordChange_comp i j i x ⟨⟨hi,hj⟩,hi⟩ v).trans
        ((tangentBundleCore 𝓘(ℂ,V) M).coordChange_self i x hi v)
  have hjA : DifferentiableAt ℂ (coordinateForm L θ j b) (G (i.1 x)) := by
    rw [hGx]; exact (coordinateForm_contDiffAt L θ hθ j b x hj hb).differentiableAt (by simp)
  have hjS : DifferentiableAt ℂ (coordinateSection L s j b) (G (i.1 x)) := by
    rw [hGx]; exact (coordinateSection_contDiffAt L s hs j b x hj hb).differentiableAt (by simp)
  have hjN : (border (coordinateForm L θ j b (G (i.1 x))).toLinearMap
      (exteriorDerivative (coordinateForm L θ j b) (G (i.1 x)))).Nondegenerate := by
    rw [hGx]; exact hN j b x hj hb
  have h := localSolution_covariance (coordinateForm L θ i a) (coordinateForm L θ j b)
    (coordinateSection L s i a) (coordinateSection L s j b) G g (i.1 x)
    ((coordinateForm_contDiffAt L θ hθ i a x hi ha).differentiableAt (by simp)) hjA
    ((coordinateSection_contDiffAt L s hs i a x hi ha).differentiableAt (by simp)) hjS
    (hG.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)) (hg.differentiableAt (by simp)) hg0
    (coordinateForm_covariance_eventually L θ i j a b x hi hj ha hb)
    (coordinateSection_covariance_eventually L s i j a b x hi hj ha hb)
    (hN i a x hi ha) hjN hInv
  rw [hGx,← tangent_coordChange_eq_fderiv] at h
  exact h

end
end QuaternionicSymmetry.HolomorphicContactHamiltonianCoordinates
