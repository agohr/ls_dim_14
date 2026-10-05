import QuaternionicSymmetry.HolomorphicChartDerivative
import QuaternionicSymmetry.HolomorphicFamilyInfinitesimalLinear

/-! Joint holomorphic families and both partial derivatives in fixed charts. -/
namespace QuaternionicSymmetry.HolomorphicFamilyCoordinateDerivatives
open HolomorphicChartDerivative
open scoped Manifold ContDiff
noncomputable section
variable {E V G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace G] [ChartedSpace E G] [IsManifold 𝓘(ℂ,E) ∞ G]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℂ,V) ∞ M]
  (A : G × M → M)
  (hA : ContMDiff (𝓘(ℂ,E).prod 𝓘(ℂ,V)) 𝓘(ℂ,V) ∞ A)
  (j : atlas E G) (i : atlas V M)

def family (z : E × V) : V := i.1 (A (j.1.symm z.1,i.1.symm z.2))

include hA
theorem family_contDiffAt (q : E) (y : V) (hq : q ∈ j.1.target) (hy : y ∈ i.1.target)
    (ho : A (j.1.symm q,i.1.symm y) ∈ i.1.source) :
    ContDiffAt ℂ ∞ (family A j i) (q,y) := by
  have hj := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,E)) (n := ∞)
    (IsManifold.subset_maximalAtlas j.2) hq
  have hi := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
    (IsManifold.subset_maximalAtlas i.2) hy
  have hc := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
    (IsManifold.subset_maximalAtlas i.2) ho
  have hin : ContMDiffAt (𝓘(ℂ,E).prod 𝓘(ℂ,V)) (𝓘(ℂ,E).prod 𝓘(ℂ,V)) ∞
      (fun z : E × V => (j.1.symm z.1,i.1.symm z.2)) (q,y) :=
    (hj.comp (q,y) contMDiffAt_fst).prodMk (hi.comp (q,y) contMDiffAt_snd)
  have hh := hc.comp (q,y) (hA.contMDiffAt.comp (q,y) hin)
  rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hh
  exact contMDiffAt_iff_contDiffAt.mp hh

theorem parameter_derivative (q : E) (y : V) (u : E)
    (hq : q ∈ j.1.target) (hy : y ∈ i.1.target)
    (ho : A (j.1.symm q,i.1.symm y) ∈ i.1.source) :
    fderiv ℂ (family A j i) (q,y) (u,0) =
      (tangentBundleCore 𝓘(ℂ,V) M).coordChange
        (achart V (A (j.1.symm q,i.1.symm y))) i (A (j.1.symm q,i.1.symm y))
        (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,V) (fun g => A (g,i.1.symm y)) (j.1.symm q)
          ((tangentBundleCore 𝓘(ℂ,E) G).coordChange j (achart E (j.1.symm q)) (j.1.symm q) u)) := by
  have hf := (family_contDiffAt A hA j i q y hq hy ho).differentiableAt (by simp)
  have hin : HasFDerivAt (fun z : E => (z,y)) (ContinuousLinearMap.inl ℂ E V) q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const y q)
  have hp := (hf.hasFDerivAt.comp q hin).fderiv
  have he := conjugate_derivative (fun g => A (g,i.1.symm y))
    (hA.comp (contMDiff_id.prodMk contMDiff_const)) j i q hq ho
  change fderiv ℂ (fun z => i.1 (A (j.1.symm z,i.1.symm y))) q = _ at hp
  rw [he] at hp
  exact (congrArg (fun B : E →L[ℂ] V => B u) hp).symm

theorem spatial_derivative (q : E) (y v : V)
    (hq : q ∈ j.1.target) (hy : y ∈ i.1.target)
    (ho : A (j.1.symm q,i.1.symm y) ∈ i.1.source) :
    fderiv ℂ (family A j i) (q,y) (0,v) =
      (tangentBundleCore 𝓘(ℂ,V) M).coordChange
        (achart V (A (j.1.symm q,i.1.symm y))) i (A (j.1.symm q,i.1.symm y))
        (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) (fun x => A (j.1.symm q,x)) (i.1.symm y)
          ((tangentBundleCore 𝓘(ℂ,V) M).coordChange i (achart V (i.1.symm y)) (i.1.symm y) v)) := by
  have hf := (family_contDiffAt A hA j i q y hq hy ho).differentiableAt (by simp)
  have hin : HasFDerivAt (fun z : V => (q,z)) (ContinuousLinearMap.inr ℂ E V) y :=
    (hasFDerivAt_const q y).prodMk (hasFDerivAt_id y)
  have hp := (hf.hasFDerivAt.comp y hin).fderiv
  have he := conjugate_derivative (fun x => A (j.1.symm q,x))
    (hA.comp (contMDiff_const.prodMk contMDiff_id)) i i y hy ho
  change fderiv ℂ (fun z => i.1 (A (j.1.symm q,i.1.symm z))) y = _ at hp
  rw [he] at hp
  exact (congrArg (fun B : V →L[ℂ] V => B v) hp).symm

end
end QuaternionicSymmetry.HolomorphicFamilyCoordinateDerivatives
