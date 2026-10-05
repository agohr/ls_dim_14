import QuaternionicSymmetry.CompactSubgroupFixedComponent
import QuaternionicSymmetry.ManifoldLocalDiffeomorphism
import Mathlib.Topology.Connected.Clopen

/-! One-jet uniqueness for a compact smooth action follows from the fixed
component of the subgroup acting trivially on the one-jet at a point. -/
namespace QuaternionicSymmetry.CompactActionOneJet
open Set CompactSubgroupFixedComponent ManifoldLocalDiffeomorphism
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 800000

variable {A E G M : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [PreconnectedSpace M]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G]
  [ChartedSpace A G] [IsManifold 𝓘(ℝ,A) ∞ G] [LieGroup 𝓘(ℝ,A) ∞ G]

lemma eq_id_of_oneJet
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (a : G × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ a)
    (h1 : ∀ x, a (1,x) = x)
    (hmul : ∀ g h x, a (g,a (h,x)) = a (g*h,x))
    (g : G) (x : M) (hg : a (g,x) = x)
    (hdg : ∀ v : E, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => a (g,y)) x v = v) :
    ∀ y, a (g,y) = y := by
  let D (h : G) : E →L[ℝ] E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => a (h,y)) x
  have hs (h : G) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun y => a (h,y)) :=
    ha.comp (contMDiff_const.prodMk contMDiff_id)
  have hD1 : D 1 = ContinuousLinearMap.id ℝ E := by
    have hf : (fun y => a (1,y)) = id := funext h1
    dsimp only [D]
    rw [hf,mfderiv_id]
    rfl
  have hDmul (h k : G) (hk : a (k,x) = x) : D (h*k) = (D h).comp (D k) := by
    have heq : (fun y => a (h*k,y)) = (fun y => a (h,y)) ∘ (fun y => a (k,y)) :=
      funext (fun y => (hmul h k y).symm)
    dsimp only [D]
    rw [heq,mfderiv_comp x ((hs h).mdifferentiableAt (by simp))
      ((hs k).mdifferentiableAt (by simp)),hk]
  let S : Subgroup G := {
    carrier := {h | a (h,x) = x ∧ ∀ v, D h v = v}
    one_mem' := ⟨h1 x,by simp only [hD1,ContinuousLinearMap.id_apply,forall_const]⟩
    mul_mem' := by
      intro h k hh hk
      refine ⟨?_,?_⟩
      · rw [← hmul,hk.1,hh.1]
      · intro v
        rw [hDmul h k hk.1]
        change D h (D k v) = v
        rw [hk.2,hh.2]
    inv_mem' := by
      intro h hh
      have hix : a (h⁻¹,x) = x := by
        calc
          a (h⁻¹,x) = a (h⁻¹,a (h,x)) := by rw [hh.1]
          _ = x := by rw [hmul,inv_mul_cancel,h1]
      refine ⟨hix,?_⟩
      have hc := hDmul h⁻¹ h hh.1
      rw [inv_mul_cancel,hD1] at hc
      intro v
      have hv := congrArg (fun B : E →L[ℝ] E => B v) hc
      change v = D h⁻¹ (D h v) at hv
      simpa only [hh.2] using hv.symm }
  have hxS : x ∈ fixedSet a S := fun h hh => hh.1
  obtain ⟨k,⟨B⟩⟩ := exists_atlas hLee a ha h1 hmul S x hxS
  let C := connectedComponentIn (fixedSet a S) x
  letI := B.charts
  letI := B.manifold
  let i : Component a S x → M := Subtype.val
  let y0 : Component a S x := ⟨x,mem_connectedComponentIn hxS⟩
  have hbi0 : Function.Bijective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y0) := by
    refine ⟨B.inclusion_injective_derivative y0,?_⟩
    intro v
    exact (B.tangent_eq y0 v).mpr (fun h hh => hh.2 v)
  let D0 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E :=
    (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y0).toLinearMap
  have hdim := (LinearEquiv.ofBijective D0 hbi0).finrank_eq
  have hbi (y : Component a S x) : Function.Bijective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y) := by
    let F : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E :=
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,E) i y).toLinearMap
    have hinj : Function.Injective F := B.inclusion_injective_derivative y
    exact ⟨hinj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  have hopen : IsOpen C := by
    have hh := (isOpenMap_of_bijective_mfderiv B.inclusion_smooth hbi).isOpen_range
    simpa [i,C,Component] using hh
  have hclosedS : IsClosed (fixedSet a S) := by
    change IsClosed {y | ∀ h ∈ S, a (h,y) = y}
    simp only [setOf_forall]
    exact isClosed_iInter (fun h => isClosed_iInter (fun _ => isClosed_eq (hs h).continuous continuous_id))
  have hclosed : IsClosed C := by
    rw [show C = Subtype.val '' connectedComponent (⟨x,hxS⟩ : fixedSet a S) from
      connectedComponentIn_eq_image hxS]
    exact hclosedS.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hC : C = univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ ⟨x,mem_connectedComponentIn hxS⟩
  intro y
  have hy : y ∈ C := by rw [hC]; trivial
  exact connectedComponentIn_subset (fixedSet a S) x hy g ⟨hg,hdg⟩

end
end QuaternionicSymmetry.CompactActionOneJet
