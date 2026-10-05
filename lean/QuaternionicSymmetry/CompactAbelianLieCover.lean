import QuaternionicSymmetry.CompactLieOneParameterSmooth
import QuaternionicSymmetry.SmoothGroupHomSurjectiveDerivative

/-! A compact connected abelian Lie group is smoothly covered by its real
coordinate space. This is the analytic part of the torus classification;
the remaining lattice step is deliberately not assumed here. -/
namespace QuaternionicSymmetry.CompactAbelianLieCover
open Module
open CompactLieOneParameterSubgroup CompactLieOneParameterSmooth
open GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CommGroup G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  {d : ℕ} (b : Basis (Fin d) ℝ (GroupLieAlgebra 𝓘(ℝ,E) G))

def coordinateMap (x : Fin d → ℝ) : G := ∏ i, curve (b i) (x i)

@[simp] theorem coordinateMap_zero : coordinateMap b 0 = 1 := by
  simp [coordinateMap]

theorem coordinateMap_add (x y : Fin d → ℝ) :
    coordinateMap b (x+y) = coordinateMap b x * coordinateMap b y := by
  simp only [coordinateMap, Pi.add_apply, curve_add, Finset.prod_mul_distrib]

theorem coordinateMap_smooth (hClosed : LeeClosedEmbeddingTheorem) :
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) ∞ (coordinateMap b) := by
  apply contMDiff_finset_prod
  intro i _
  exact (curve_smooth hClosed (b i)).comp ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).contMDiff)

def singleCLM (j : Fin d) : ℝ →L[ℝ] (Fin d → ℝ) :=
  ⟨LinearMap.single ℝ (fun _ : Fin d => ℝ) j,
    (LinearMap.single ℝ (fun _ : Fin d => ℝ) j).continuous_of_finiteDimensional⟩

theorem coordinateMap_single (j : Fin d) (t : ℝ) :
    coordinateMap b (singleCLM j t) = curve (b j) t := by
  classical
  unfold coordinateMap
  rw [Finset.prod_eq_single j]
  · simp [singleCLM]
  · intro i _ hij
    simp [singleCLM, Pi.single_eq_of_ne hij]
  · simp

theorem derivative_single (hClosed : LeeClosedEmbeddingTheorem) (j : Fin d) :
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) (coordinateMap b) 0 (Pi.single j 1) = b j := by
  have hsingle : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ) (singleCLM j) 0 = singleCLM j := by
    rw [mfderiv_eq_fderiv]
    exact (singleCLM j).hasFDerivAt.fderiv
  have hcomp := mfderiv_comp (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,Fin d → ℝ))
    (I'' := 𝓘(ℝ,E)) (x := (0 : ℝ))
    ((coordinateMap_smooth b hClosed).mdifferentiableAt (by simp))
    (((singleCLM j).contMDiff (n := ∞)).mdifferentiableAt (by simp))
  have he : coordinateMap b ∘ singleCLM j = curve (b j) :=
    funext (coordinateMap_single b j)
  rw [he, hsingle, map_zero] at hcomp
  have hh := congrArg (fun A : ℝ →L[ℝ] E => A 1) hcomp
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (curve (b j)) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) (coordinateMap b) 0 (Pi.single j 1) at hh
  rw [curve_derivative_zero (G := G) (b j)] at hh
  exact hh.symm

theorem derivative_eq (hClosed : LeeClosedEmbeddingTheorem) :
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) (coordinateMap b) 0).toLinearMap =
      b.equivFun.symm.toLinearMap := by
  apply (Pi.basisFun ℝ (Fin d)).ext
  intro i
  simp only [Pi.basisFun_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe]
  exact (derivative_single b hClosed i).trans (by
    change b i = b.equivFun.symm (Pi.single i 1)
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    ext j
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm])

def coordinateHom : Multiplicative (Fin d → ℝ) →* G where
  toFun x := coordinateMap b (Multiplicative.toAdd x)
  map_one' := coordinateMap_zero b
  map_mul' x y := coordinateMap_add b (Multiplicative.toAdd x) (Multiplicative.toAdd y)

theorem coordinateMap_surjective [PreconnectedSpace G]
    (hClosed : LeeClosedEmbeddingTheorem) : Function.Surjective (coordinateMap b) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  letI : ChartedSpace (Fin d → ℝ) (Multiplicative (Fin d → ℝ)) :=
    inferInstanceAs (ChartedSpace (Fin d → ℝ) (Fin d → ℝ))
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Multiplicative (Fin d → ℝ)) :=
    inferInstanceAs (IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin d → ℝ))
  apply SmoothGroupHomSurjectiveDerivative.surjective_of_surjective_mfderiv_one
    (coordinateHom b) (coordinateMap_smooth b hClosed)
  change Function.Surjective (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) (coordinateMap b) 0)
  change Function.Surjective
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) (coordinateMap b) 0).toLinearMap
  rw [derivative_eq b hClosed]
  exact b.equivFun.symm.surjective

end
end QuaternionicSymmetry.CompactAbelianLieCover
