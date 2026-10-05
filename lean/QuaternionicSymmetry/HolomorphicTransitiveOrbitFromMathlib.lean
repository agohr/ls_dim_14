import QuaternionicSymmetry.ManifoldOpenMapRank
import QuaternionicSymmetry.GeneralHolomorphicTransitiveOrbitSource
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! The literal complex transitive-orbit submersion contract follows from
mathlib's open orbit theorem and the internally proved local rank argument. -/
namespace QuaternionicSymmetry.HolomorphicTransitiveOrbitFromMathlib
open ManifoldOpenMapRank
open scoped Manifold ContDiff Topology
open Function
noncomputable section

private def actionDiffeomorph
    {V G W Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace G] [ChartedSpace V G] [Group G]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [TopologicalSpace Z] [ChartedSpace W Z]
    (a : G × Z → Z) (ha : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,W)) 𝓘(ℂ,W) ∞ a)
    (hOne : ∀ z, a (1,z) = z)
    (hMul : ∀ g h z, a (g*h,z) = a (g,a (h,z))) (g : G) :
    Diffeomorph 𝓘(ℂ,W) 𝓘(ℂ,W) Z Z ∞ where
  toFun z := a (g,z)
  invFun z := a (g⁻¹,z)
  left_inv z := by dsimp; rw [← hMul, inv_mul_cancel, hOne]
  right_inv z := by dsimp; rw [← hMul, mul_inv_cancel, hOne]
  contMDiff_toFun := ha.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := ha.comp (contMDiff_const.prodMk contMDiff_id)

private def leftDiffeomorph
    {V G : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace G] [ChartedSpace V G] [Group G] [LieGroup 𝓘(ℂ,V) ∞ G]
    (g : G) : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) G G ∞ where
  toFun h := g*h
  invFun h := g⁻¹*h
  left_inv h := inv_mul_cancel_left g h
  right_inv h := mul_inv_cancel_left g h
  contMDiff_toFun := contMDiff_const.mul contMDiff_id
  contMDiff_invFun := contMDiff_const.mul contMDiff_id

/-- The original BG-L7 contract, with every topological and smoothness
hypothesis retained and no new literature input. -/
theorem holomorphicTransitiveOrbitSubmersion :
    GeneralHolomorphicTransitiveOrbitSource.LeeHolomorphicTransitiveOrbitSubmersion := by
  intro V G W Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a ha hOne hMul hTrans z
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ,V) ∞
  letI : MulAction G Z := {
    smul := fun g z => a (g,z)
    one_smul := hOne
    mul_smul := hMul }
  letI : ContinuousSMul G Z := ⟨ha.continuous⟩
  letI : MulAction.IsPretransitive G Z := ⟨hTrans⟩
  letI : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace V G
  letI : LocallyCompactSpace Z := ChartedSpace.locallyCompactSpace W Z
  let f : G → Z := fun g => a (g,z)
  have hf : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,W) ∞ f :=
    ha.comp (contMDiff_id.prodMk contMDiff_const)
  have hopen : IsOpenMap f := isOpenMap_smul_of_sigmaCompact z
  obtain ⟨g, hg⟩ := exists_surjective_mfderiv (1 : G) hf hopen
  let A := leftDiffeomorph (V := V) g
  let B := actionDiffeomorph a ha hOne hMul g
  have heq : f ∘ A = B ∘ f := funext (fun h => hMul g h z)
  have hchain :
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) f (A 1)).comp
        (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) A 1) =
      (mfderiv 𝓘(ℂ,W) 𝓘(ℂ,W) B (f 1)).comp
        (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) f 1) := by
    calc
      _ = mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) (f ∘ A) 1 :=
        (mfderiv_comp 1 (hf.mdifferentiableAt (by simp))
          (A.contMDiff.mdifferentiableAt (by simp))).symm
      _ = mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) (B ∘ f) 1 := by rw [heq]
      _ = _ := mfderiv_comp 1 (B.contMDiff.mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp))
  have hA : Surjective (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) A 1) :=
    (A.mfderivToContinuousLinearEquiv (by simp) 1).surjective
  have hB : Injective (mfderiv 𝓘(ℂ,W) 𝓘(ℂ,W) B (f 1)) :=
    (B.mfderivToContinuousLinearEquiv (by simp) (f 1)).injective
  have hg' : Surjective (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) f (A 1)) := by
    change Surjective (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) f (g*1))
    rwa [mul_one]
  have hcomp : Surjective ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,W) f (A 1)).comp
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) A 1)) := hg'.comp hA
  rw [hchain] at hcomp
  intro v
  obtain ⟨w, hw⟩ := hcomp (mfderiv 𝓘(ℂ,W) 𝓘(ℂ,W) B (f 1) v)
  exact ⟨w, hB hw⟩

end
end QuaternionicSymmetry.HolomorphicTransitiveOrbitFromMathlib
