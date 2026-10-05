import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! For a jointly holomorphic family, the derivative in the manifold
variable, evaluated at a fixed tangent vector, varies holomorphically in
the parameter as a map into the actual tangent bundle. -/

namespace QuaternionicSymmetry.HolomorphicParameterTangent

open scoped Manifold ContDiff
noncomputable section

variable {P Z W V : Type*}
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace P] [ChartedSpace W P] [IsManifold 𝓘(ℂ, W) ∞ P]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ, V) ∞ Z]

def parameterTangent (F : P × Z → Z) (z : Z) (v : TangentSpace 𝓘(ℂ, V) z)
    (p : P) : TangentBundle 𝓘(ℂ, V) Z :=
  ⟨F (p, z), mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) (fun y => F (p, y)) z v⟩

theorem partial_mfderiv (F : P × Z → Z)
    (hF : ContMDiff (𝓘(ℂ, W).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) ∞ F)
    (p : P) (z : Z) (v : TangentSpace 𝓘(ℂ, V) z) :
    mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) (fun y => F (p, y)) z v =
      mfderiv (𝓘(ℂ, W).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) F (p, z) (0, v) := by
  have hi : MDifferentiableAt 𝓘(ℂ, V) (𝓘(ℂ, W).prod 𝓘(ℂ, V))
      (fun y : Z => (p, y)) z :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hc := mfderiv_comp z (hF.mdifferentiable (by simp) (p, z)) hi
  change mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) (F ∘ fun y : Z => (p, y)) z v = _
  rw [hc]
  change (mfderiv (𝓘(ℂ, W).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) F (p, z))
    ((mfderiv 𝓘(ℂ, V) (𝓘(ℂ, W).prod 𝓘(ℂ, V)) (fun y : Z => (p, y)) z) v) = _
  apply congrArg
  have hp := mfderiv_prodMk
    (show MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, W) (fun _ : Z => p) z from
      mdifferentiableAt_const)
    (show MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, V) (id : Z → Z) z from
      mdifferentiableAt_id)
  simpa only [mfderiv_const, mfderiv_id, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun T : V →L[ℂ] W × V => T v) hp

theorem parameterTangent_contMDiff (F : P × Z → Z)
    (hF : ContMDiff (𝓘(ℂ, W).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) ∞ F)
    (z : Z) (v : TangentSpace 𝓘(ℂ, V) z) :
    ContMDiff 𝓘(ℂ, W) (𝓘(ℂ, V)).tangent ∞ (parameterTangent F z v) := by
  have hzero : ContMDiff 𝓘(ℂ, W) (𝓘(ℂ, W)).tangent ∞
      (fun p : P => (⟨p, 0⟩ : TangentBundle 𝓘(ℂ, W) P)) :=
    Bundle.contMDiff_zeroSection ℂ _
  have hpair : ContMDiff 𝓘(ℂ, W)
      ((𝓘(ℂ, W)).tangent.prod (𝓘(ℂ, V)).tangent) ∞
      (fun p : P => ((⟨p, 0⟩ : TangentBundle 𝓘(ℂ, W) P),
        (⟨z, v⟩ : TangentBundle 𝓘(ℂ, V) Z))) :=
    hzero.prodMk contMDiff_const
  have hlift : ContMDiff 𝓘(ℂ, W) (𝓘(ℂ, W).prod 𝓘(ℂ, V)).tangent ∞
      (fun p : P => (⟨(p, z), (0, v)⟩ :
        TangentBundle (𝓘(ℂ, W).prod 𝓘(ℂ, V)) (P × Z))) :=
    contMDiff_equivTangentBundleProd_symm.comp hpair
  have htotal := (hF.contMDiff_tangentMap (m := ∞) (by simp)).comp hlift
  apply htotal.congr
  intro p
  symm
  change (⟨F (p, z),
      mfderiv (𝓘(ℂ, W).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) F (p, z) (0, v)⟩ :
      TangentBundle 𝓘(ℂ, V) Z) = parameterTangent F z v p
  unfold parameterTangent
  rw [partial_mfderiv F hF]

end
end QuaternionicSymmetry.HolomorphicParameterTangent
