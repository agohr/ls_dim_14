import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Complex.Basic

/-! Actual holomorphic vector fields and their derivative-defined
pushforward by biholomorphisms. These are sections of the true tangent
bundle, not functions into a substitute Lie algebra. -/

namespace QuaternionicSymmetry.HolomorphicVectorFieldPushforward

open scoped Manifold ContDiff
noncomputable section

variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace Z] [ChartedSpace V Z] [IsManifold 𝓘(ℂ, V) ∞ Z]

abbrev Fields :=
  ContMDiffSection 𝓘(ℂ, V) V ∞ (TangentSpace 𝓘(ℂ, V) : Z → Type _)

def pushForwardValue (f : Diffeomorph 𝓘(ℂ, V) 𝓘(ℂ, V) Z Z ∞)
    (X : Fields (V := V) (Z := Z)) (z : Z) : TangentSpace 𝓘(ℂ, V) z :=
  mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) f (f.symm z) (X (f.symm z))

theorem pushForwardValue_holomorphic
    (f : Diffeomorph 𝓘(ℂ, V) 𝓘(ℂ, V) Z Z ∞)
    (X : Fields (V := V) (Z := Z)) :
    ContMDiff 𝓘(ℂ, V) (𝓘(ℂ, V)).tangent ∞
      (fun z => (⟨z, pushForwardValue f X z⟩ : TangentBundle 𝓘(ℂ, V) Z)) := by
  have hTM := f.contMDiff.contMDiff_tangentMap (by simp : ∞ + 1 ≤ ∞)
  have h := hTM.comp (X.contMDiff.comp f.symm.contMDiff)
  convert h using 1
  funext z
  apply Bundle.TotalSpace.ext
  · exact (f.apply_symm_apply z).symm
  · rfl

def pushForwardLinear (f : Diffeomorph 𝓘(ℂ, V) 𝓘(ℂ, V) Z Z ∞) :
    Fields (V := V) (Z := Z) →ₗ[ℂ] Fields (V := V) (Z := Z) where
  toFun X := ⟨pushForwardValue f X, pushForwardValue_holomorphic f X⟩
  map_add' X Y := by
    apply ContMDiffSection.ext
    intro z
    exact map_add (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) f (f.symm z)) _ _
  map_smul' c X := by
    apply ContMDiffSection.ext
    intro z
    exact map_smul (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) f (f.symm z)) c _

theorem pushForwardLinear_apply_at_image
    (f : Diffeomorph 𝓘(ℂ, V) 𝓘(ℂ, V) Z Z ∞)
    (X : Fields (V := V) (Z := Z)) (z : Z) :
    pushForwardLinear f X (f z) = mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) f z (X z) := by
  change mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) f (f.symm (f z)) (X (f.symm (f z))) = _
  rw [f.symm_apply_apply]

theorem pushForwardLinear_refl :
    pushForwardLinear (Diffeomorph.refl 𝓘(ℂ, V) Z ∞) =
      LinearMap.id (R := ℂ) (M := Fields (V := V) (Z := Z)) := by
  apply LinearMap.ext
  intro X
  apply ContMDiffSection.ext
  intro z
  have h := pushForwardLinear_apply_at_image
    (Diffeomorph.refl 𝓘(ℂ, V) Z ∞) X z
  simpa using h

theorem pushForwardLinear_trans
    (f g : Diffeomorph 𝓘(ℂ, V) 𝓘(ℂ, V) Z Z ∞) :
    pushForwardLinear (f.trans g) = (pushForwardLinear g).comp (pushForwardLinear f) := by
  apply LinearMap.ext
  intro X
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z, rfl⟩ := (f.trans g).surjective y
  change pushForwardLinear (f.trans g) X ((f.trans g) z) =
    pushForwardLinear g (pushForwardLinear f X) (g (f z))
  rw [pushForwardLinear_apply_at_image, pushForwardLinear_apply_at_image,
    pushForwardLinear_apply_at_image]
  change mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) ((g : Z → Z) ∘ (f : Z → Z)) z (X z) = _
  rw [mfderiv_comp z (g.contMDiff.mdifferentiable (by simp) (f z))
    (f.contMDiff.mdifferentiable (by simp) z)]
  rfl

end
end QuaternionicSymmetry.HolomorphicVectorFieldPushforward
