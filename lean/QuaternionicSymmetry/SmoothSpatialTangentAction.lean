import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Smoothness of the spatial derivative of an actual smooth family.

The parameter tangent is set to zero in the genuine tangent bundle of a
product. No Lie group, isometry source, or separately assumed smooth
derivative action is needed. -/

namespace QuaternionicSymmetry.SmoothSpatialTangentAction

open Manifold
open scoped Manifold ContDiff

noncomputable section

variable {V E G M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace V G] [IsManifold 𝓘(ℝ, V) ∞ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The derivative in the spatial variable of a jointly smooth family
acts smoothly on the whole tangent bundle, with the actual moving base
point and the actual manifold derivative. -/
theorem contMDiff_spatialTangentAction
    (a : G × M → M)
    (ha : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ a) :
    ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, E).tangent) 𝓘(ℝ, E).tangent ∞
      (fun p : G × TangentBundle 𝓘(ℝ, E) M =>
        (⟨a (p.1, p.2.1),
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x => a (p.1, x)) p.2.1 p.2.2⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
  let F₁ : G × TangentBundle 𝓘(ℝ, E) M →
      TangentBundle 𝓘(ℝ, V) G × TangentBundle 𝓘(ℝ, E) M :=
    fun p => (⟨p.1, 0⟩, p.2)
  have h₁ : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, E).tangent)
      (𝓘(ℝ, V).tangent.prod 𝓘(ℝ, E).tangent) ∞ F₁ := by
    exact ((Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, V)) (n := ∞)
      ℝ (TangentSpace 𝓘(ℝ, V) : G → Type _)).comp contMDiff_fst).prodMk
        contMDiff_snd
  let F₂ := (equivTangentBundleProd 𝓘(ℝ, V) G 𝓘(ℝ, E) M).symm
  have h₂ : ContMDiff (𝓘(ℝ, V).tangent.prod 𝓘(ℝ, E).tangent)
      (𝓘(ℝ, V).prod 𝓘(ℝ, E)).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm (n := ∞)
      (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E))
  have h₃ : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, E)).tangent 𝓘(ℝ, E).tangent ∞
      (tangentMap (𝓘(ℝ, V).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) a) :=
    ha.contMDiff_tangentMap (by simp)
  have h := h₃.comp (h₂.comp h₁)
  convert h using 1
  funext p
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x => a (p.1, x)) p.2.1 p.2.2 =
    mfderiv (𝓘(ℝ, V).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) a (p.1, p.2.1) (0, p.2.2)
  have hc : a ∘ (fun x : M => (p.1, x)) = (fun x => a (p.1, x)) := rfl
  have hright : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, V).prod 𝓘(ℝ, E))
      (fun x : M => (p.1, x)) p.2.1 :=
    ((contMDiff_const.prodMk contMDiff_id :
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, V).prod 𝓘(ℝ, E)) ∞
        (fun x : M => (p.1, x))).mdifferentiableAt (by simp))
  have hcomp := tangentMap_comp_at (I := 𝓘(ℝ, E))
    (I' := 𝓘(ℝ, V).prod 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    (f := fun x : M => (p.1, x)) (g := a) p.2
    (ha.mdifferentiableAt (by simp)) hright
  rw [hc, tangentMap_prod_right] at hcomp
  exact congrArg Bundle.TotalSpace.snd hcomp

end

end QuaternionicSymmetry.SmoothSpatialTangentAction
