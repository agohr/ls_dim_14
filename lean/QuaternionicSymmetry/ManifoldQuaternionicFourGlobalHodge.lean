import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeOverlapExterior
import QuaternionicSymmetry.ManifoldQuaternionicFourTangentOrientation

/-! The actual tangent bundle receives a globally defined pointwise Hodge
operator. It is constructed in the core's preferred frame and checked in
every adapted chart by the proved exterior overlap law. Smooth dependence on
the base point and the source's spinor naming are separate questions. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourGlobalHodge

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorCanonicalHodge
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

/-- Genuine exterior pullback is linear in the form. -/
def pullbackTwoFormLinear (b : Basis (Fin 4) ℝ E)
    (T : E →ₗ[ℝ] E) : TwoForm E →ₗ[ℝ] TwoForm E where
  toFun := pullbackTwoForm b T
  map_add' α β := by
    apply ExteriorDuality.twoform_ext b
    intro v w
    simp [evaluate_pullbackTwoForm]
  map_smul' c α := by
    apply ExteriorDuality.twoform_ext b
    intro v w
    simp [evaluate_pullbackTwoForm]

private def unit : E := NormedSpace.normalize (Classical.choose (exists_ne (0 : E)))
private theorem unit_norm : ‖(unit : E)‖ = 1 :=
  NormedSpace.norm_normalize (Classical.choose_spec (exists_ne (0 : E)))

private def preferredBasis (x : M) : Basis (Fin 4) ℝ E :=
  (FourDimensionalQuaternionicHodgeFrame.frameBasis
    (Q.reduction.Q (Q.frames.adaptedCore.indexAt x)) hdim unit unit_norm).toBasis

/-- Pointwise linear Hodge star on the actual tangent fiber, not merely on a
model-space chart. The tangent fiber is definitionally `E`; the gauge maps
below convert to and from its core-preferred coordinate representation. -/
def tangentHodgeStar (x : M) :
    TwoForm (TangentSpace 𝓘(ℝ,E) x) →ₗ[ℝ]
      TwoForm (TangentSpace 𝓘(ℝ,E) x) := by
  change TwoForm E →ₗ[ℝ] TwoForm E
  let k := Q.frames.adaptedCore.indexAt x
  let b := preferredBasis Q hdim x
  exact (pullbackTwoFormLinear b (Q.frames.toFrame k x).toLinearMap).comp
    ((canonicalStar (Q.reduction.Q k) hdim).comp
      (pullbackTwoFormLinear b (Q.frames.fromFrame k x).toLinearMap))

theorem tangentHodgeStar_eval (x : M) (α : TwoForm E) (v w : E) :
    BilinearExterior.evaluate v w (tangentHodgeStar Q hdim x α) =
      BilinearExterior.evaluate
        (Q.frames.toFrame (Q.frames.adaptedCore.indexAt x) x v)
        (Q.frames.toFrame (Q.frames.adaptedCore.indexAt x) x w)
        (canonicalStar (Q.reduction.Q (Q.frames.adaptedCore.indexAt x)) hdim
          (pullbackTwoForm (preferredBasis Q hdim x)
            (Q.frames.fromFrame (Q.frames.adaptedCore.indexAt x) x).toLinearMap α)) := by
  change BilinearExterior.evaluate v w
      ((pullbackTwoFormLinear (preferredBasis Q hdim x)
        (Q.frames.toFrame (Q.frames.adaptedCore.indexAt x) x).toLinearMap).comp
          ((canonicalStar (Q.reduction.Q (Q.frames.adaptedCore.indexAt x)) hdim).comp
            (pullbackTwoFormLinear (preferredBasis Q hdim x)
              (Q.frames.fromFrame (Q.frames.adaptedCore.indexAt x) x).toLinearMap)) α) = _
  exact evaluate_pullbackTwoForm _ _ _ _ _

/-- Any adapted local frame, converted into the actual tangent fiber,
computes the same global pointwise Hodge operator. -/
theorem tangentHodgeStar_local
    (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (b : Basis (Fin 4) ℝ E) (α : TwoForm E) :
    pullbackTwoForm b (localToTangentEquiv Q i x hi).toLinearMap
      (tangentHodgeStar Q hdim x α) =
    canonicalStar (Q.reduction.Q i) hdim
      (pullbackTwoForm b (localToTangentEquiv Q i x hi).toLinearMap α) := by
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  let T := Q.frames.coordChange i k x
  let C := (localToTangentEquiv Q i x hi).toLinearMap
  let β := pullbackTwoForm (preferredBasis Q hdim x)
    (Q.frames.fromFrame k x).toLinearMap α
  have hC (v : E) : C v = Q.frames.fromFrame k x (T v) := rfl
  have hβ : pullbackTwoForm b T.toLinearMap β =
      pullbackTwoForm b C α := by
    apply ExteriorDuality.twoform_ext b
    intro v w
    rw [evaluate_pullbackTwoForm, evaluate_pullbackTwoForm,
      evaluate_pullbackTwoForm]
    rfl
  have hoverlap := canonicalStar_overlap Q hdim i k x hi hk b β
  apply ExteriorDuality.twoform_ext b
  intro v w
  rw [evaluate_pullbackTwoForm]
  rw [tangentHodgeStar_eval]
  have hTC (z : E) : Q.frames.toFrame k x (C z) = T z := by
    rw [hC, Q.frames.to_from k x hk]
  change BilinearExterior.evaluate (Q.frames.toFrame k x (C v))
      (Q.frames.toFrame k x (C w))
      (canonicalStar (Q.reduction.Q k) hdim β) =
    BilinearExterior.evaluate v w
      (canonicalStar (Q.reduction.Q i) hdim (pullbackTwoForm b C α))
  rw [hTC, hTC]
  have h := congrArg (fun θ : TwoForm E => BilinearExterior.evaluate v w θ) hoverlap
  change BilinearExterior.evaluate v w
      (pullbackTwoForm b T.toLinearMap
        (canonicalStar (Q.reduction.Q k) hdim β)) =
    BilinearExterior.evaluate v w
      (canonicalStar (Q.reduction.Q i) hdim
        (pullbackTwoForm b T.toLinearMap β)) at h
  rw [evaluate_pullbackTwoForm] at h
  rw [hβ] at h
  exact h

end
end QuaternionicSymmetry.ManifoldQuaternionicFourGlobalHodge
