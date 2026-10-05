import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients
import QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrientation
import QuaternionicSymmetry.ManifoldTwistorVerticalComplex

/-! Quaternionic derivative conjugation preserves the oriented cross product
on the actual rank-three tangent endomorphism plane. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryOrientation

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicRankThreeOrientation
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldTwistorVerticalComplex
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] in
/-- Quaternionic commutators on the genuine tangent fiber realize twice the
standard coefficient cross product. -/
theorem tangentSynth_commutator_cross (x : M) (a b : Fin 3 → ℝ) :
    tangentSynth Q x a * tangentSynth Q x b -
        tangentSynth Q x b * tangentSynth Q x a =
      (2 : ℝ) • tangentSynth Q x (crossProduct a b) := by
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let S := Q.reduction.Q i
  let T := Q.frames.toFrame i x
  let F := Q.frames.fromFrame i x
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hTF (w : E) : T (F w) = w := Q.frames.to_from i x hi w
  ext v
  change F ((synth S a) (T (F ((synth S b) (T v))))) -
      F ((synth S b) (T (F ((synth S a) (T v))))) =
    (2 : ℝ) • F ((synth S (crossProduct a b)) (T v))
  rw [hTF, hTF, ← map_sub, ← map_smul]
  have h := congrArg (fun A : E →L[ℝ] E => A (T v))
    (synth_commutator_cross S a b)
  simpa only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] using
    congrArg F h

/-- The actual derivative normalizer acts by an orientation-preserving
orthogonal transformation of its quaternionic three-plane. -/
theorem coefficientAction_cross (f : QuaternionicIsometries Q)
    (x : M) (a b : Fin 3 → ℝ) :
    coefficientAction Q f x (crossProduct a b) =
      crossProduct (coefficientAction Q f x a)
        (coefficientAction Q f x b) := by
  let R := coefficientAction Q f x
  have heq : (2 : ℝ) • tangentSynth Q (f • x) (R (crossProduct a b)) =
      (2 : ℝ) • tangentSynth Q (f • x)
        (crossProduct (R a) (R b)) := by
    calc
      _ = tangentConjugation Q f x
            ((2 : ℝ) • tangentSynth Q x (crossProduct a b)) := by
        rw [map_smul, tangentSynth_coefficientAction]
      _ = tangentConjugation Q f x
            (tangentSynth Q x a * tangentSynth Q x b -
              tangentSynth Q x b * tangentSynth Q x a) := by
        rw [tangentSynth_commutator_cross]
      _ = tangentConjugation Q f x (tangentSynth Q x a) *
            tangentConjugation Q f x (tangentSynth Q x b) -
          tangentConjugation Q f x (tangentSynth Q x b) *
            tangentConjugation Q f x (tangentSynth Q x a) := by
        rw [map_sub, tangentConjugation_operator_mul,
          tangentConjugation_operator_mul]
      _ = tangentSynth Q (f • x) (R a) * tangentSynth Q (f • x) (R b) -
          tangentSynth Q (f • x) (R b) * tangentSynth Q (f • x) (R a) := by
        rw [tangentSynth_coefficientAction, tangentSynth_coefficientAction]
      _ = _ := tangentSynth_commutator_cross Q (f • x) (R a) (R b)
  have heq' := (smul_right_injective
    (TangentSpace 𝓘(ℝ,E) (f • x) →L[ℝ] TangentSpace 𝓘(ℝ,E) (f • x))
    (by norm_num : (2 : ℝ) ≠ 0)) heq
  exact tangentSynth_injective Q (f • x) heq'

private theorem squareNorm_add_dot (a b : Fin 3 → ℝ) :
    squareNorm (a + b) = squareNorm a + squareNorm b +
      2 * (a ⬝ᵥ b) := by
  change (∑ t : Fin 3, (a t + b t) * (a t + b t)) =
    (∑ t : Fin 3, a t * a t) + (∑ t : Fin 3, b t * b t) +
      2 * (∑ t : Fin 3, a t * b t)
  calc
    _ = ∑ t : Fin 3, (a t * a t + b t * b t + 2 * (a t * b t)) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem coefficientAction_dot (f : QuaternionicIsometries Q)
    (x : M) (a b : Fin 3 → ℝ) :
    (coefficientAction Q f x a) ⬝ᵥ (coefficientAction Q f x b) =
      a ⬝ᵥ b := by
  let R := coefficientAction Q f x
  have h := coefficientAction_squareNorm Q f x (a + b)
  rw [map_add, squareNorm_add_dot, squareNorm_add_dot,
    coefficientAction_squareNorm, coefficientAction_squareNorm] at h
  linarith

/-- The concrete SO(3) coefficient action restricts to the tangent plane of
the quaternionic unit sphere at each twistor point. -/
def coefficientVerticalAction (f : QuaternionicIsometries Q)
    (x : M) (a : coefficientSphere) :
    verticalSubmodule a →ₗ[ℝ]
      verticalSubmodule (coefficientSphereAction Q f x a) where
  toFun v := ⟨coefficientAction Q f x v.1, by
    change (coefficientAction Q f x a.1) ⬝ᵥ
      (coefficientAction Q f x v.1) = 0
    rw [coefficientAction_dot]
    exact v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact (coefficientAction Q f x).map_add u.1 v.1
  map_smul' r v := by
    apply Subtype.ext
    exact (coefficientAction Q f x).map_smul r v.1

/-- On the coefficient vertical line, derivative conjugation is complex
linear for the canonical cross-product complex structure. -/
theorem coefficientVerticalAction_complex
    (f : QuaternionicIsometries Q) (x : M)
    (a : coefficientSphere) (v : verticalSubmodule a) :
    coefficientVerticalAction Q f x a (verticalComplex a v) =
      verticalComplex (coefficientSphereAction Q f x a)
        (coefficientVerticalAction Q f x a v) := by
  apply Subtype.ext
  exact coefficientAction_cross Q f x a.1 v.1

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryOrientation
