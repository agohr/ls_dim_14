import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
The differential of a genuine quaternionic isometry acts by conjugation on
endomorphisms of the actual tangent fibers. The defining span-preservation
law implies that this conjugation carries the quaternionic three-plane into
the target three-plane.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicDerivativeAction

open ManifoldQuaternionicSpanSymmetry
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual derivative as a continuous linear equivalence of tangent
fibers. Its inverse is the derivative of the inverse diffeomorphism. -/
def tangentEquiv (f : QuaternionicIsometries Q) (x : M) :
    TangentSpace 𝓘(ℝ,E) x ≃L[ℝ] TangentSpace 𝓘(ℝ,E) (f • x) := by
  exact f.1.mfderivToContinuousLinearEquiv (by simp) x

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentEquiv_apply (f : QuaternionicIsometries Q) (x : M)
    (v : TangentSpace 𝓘(ℝ,E) x) :
    tangentEquiv Q f x v =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x v := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentEquiv_mul_apply (f g : QuaternionicIsometries Q)
    (x : M) (v : TangentSpace 𝓘(ℝ,E) x) :
    tangentEquiv Q (f * g) x v =
      tangentEquiv Q f (g • x) (tangentEquiv Q g x v) := by
  rw [tangentEquiv_apply, tangentEquiv_apply, tangentEquiv_apply]
  exact mfderiv_comp_apply x
    (f.1.contMDiff.mdifferentiable (by simp) (g • x))
    (g.1.contMDiff.mdifferentiable (by simp) x) v

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentEquiv_one_apply (x : M)
    (v : TangentSpace 𝓘(ℝ,E) x) :
    tangentEquiv Q 1 x v = v := by
  rw [tangentEquiv_apply]
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (id : M → M) x v = v
  rw [mfderiv_id]
  rfl

/-- Conjugation by the actual derivative on continuous tangent
endomorphisms. -/
def tangentConjugation (f : QuaternionicIsometries Q) (x : M) :
    (TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) ≃ₗ[ℝ]
      (TangentSpace 𝓘(ℝ,E) (f • x) →L[ℝ]
        TangentSpace 𝓘(ℝ,E) (f • x)) :=
  ((tangentEquiv Q f x).conjContinuousAlgEquiv).toLinearEquiv

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentConjugation_apply_tangentEquiv
    (f : QuaternionicIsometries Q) (x : M)
    (A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (v : TangentSpace 𝓘(ℝ,E) x) :
    tangentConjugation Q f x A (tangentEquiv Q f x v) =
      tangentEquiv Q f x (A v) := by
  simp [tangentConjugation, tangentEquiv]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentConjugation_mul (f g : QuaternionicIsometries Q)
    (x : M)
    (A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) :
    tangentConjugation Q (f * g) x A =
      tangentConjugation Q f (g • x) (tangentConjugation Q g x A) := by
  ext w
  obtain ⟨v, rfl⟩ := (tangentEquiv Q (f * g) x).surjective w
  calc
    tangentConjugation Q (f * g) x A (tangentEquiv Q (f * g) x v) =
        tangentEquiv Q (f * g) x (A v) :=
      tangentConjugation_apply_tangentEquiv Q (f * g) x A v
    _ = tangentEquiv Q f (g • x) (tangentEquiv Q g x (A v)) :=
      tangentEquiv_mul_apply Q f g x (A v)
    _ = tangentConjugation Q f (g • x) (tangentConjugation Q g x A)
        (tangentEquiv Q (f * g) x v) := by
      rw [tangentEquiv_mul_apply]
      rw [tangentConjugation_apply_tangentEquiv Q f (g • x)
        (tangentConjugation Q g x A) (tangentEquiv Q g x v)]
      rw [tangentConjugation_apply_tangentEquiv Q g x A v]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentConjugation_one (x : M)
    (A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) :
    tangentConjugation Q 1 x A = A := by
  ext v
  have h := tangentConjugation_apply_tangentEquiv Q 1 x A v
  simpa only [tangentEquiv_one_apply] using h

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentConjugation_operator_mul
    (f : QuaternionicIsometries Q) (x : M)
    (A B : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) :
    tangentConjugation Q f x (A * B) =
      tangentConjugation Q f x A * tangentConjugation Q f x B := by
  exact (tangentEquiv Q f x).conjContinuousAlgEquiv.map_mul A B

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentConjugation_mem_span
    (f : QuaternionicIsometries Q) (x : M)
    (A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hA : A ∈ tangentSpan Q x) :
    tangentConjugation Q f x A ∈ tangentSpan Q (f • x) := by
  obtain ⟨B, hB, hAB⟩ := f.2.2.1 x A hA
  have hEq : tangentConjugation Q f x A = B := by
    ext w
    obtain ⟨v, rfl⟩ := (tangentEquiv Q f x).surjective w
    rw [tangentConjugation_apply_tangentEquiv, tangentEquiv_apply,
      tangentEquiv_apply]
    exact hAB v
  rw [hEq]
  exact hB

/-- The derivative's induced linear action on the actual quaternionic
endomorphism three-planes. -/
def tangentSpanMap (f : QuaternionicIsometries Q) (x : M) :
    tangentSpan Q x →ₗ[ℝ] tangentSpan Q (f • x) where
  toFun A := ⟨tangentConjugation Q f x A.1,
    tangentConjugation_mem_span Q f x A.1 A.2⟩
  map_add' A B := by
    apply Subtype.ext
    exact (tangentConjugation Q f x).map_add A.1 B.1
  map_smul' c A := by
    apply Subtype.ext
    exact (tangentConjugation Q f x).map_smul c A.1

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentSpanMap_apply (f : QuaternionicIsometries Q) (x : M)
    (A : tangentSpan Q x) :
    (tangentSpanMap Q f x A).1 = tangentConjugation Q f x A.1 := rfl

/-- Intrinsic twistor fiber: actual tangent endomorphisms in the quaternionic
three-plane that square to minus the identity. Identifying this with the
existing coefficient-sphere bundle is a separate, explicit comparison. -/
def IntrinsicTwistorFiber (x : M) :=
  {A : tangentSpan Q x // ∀ v : TangentSpace 𝓘(ℝ,E) x, A.1 (A.1 v) = -v}

/-- The differential conjugation carries quaternionic complex structures
from one tangent fiber to the next. -/
def intrinsicTwistorFiberAction (f : QuaternionicIsometries Q) (x : M) :
    IntrinsicTwistorFiber Q x → IntrinsicTwistorFiber Q (f • x) := by
  intro A
  refine ⟨tangentSpanMap Q f x A.1, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := (tangentEquiv Q f x).surjective w
  change tangentConjugation Q f x A.1.1
      (tangentConjugation Q f x A.1.1 (tangentEquiv Q f x v)) =
    -(tangentEquiv Q f x v)
  rw [tangentConjugation_apply_tangentEquiv,
    tangentConjugation_apply_tangentEquiv, A.2 v, map_neg]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem intrinsicTwistorFiberAction_apply
    (f : QuaternionicIsometries Q) (x : M)
    (A : IntrinsicTwistorFiber Q x) :
    (intrinsicTwistorFiberAction Q f x A).1 = tangentSpanMap Q f x A.1 := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem intrinsicTwistorFiberAction_one (x : M)
    (A : IntrinsicTwistorFiber Q x) :
    intrinsicTwistorFiberAction Q 1 x A = A := by
  apply Subtype.ext
  apply Subtype.ext
  exact tangentConjugation_one Q x A.1.1

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem intrinsicTwistorFiberAction_mul (f g : QuaternionicIsometries Q)
    (x : M) (A : IntrinsicTwistorFiber Q x) :
    intrinsicTwistorFiberAction Q (f * g) x A =
      intrinsicTwistorFiberAction Q f (g • x)
        (intrinsicTwistorFiberAction Q g x A) := by
  apply Subtype.ext
  apply Subtype.ext
  exact tangentConjugation_mul Q f g x A.1.1

end
end QuaternionicSymmetry.ManifoldQuaternionicDerivativeAction
