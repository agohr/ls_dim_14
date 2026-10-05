import QuaternionicSymmetry.ManifoldQuaternionicDerivativeAction
import QuaternionicSymmetry.ManifoldTwistorSphereBundle
import QuaternionicSymmetry.QuaternionicScalarTrace

/-! A coefficient quaternionic unit vector gives an intrinsic complex
structure on the actual tangent fiber. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison

open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicSpanSymmetry
open ManifoldTwistorSphereBundle
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Quaternionic coefficients as an endomorphism of the actual tangent fiber. -/
def tangentSynth (x : M) (a : Fin 3 → ℝ) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  (Q.frames.fromFrame i x).comp
    ((synth (Q.reduction.Q i) a).comp (Q.frames.toFrame i x))

omit [FiniteDimensional ℝ E] in
theorem tangentSynth_eq_sum (x : M) (a : Fin 3 → ℝ) :
    tangentSynth Q x a = ∑ t : Fin 3, a t • tangentGenerator Q x t := by
  ext v
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let S := Q.reduction.Q i
  let T := Q.frames.toFrame i x
  let F := Q.frames.fromFrame i x
  change F ((synth S a) (T v)) =
    ∑ t : Fin 3, a t • F (VectorBundleFrameTransitions.quaternionicGenerator S t (T v))
  rw [ManifoldQuaternionicRankThreeOrthogonal.synth_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sum, map_smul]

omit [FiniteDimensional ℝ E] in
theorem tangentSynth_mem_span (x : M) (a : Fin 3 → ℝ) :
    tangentSynth Q x a ∈ tangentSpan Q x := by
  rw [tangentSynth_eq_sum]
  apply Submodule.sum_mem
  intro t _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨t, rfl⟩

theorem tangentSynth_injective (x : M) :
    Function.Injective (tangentSynth Q x) := by
  intro a b hab
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let S := Q.reduction.Q i
  let T := Q.frames.toFrame i x
  let F := Q.frames.fromFrame i x
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hTF (w : E) : T (F w) = w := Q.frames.to_from i x hi w
  have hS : synth S a = synth S b := by
    ext w
    have h := congrArg
      (fun A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x =>
        T (A (F w))) hab
    change T (F (synth S a (T (F w)))) =
      T (F (synth S b (T (F w)))) at h
    simpa only [hTF] using h
  exact (Function.LeftInverse.injective (coeff_synth S)) hS

omit [FiniteDimensional ℝ E] in
theorem tangentSynth_zero (x : M) :
    tangentSynth Q x 0 = 0 := by
  rw [tangentSynth_eq_sum]
  simp

omit [FiniteDimensional ℝ E] in
theorem tangentSynth_add (x : M) (a b : Fin 3 → ℝ) :
    tangentSynth Q x (a + b) = tangentSynth Q x a + tangentSynth Q x b := by
  simp [tangentSynth_eq_sum, Finset.sum_add_distrib, add_smul]

omit [FiniteDimensional ℝ E] in
theorem tangentSynth_smul (x : M) (c : ℝ) (a : Fin 3 → ℝ) :
    tangentSynth Q x (c • a) = c • tangentSynth Q x a := by
  simp [tangentSynth_eq_sum, Finset.smul_sum, smul_smul]

omit [FiniteDimensional ℝ E] in
theorem tangentSynth_basis (x : M) (t : Fin 3) :
    tangentSynth Q x (Pi.basisFun ℝ (Fin 3) t) = tangentGenerator Q x t := by
  rw [tangentSynth_eq_sum]
  simp [Pi.basisFun_apply]

omit [FiniteDimensional ℝ E] in
/-- Every operator in the actual quaternionic three-plane has unique
coefficient coordinates in the preferred adapted frame. -/
theorem exists_tangentSynth_of_mem (x : M)
    (A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hA : A ∈ tangentSpan Q x) :
    ∃ a : Fin 3 → ℝ, tangentSynth Q x a = A := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
      obtain ⟨t, rfl⟩ := hA
      exact ⟨Pi.basisFun ℝ (Fin 3) t, tangentSynth_basis Q x t⟩
  | zero => exact ⟨0, tangentSynth_zero Q x⟩
  | add A B hA hB ihA ihB =>
      obtain ⟨a, rfl⟩ := ihA
      obtain ⟨b, rfl⟩ := ihB
      exact ⟨a + b, tangentSynth_add Q x a b⟩
  | smul c A hA ihA =>
      obtain ⟨a, rfl⟩ := ihA
      exact ⟨c • a, tangentSynth_smul Q x c a⟩

omit [FiniteDimensional ℝ E] in
theorem synth_square (S : QuaternionicStructure E) (a : Fin 3 → ℝ) :
    (synth S a) ^ 2 =
      (-(squareNorm a)) • (1 : E →L[ℝ] E) := by
  have h := QuaternionicScalarTrace.synth_anticommutator S a a
  change synth S a * synth S a + synth S a * synth S a =
    (-(2 * squareNorm a)) • (1 : E →L[ℝ] E) at h
  rw [pow_two]
  calc
    synth S a * synth S a =
        (1 / 2 : ℝ) • (synth S a * synth S a + synth S a * synth S a) := by module
    _ = (1 / 2 : ℝ) • ((-(2 * squareNorm a)) • (1 : E →L[ℝ] E)) := by rw [h]
    _ = (-(squareNorm a)) • (1 : E →L[ℝ] E) := by module

omit [FiniteDimensional ℝ E] in
theorem tangentSynth_square (x : M) (a : Fin 3 → ℝ)
    (v : TangentSpace 𝓘(ℝ,E) x) :
    tangentSynth Q x a (tangentSynth Q x a v) =
      (-(squareNorm a)) • v := by
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let S := Q.reduction.Q i
  let T := Q.frames.toFrame i x
  let F := Q.frames.fromFrame i x
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hTF (w : E) : T (F w) = w := Q.frames.to_from i x hi w
  have hFT (w : TangentSpace 𝓘(ℝ,E) x) : F (T w) = w := Q.frames.from_to i x hi w
  have hs := congrArg (fun A : E →L[ℝ] E => A (T v)) (synth_square S a)
  change (synth S a) ((synth S a) (T v)) =
    (-(squareNorm a)) • T v at hs
  change F ((synth S a) (T (F ((synth S a) (T v))))) = _
  rw [hTF, hs, map_smul, hFT]

/-- The existing coefficient sphere maps into the intrinsic fiber of
quaternionic complex structures. -/
def toIntrinsicFiber (z : TwistorSphere Q) :
    IntrinsicTwistorFiber Q (projection Q z) := by
  let x := projection Q z
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let a := localCoordinate Q i z
    (Q.frames.adaptedCore.mem_baseSet_at x)
  refine ⟨⟨tangentSynth Q x a.1, tangentSynth_mem_span Q x a.1⟩, ?_⟩
  intro v
  simpa [a.2] using tangentSynth_square Q x a.1 v

/-- A point in the existing sphere bundle expressed in the preferred adapted
chart at its base point. -/
def preferredPoint (x : M) (a : coefficientSphere) : TwistorSphere Q :=
  pointOfLocal Q (Q.frames.adaptedCore.indexAt x) x
    (Q.frames.adaptedCore.mem_baseSet_at x) a

theorem toIntrinsicFiber_preferredPoint (x : M) (a : coefficientSphere) :
    (toIntrinsicFiber Q (preferredPoint Q x a)).1.1 = tangentSynth Q x a.1 := by
  change tangentSynth Q x
      (localCoordinate Q (Q.frames.adaptedCore.indexAt x)
        (pointOfLocal Q (Q.frames.adaptedCore.indexAt x) x
          (Q.frames.adaptedCore.mem_baseSet_at x) a)
        (Q.frames.adaptedCore.mem_baseSet_at x)).1 = _
  rw [localCoordinate_pointOfLocal]

def preferredToIntrinsic (x : M) (a : coefficientSphere) :
    IntrinsicTwistorFiber Q x := by
  simpa only [preferredPoint, projection_pointOfLocal] using
    toIntrinsicFiber Q (preferredPoint Q x a)

theorem preferredToIntrinsic_operator (x : M) (a : coefficientSphere) :
    (preferredToIntrinsic Q x a).1.1 = tangentSynth Q x a.1 := by
  exact toIntrinsicFiber_preferredPoint Q x a

theorem preferredPoint_toIntrinsic_injective (x : M) :
    Function.Injective (fun a : coefficientSphere =>
      preferredToIntrinsic Q x a) := by
  intro a b hab
  have h := congrArg (fun A : IntrinsicTwistorFiber Q x => A.1.1) hab
  change (preferredToIntrinsic Q x a).1.1 =
    (preferredToIntrinsic Q x b).1.1 at h
  rw [preferredToIntrinsic_operator Q x a,
    preferredToIntrinsic_operator Q x b] at h
  exact Subtype.ext ((tangentSynth_injective Q x) h)

theorem preferredToIntrinsic_surjective (x : M) :
    Function.Surjective (preferredToIntrinsic Q x) := by
  intro A
  obtain ⟨a, ha⟩ := exists_tangentSynth_of_mem Q x A.1.1 A.1.2
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let F := Q.frames.fromFrame i x
  let T := Q.frames.toFrame i x
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hv : F w ≠ 0 := by
    intro hzero
    have h := congrArg T hzero
    rw [Q.frames.to_from i x hi] at h
    exact hw (by simpa using h)
  have hsq := tangentSynth_square Q x a (F w)
  rw [ha] at hsq
  have hscalar : (-(squareNorm a)) • F w = (-1 : ℝ) • F w := by
    calc
      (-(squareNorm a)) • F w = A.1.1 (A.1.1 (F w)) := hsq.symm
      _ = -(F w) := A.2 (F w)
      _ = (-1 : ℝ) • F w := by simp
  have hcoeff : -(squareNorm a) = (-1 : ℝ) :=
    (smul_left_injective ℝ hv) hscalar
  have haunit : squareNorm a = 1 := by linarith
  refine ⟨⟨a, haunit⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [preferredToIntrinsic_operator Q x]
  exact ha

/-- Pointwise equivalence between the existing coefficient two-sphere and
the intrinsic sphere of complex structures in the tangent quaternionic
three-plane. -/
def preferredFiberEquiv (x : M) :
    coefficientSphere ≃ IntrinsicTwistorFiber Q x :=
  Equiv.ofBijective (preferredToIntrinsic Q x)
    ⟨preferredPoint_toIntrinsic_injective Q x,
      preferredToIntrinsic_surjective Q x⟩

theorem preferredPoint_intrinsic_roundtrip (z : TwistorSphere Q) :
    preferredPoint Q (projection Q z)
      ((preferredFiberEquiv Q (projection Q z)).symm
        (toIntrinsicFiber Q z)) = z := by
  let x := projection Q z
  let i := Q.frames.adaptedCore.indexAt x
  let a := localCoordinate Q i z (Q.frames.adaptedCore.mem_baseSet_at x)
  have h : preferredToIntrinsic Q x a = toIntrinsicFiber Q z := by
    apply Subtype.ext
    apply Subtype.ext
    rw [preferredToIntrinsic_operator]
    rfl
  have ha : (preferredFiberEquiv Q x).symm (toIntrinsicFiber Q z) = a := by
    apply (preferredFiberEquiv Q x).injective
    rw [(preferredFiberEquiv Q x).apply_symm_apply]
    exact h.symm
  rw [ha]
  exact pointOfLocal_localCoordinate Q i z
    (Q.frames.adaptedCore.mem_baseSet_at x)

end
end QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison
