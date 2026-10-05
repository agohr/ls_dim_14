import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryAction

/-! The actual derivative-conjugation action expressed in the three real
coefficients of an adapted quaternionic tangent frame. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorSphereBundle
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The adapted quaternionic generators are a genuine basis of the actual
tangent endomorphism three-plane at every point. -/
def tangentSpanCoefficientEquiv (x : M) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] tangentSpan Q x :=
  LinearEquiv.ofBijective
    { toFun := fun a => ⟨tangentSynth Q x a, tangentSynth_mem_span Q x a⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        exact tangentSynth_add Q x a b
      map_smul' := by
        intro c a
        apply Subtype.ext
        exact tangentSynth_smul Q x c a }
    ⟨by
      intro a b h
      exact tangentSynth_injective Q x (congrArg Subtype.val h),
     by
      intro A
      obtain ⟨a, ha⟩ := exists_tangentSynth_of_mem Q x A.1 A.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem tangentSpanCoefficientEquiv_apply (x : M) (a : Fin 3 → ℝ) :
    ((tangentSpanCoefficientEquiv Q x) a).1 = tangentSynth Q x a := rfl

/-- Matrix-free three-dimensional coefficient action induced by the actual
derivative of a quaternionic isometry. In fixed adapted charts its matrix
entries are the functions whose smoothness must be established locally. -/
def coefficientAction (f : QuaternionicIsometries Q) (x : M) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  ((tangentSpanCoefficientEquiv Q (f • x)).symm.toLinearMap).comp
    ((tangentSpanMap Q f x).comp (tangentSpanCoefficientEquiv Q x).toLinearMap)

theorem tangentSynth_coefficientAction (f : QuaternionicIsometries Q)
    (x : M) (a : Fin 3 → ℝ) :
    tangentSynth Q (f • x) (coefficientAction Q f x a) =
      tangentConjugation Q f x (tangentSynth Q x a) := by
  change ((tangentSpanCoefficientEquiv Q (f • x))
    ((tangentSpanCoefficientEquiv Q (f • x)).symm
      (tangentSpanMap Q f x ((tangentSpanCoefficientEquiv Q x) a)))).1 = _
  rw [(tangentSpanCoefficientEquiv Q (f • x)).apply_symm_apply]
  rfl

theorem coefficientAction_one (x : M) (a : Fin 3 → ℝ) :
    coefficientAction Q 1 x a = a := by
  apply tangentSynth_injective Q x
  rw [← tangentConjugation_one Q x (tangentSynth Q x a)]
  exact tangentSynth_coefficientAction Q 1 x a

theorem coefficientAction_mul (f g : QuaternionicIsometries Q)
    (x : M) (a : Fin 3 → ℝ) :
    coefficientAction Q (f * g) x a =
      coefficientAction Q f (g • x) (coefficientAction Q g x a) := by
  apply tangentSynth_injective Q (f • (g • x))
  calc
    tangentSynth Q (f • (g • x)) (coefficientAction Q (f * g) x a) =
        tangentConjugation Q (f * g) x (tangentSynth Q x a) :=
      tangentSynth_coefficientAction Q (f * g) x a
    _ = tangentConjugation Q f (g • x)
          (tangentConjugation Q g x (tangentSynth Q x a)) :=
      tangentConjugation_mul Q f g x (tangentSynth Q x a)
    _ = tangentSynth Q (f • (g • x))
          (coefficientAction Q f (g • x) (coefficientAction Q g x a)) := by
      rw [← tangentSynth_coefficientAction Q g x a,
        ← tangentSynth_coefficientAction Q f (g • x)]

/-- The actual stabilizer of a base point acts linearly on its intrinsic
quaternionic three-plane, expressed in a fixed adapted coefficient frame. -/
def isotropyCoefficientRepresentation (x : M) :
    (MulAction.stabilizer (QuaternionicIsometries Q) x) →*
      Module.End ℝ (Fin 3 → ℝ) where
  toFun f := coefficientAction Q f.1 x
  map_one' := by
    apply LinearMap.ext
    intro a
    exact coefficientAction_one Q x a
  map_mul' f g := by
    apply LinearMap.ext
    intro a
    change coefficientAction Q (f.1 * g.1) x a =
      coefficientAction Q f.1 x (coefficientAction Q g.1 x a)
    rw [coefficientAction_mul, g.2]

/-- An actual quaternionic isometry rotates, rather than dilates, the
three-dimensional quaternionic coefficient plane. -/
theorem coefficientAction_squareNorm (f : QuaternionicIsometries Q)
    (x : M) (a : Fin 3 → ℝ) :
    squareNorm (coefficientAction Q f x a) = squareNorm a := by
  let b := coefficientAction Q f x a
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  let v := Q.frames.fromFrame i x w
  have hv : v ≠ 0 := by
    intro hzero
    have h := congrArg (Q.frames.toFrame i x) hzero
    rw [Q.frames.to_from i x
      ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x)] at h
    exact hw (by simpa using h)
  have hv' : tangentEquiv Q f x v ≠ 0 := by
    intro h
    exact hv ((tangentEquiv Q f x).injective (by simpa using h))
  have hsqb := tangentSynth_square Q (f • x) b (tangentEquiv Q f x v)
  have hsqa := tangentSynth_square Q x a v
  have hcomm : tangentSynth Q (f • x) b
      (tangentSynth Q (f • x) b (tangentEquiv Q f x v)) =
      tangentEquiv Q f x (tangentSynth Q x a (tangentSynth Q x a v)) := by
    simp only [b, tangentSynth_coefficientAction]
    rw [tangentConjugation_apply_tangentEquiv,
      tangentConjugation_apply_tangentEquiv]
  have hscalar : (-(squareNorm b)) • tangentEquiv Q f x v =
      (-(squareNorm a)) • tangentEquiv Q f x v := by
    calc
      _ = tangentSynth Q (f • x) b
            (tangentSynth Q (f • x) b (tangentEquiv Q f x v)) := hsqb.symm
      _ = tangentEquiv Q f x
            (tangentSynth Q x a (tangentSynth Q x a v)) := hcomm
      _ = _ := by rw [hsqa, map_smul]
  have hcoeff := (smul_left_injective ℝ hv') hscalar
  dsimp [b] at hcoeff ⊢
  linarith

/-- The induced action on the unit sphere of preferred quaternionic
coefficients. -/
def coefficientSphereAction (f : QuaternionicIsometries Q) (x : M)
    (a : coefficientSphere) : coefficientSphere :=
  ⟨coefficientAction Q f x a.1,
    (coefficientAction_squareNorm Q f x a.1).trans a.2⟩

theorem coefficientSphereAction_one (x : M) (a : coefficientSphere) :
    coefficientSphereAction Q 1 x a = a := by
  apply Subtype.ext
  exact coefficientAction_one Q x a.1

theorem coefficientSphereAction_mul (f g : QuaternionicIsometries Q)
    (x : M) (a : coefficientSphere) :
    coefficientSphereAction Q (f * g) x a =
      coefficientSphereAction Q f (g • x)
        (coefficientSphereAction Q g x a) := by
  apply Subtype.ext
  exact coefficientAction_mul Q f g x a.1

theorem preferredToIntrinsic_coefficientSphereAction
    (f : QuaternionicIsometries Q) (x : M) (a : coefficientSphere) :
    preferredToIntrinsic Q (f • x) (coefficientSphereAction Q f x a) =
      intrinsicTwistorFiberAction Q f x (preferredToIntrinsic Q x a) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [preferredToIntrinsic_operator]
  change tangentSynth Q (f • x) (coefficientAction Q f x a.1) =
    tangentConjugation Q f x ((preferredToIntrinsic Q x a).1.1)
  rw [preferredToIntrinsic_operator]
  exact tangentSynth_coefficientAction Q f x a.1

theorem twistorMap_preferredPoint (f : QuaternionicIsometries Q)
    (x : M) (a : coefficientSphere) :
    twistorMap Q f (preferredPoint Q x a) =
      preferredPoint Q (f • x) (coefficientSphereAction Q f x a) := by
  change preferredPoint Q (f • x)
      ((preferredFiberEquiv Q (f • x)).symm
        (intrinsicTwistorFiberAction Q f x (preferredToIntrinsic Q x a))) = _
  congr 1
  apply (preferredFiberEquiv Q (f • x)).injective
  rw [(preferredFiberEquiv Q (f • x)).apply_symm_apply]
  exact (preferredToIntrinsic_coefficientSphereAction Q f x a).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients
