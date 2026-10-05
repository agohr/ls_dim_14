import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorFiber
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients
import QuaternionicSymmetry.ManifoldQuaternionicIsometryOrientation

/-! The actual induced quaternionic tangent span determines a linear
isomorphism of quaternionic coefficient planes. This does not require the
inclusion derivative to be onto the ambient tangent space. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientMap
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicSpanFaithfulEvaluation
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryOrientation
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

include R hι in
private theorem exists_nonzero_derivative (x : N) :
    ∃ v : TangentSpace 𝓘(ℝ,F) x,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  let i := (tangentBundleCore 𝓘(ℝ,F) N).indexAt x
  let v := R.tangent.frames.fromFrame i x w
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrArg (R.tangent.frames.toFrame i x) hz
    rw [R.tangent.frames.to_from i x
      ((tangentBundleCore 𝓘(ℝ,F) N).mem_baseSet_at x)] at hh
    exact hw (by simpa using hh)
  refine ⟨v, fun h => hv (hι x ?_)⟩
  simpa using h

def spanExtension (x : N) (A : tangentSpan R.tangent x) :
    tangentSpan P.tangent (ι x) :=
  ⟨((hR.2 x A.1).1 A.2).choose, ((hR.2 x A.1).1 A.2).choose_spec.1⟩

theorem spanExtension_intertwines (x : N) (A : tangentSpan R.tangent x)
    (v : TangentSpace 𝓘(ℝ,F) x) :
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A.1 v) =
      (spanExtension P R ι hR x A).1
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) :=
  ((hR.2 x A.1).1 A.2).choose_spec.2 v

include hι in
/-- The extension is unique even though the ambient tangent space may be
strictly larger. A nonzero tangent image determines a quaternionic operator. -/
theorem spanExtension_unique (x : N) (A : tangentSpan R.tangent x)
    (B : tangentSpan P.tangent (ι x))
    (hB : ∀ v : TangentSpace 𝓘(ℝ,F) x,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A.1 v) =
        B.1 (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v)) :
    spanExtension P R ι hR x A = B := by
  obtain ⟨v,hv⟩ := exists_nonzero_derivative R ι hι x
  apply Subtype.ext
  exact tangentSpan_eq_of_apply_eq P.tangent (ι x) _ _
    (spanExtension P R ι hR x A).2 B.2
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) hv
    ((spanExtension_intertwines P R ι hR x A v).symm.trans (hB v))

def spanExtensionLinear (x : N) :
    tangentSpan R.tangent x →ₗ[ℝ] tangentSpan P.tangent (ι x) where
  toFun := spanExtension P R ι hR x
  map_add' A B := by
    apply spanExtension_unique P R ι hι hR
    intro v
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A.1 v + B.1 v) = _
    rw [map_add, spanExtension_intertwines P R ι hR x A,
      spanExtension_intertwines P R ι hR x B]
    rfl
  map_smul' c A := by
    apply spanExtension_unique P R ι hι hR
    intro v
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (c • A.1 v) = _
    rw [map_smul, spanExtension_intertwines P R ι hR x A]
    rfl

theorem spanExtensionLinear_injective (x : N) :
    Function.Injective (spanExtensionLinear P R ι hι hR x) := by
  intro A B h
  apply Subtype.ext
  ext v
  apply hι x
  rw [spanExtension_intertwines P R ι hR x A,
    spanExtension_intertwines P R ι hR x B]
  exact congrArg (fun C : tangentSpan P.tangent (ι x) =>
    C.1 (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v)) h

def coefficientMap (x : N) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (tangentSpanCoefficientEquiv P.tangent (ι x)).symm.toLinearMap.comp
    ((spanExtensionLinear P R ι hι hR x).comp
      (tangentSpanCoefficientEquiv R.tangent x).toLinearMap)

theorem coefficientMap_intertwines (x : N) (a : Fin 3 → ℝ)
    (v : TangentSpace 𝓘(ℝ,F) x) :
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (tangentSynth R.tangent x a v) =
      tangentSynth P.tangent (ι x) (coefficientMap P R ι hι hR x a)
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) := by
  have heq : tangentSynth P.tangent (ι x) (coefficientMap P R ι hι hR x a) =
      (spanExtension P R ι hR x ((tangentSpanCoefficientEquiv R.tangent x) a)).1 := by
    change ((tangentSpanCoefficientEquiv P.tangent (ι x))
      ((tangentSpanCoefficientEquiv P.tangent (ι x)).symm _)).1 = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [heq]
  exact spanExtension_intertwines P R ι hR x
    ((tangentSpanCoefficientEquiv R.tangent x) a) v

theorem coefficientMap_injective (x : N) :
    Function.Injective (coefficientMap P R ι hι hR x) :=
  (tangentSpanCoefficientEquiv P.tangent (ι x)).symm.injective.comp
    ((spanExtensionLinear_injective P R ι hι hR x).comp
      (tangentSpanCoefficientEquiv R.tangent x).injective)

/-- The ambient and induced quaternionic three-planes have equal dimension,
so the injective extension is in fact an isomorphism. -/
def coefficientEquiv (x : N) : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.ofBijective (coefficientMap P R ι hι hR x)
    ⟨coefficientMap_injective P R ι hι hR x,
      (LinearMap.injective_iff_surjective).1
        (coefficientMap_injective P R ι hι hR x)⟩

/-- Intertwining the quaternionic square identity on one nonzero tangent
image proves that the induced coefficient isomorphism preserves length. -/
theorem coefficientMap_squareNorm (x : N) (a : Fin 3 → ℝ) :
    squareNorm (coefficientMap P R ι hι hR x a) = squareNorm a := by
  obtain ⟨v, hv⟩ := exists_nonzero_derivative R ι hι x
  let d := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
  let b := coefficientMap P R ι hι hR x a
  have hb := tangentSynth_square P.tangent (ι x) b (d v)
  have ha := tangentSynth_square R.tangent x a v
  have hcomm : tangentSynth P.tangent (ι x) b
      (tangentSynth P.tangent (ι x) b (d v)) =
      d (tangentSynth R.tangent x a (tangentSynth R.tangent x a v)) := by
    rw [← coefficientMap_intertwines P R ι hι hR x a v,
      ← coefficientMap_intertwines P R ι hι hR x a
        (tangentSynth R.tangent x a v)]
  have hscalar : (-(squareNorm b)) • d v = (-(squareNorm a)) • d v := by
    calc
      _ = tangentSynth P.tangent (ι x) b
          (tangentSynth P.tangent (ι x) b (d v)) := hb.symm
      _ = d (tangentSynth R.tangent x a (tangentSynth R.tangent x a v)) := hcomm
      _ = _ := by rw [ha, map_smul]
  have hcoeff := (smul_left_injective ℝ hv) hscalar
  dsimp [b] at hcoeff ⊢
  linarith

/-- The induced map also preserves quaternionic orientation, as follows
from the commutator identity and the actual derivative intertwining. -/
theorem coefficientMap_cross (x : N) (a b : Fin 3 → ℝ) :
    coefficientMap P R ι hι hR x (crossProduct a b) =
      crossProduct (coefficientMap P R ι hι hR x a)
        (coefficientMap P R ι hι hR x b) := by
  obtain ⟨v,hv⟩ := exists_nonzero_derivative R ι hι x
  let C := coefficientMap P R ι hι hR x
  let d := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
  apply tangentSynth_injective P.tangent (ι x)
  apply tangentSpan_eq_of_apply_eq P.tangent (ι x) _ _
    (tangentSynth_mem_span _ _ _) (tangentSynth_mem_span _ _ _) (d v) hv
  have hs := congrArg
    (fun L : TangentSpace 𝓘(ℝ,F) x →L[ℝ] TangentSpace 𝓘(ℝ,F) x => L v)
    (tangentSynth_commutator_cross R.tangent x a b)
  have ht := congrArg
    (fun L : TangentSpace 𝓘(ℝ,E) (ι x) →L[ℝ] TangentSpace 𝓘(ℝ,E) (ι x) => L (d v))
    (tangentSynth_commutator_cross P.tangent (ι x) (C a) (C b))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply] at hs ht
  have h2 : (2 : ℝ) • tangentSynth P.tangent (ι x) (C (crossProduct a b)) (d v) =
      (2 : ℝ) • tangentSynth P.tangent (ι x) (crossProduct (C a) (C b)) (d v) := by
    calc
      _ = d ((2 : ℝ) • tangentSynth R.tangent x (crossProduct a b) v) := by
        rw [map_smul, coefficientMap_intertwines P R ι hι hR x]
      _ = d (tangentSynth R.tangent x a (tangentSynth R.tangent x b v) -
          tangentSynth R.tangent x b (tangentSynth R.tangent x a v)) := by rw [hs]
      _ = tangentSynth P.tangent (ι x) (C a)
            (tangentSynth P.tangent (ι x) (C b) (d v)) -
          tangentSynth P.tangent (ι x) (C b)
            (tangentSynth P.tangent (ι x) (C a) (d v)) := by
        rw [map_sub, coefficientMap_intertwines P R ι hι hR x,
          coefficientMap_intertwines P R ι hι hR x,
          coefficientMap_intertwines P R ι hι hR x,
          coefficientMap_intertwines P R ι hι hR x]
      _ = _ := ht
  exact (smul_right_injective (TangentSpace 𝓘(ℝ,E) (ι x))
    (by norm_num : (2 : ℝ) ≠ 0)) h2

private theorem squareNorm_add_dot (a b : Fin 3 → ℝ) :
    squareNorm (a + b) = squareNorm a + squareNorm b + 2 * (a ⬝ᵥ b) := by
  change (∑ t : Fin 3, (a t + b t) * (a t + b t)) =
    (∑ t : Fin 3, a t * a t) + (∑ t : Fin 3, b t * b t) +
      2 * (∑ t : Fin 3, a t * b t)
  calc
    _ = ∑ t : Fin 3, (a t * a t + b t * b t + 2 * (a t * b t)) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem coefficientMap_dot (x : N) (a b : Fin 3 → ℝ) :
    (coefficientMap P R ι hι hR x a) ⬝ᵥ (coefficientMap P R ι hι hR x b) =
      a ⬝ᵥ b := by
  have h := coefficientMap_squareNorm P R ι hι hR x (a + b)
  rw [map_add, squareNorm_add_dot, squareNorm_add_dot,
    coefficientMap_squareNorm, coefficientMap_squareNorm] at h
  linarith

/-- Actual unit-sphere map induced by the inclusion derivative. -/
def coefficientSphereMap (x : N) (a : coefficientSphere) : coefficientSphere :=
  ⟨coefficientMap P R ι hι hR x a.1,
    (coefficientMap_squareNorm P R ι hι hR x a.1).trans a.2⟩

/-- Although the submanifold has smaller tangent dimension, its twistor
sphere maps bijectively onto the ambient twistor sphere at that point. -/
def coefficientSphereEquiv (x : N) : coefficientSphere ≃ coefficientSphere where
  toFun := coefficientSphereMap P R ι hι hR x
  invFun a := ⟨(coefficientEquiv P R ι hι hR x).symm a.1, by
    have h := coefficientMap_squareNorm P R ι hι hR x
      ((coefficientEquiv P R ι hι hR x).symm a.1)
    change squareNorm ((coefficientEquiv P R ι hι hR x)
      ((coefficientEquiv P R ι hι hR x).symm a.1)) = _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans a.2⟩
  left_inv a := by
    apply Subtype.ext
    exact (coefficientEquiv P R ι hι hR x).symm_apply_apply a.1
  right_inv a := by
    apply Subtype.ext
    exact (coefficientEquiv P R ι hι hR x).apply_symm_apply a.1

theorem preferredToIntrinsic_coefficientSphereMap (x : N) (a : coefficientSphere) :
    preferredToIntrinsic P.tangent (ι x) (coefficientSphereMap P R ι hι hR x a) =
      ManifoldQuaternionicInducedTwistorFiber.intrinsicFiberMap P R ι hι hR x
        (preferredToIntrinsic R.tangent x a) := by
  apply Subtype.ext
  have h := spanExtension_unique P R ι hι hR x
    (preferredToIntrinsic R.tangent x a).1
    (preferredToIntrinsic P.tangent (ι x)
      (coefficientSphereMap P R ι hι hR x a)).1
    (by
      intro v
      simp only [preferredToIntrinsic_operator]
      exact coefficientMap_intertwines P R ι hι hR x a.1 v)
  have h' := spanExtension_unique P R ι hι hR x
    (preferredToIntrinsic R.tangent x a).1
    (ManifoldQuaternionicInducedTwistorFiber.intrinsicFiberMap P R ι hι hR x
      (preferredToIntrinsic R.tangent x a)).1
    (ManifoldQuaternionicInducedTwistorFiber.intrinsicFiberMap_intertwines
      P R ι hι hR x (preferredToIntrinsic R.tangent x a))
  exact h.symm.trans h'

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientMap
