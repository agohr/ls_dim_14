import QuaternionicSymmetry.ManifoldQuaternionicSubmanifoldInput
import QuaternionicSymmetry.ManifoldQuaternionicSpanFaithfulEvaluation

/-! Intrinsic twistor fibers of a genuine induced quaternionic submanifold
map uniquely into the ambient twistor fibers. The ambient complex structure
is determined by intertwining the actual inclusion derivative; its square
is proved on the whole ambient tangent space, not just the tangent image. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorFiber
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicSpanFaithfulEvaluation
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

include hι hR

theorem existsUnique_intrinsic_extension (x : N)
    (A : IntrinsicTwistorFiber R.tangent x) :
    ∃! B : IntrinsicTwistorFiber P.tangent (ι x),
      ∀ v : TangentSpace 𝓘(ℝ,F) x,
        mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A.1.1 v) =
          B.1.1 (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) := by
  obtain ⟨B, hB, hAB⟩ := (hR.2 x A.1.1).1 A.1.2
  let d := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  let i := (tangentBundleCore 𝓘(ℝ,F) N).indexAt x
  let v := R.tangent.frames.fromFrame i x w
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrArg (R.tangent.frames.toFrame i x) hz
    rw [R.tangent.frames.to_from i x
      ((tangentBundleCore 𝓘(ℝ,F) N).mem_baseSet_at x)] at hh
    exact hw (by simpa using hh)
  have hdv : d v ≠ 0 := by
    intro hz
    exact hv (hι x (by simpa using hz))
  have hsq : B (B (d v)) = -(d v) := by
    rw [← hAB v, ← hAB (A.1.1 v), A.2 v, map_neg]
  have hBsquare := tangentSpan_sq_neg_of_one_vector P.tangent (ι x)
    B hB (d v) hdv hsq
  refine ⟨⟨⟨B,hB⟩,hBsquare⟩, hAB, ?_⟩
  intro C hC
  apply Subtype.ext
  apply Subtype.ext
  exact tangentSpan_eq_of_apply_eq P.tangent (ι x) C.1.1 B C.1.2 hB
    (d v) hdv ((hC v).symm.trans (hAB v))

/-- The intrinsic fiber inclusion attached to the actual differential and
the actual induced quaternionic-span relation. -/
def intrinsicFiberMap (x : N) :
    IntrinsicTwistorFiber R.tangent x → IntrinsicTwistorFiber P.tangent (ι x) :=
  fun A => (existsUnique_intrinsic_extension P R ι hι hR x A).choose

theorem intrinsicFiberMap_intertwines (x : N)
    (A : IntrinsicTwistorFiber R.tangent x) (v : TangentSpace 𝓘(ℝ,F) x) :
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A.1.1 v) =
      (intrinsicFiberMap P R ι hι hR x A).1.1
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) :=
  (existsUnique_intrinsic_extension P R ι hι hR x A).choose_spec.1 v

theorem intrinsicFiberMap_injective (x : N) :
    Function.Injective (intrinsicFiberMap P R ι hι hR x) := by
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  ext v
  apply hι x
  rw [intrinsicFiberMap_intertwines P R ι hι hR x A v,
    intrinsicFiberMap_intertwines P R ι hι hR x B v, h]

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorFiber
