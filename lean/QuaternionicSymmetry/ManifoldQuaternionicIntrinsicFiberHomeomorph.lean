import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison

/-! The already established pointwise quaternionic coefficient equivalence is
continuous in each fixed tangent fiber. The inverse uses the finite-dimensional
linear isomorphism between coefficients and the genuine tangent three-plane. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIntrinsicFiberHomeomorph

open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicSpanSymmetry
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

instance (x : M) : TopologicalSpace (IntrinsicTwistorFiber Q x) := by
  unfold IntrinsicTwistorFiber
  infer_instance

def tangentSynthLinear (x : M) :
    (Fin 3 → ℝ) →ₗ[ℝ] tangentSpan Q x where
  toFun a := ⟨tangentSynth Q x a, tangentSynth_mem_span Q x a⟩
  map_add' a b := by
    apply Subtype.ext
    exact tangentSynth_add Q x a b
  map_smul' c a := by
    apply Subtype.ext
    exact tangentSynth_smul Q x c a

def tangentSynthLinearEquiv (x : M) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] tangentSpan Q x :=
  LinearEquiv.ofBijective (tangentSynthLinear Q x)
    ⟨fun a b hab => tangentSynth_injective Q x (congrArg Subtype.val hab),
      by
        intro A
        obtain ⟨a, ha⟩ := exists_tangentSynth_of_mem Q x A.1 A.2
        exact ⟨a, Subtype.ext ha⟩⟩

theorem continuous_preferredFiberEquiv_symm (x : M) :
    Continuous ((preferredFiberEquiv Q x).symm) := by
  let L := tangentSynthLinearEquiv Q x
  haveI : FiniteDimensional ℝ (tangentSpan Q x) :=
    LinearEquiv.finiteDimensional L
  have hlin : Continuous L.symm := L.symm.toLinearMap.continuous_of_finiteDimensional
  have hA : Continuous (fun A : IntrinsicTwistorFiber Q x => (A.1 : tangentSpan Q x)) :=
    continuous_subtype_val
  have hcoord : Continuous (fun A : IntrinsicTwistorFiber Q x => L.symm A.1) :=
    hlin.comp hA
  have heq (A : IntrinsicTwistorFiber Q x) :
      L.symm A.1 = ((preferredFiberEquiv Q x).symm A).1 := by
    apply L.injective
    apply Subtype.ext
    change tangentSynth Q x (L.symm A.1) =
      tangentSynth Q x (((preferredFiberEquiv Q x).symm A).1)
    rw [show tangentSynth Q x (L.symm A.1) = A.1.1 from
      congrArg Subtype.val (L.apply_symm_apply A.1)]
    have h := congrArg (fun B : IntrinsicTwistorFiber Q x => B.1.1)
      ((preferredFiberEquiv Q x).apply_symm_apply A)
    have h' : tangentSynth Q x (((preferredFiberEquiv Q x).symm A).1) = A.1.1 := by
      simpa only [preferredFiberEquiv, Equiv.ofBijective_apply,
        preferredToIntrinsic_operator] using h
    exact h'.symm
  have hsub : Continuous (fun A : IntrinsicTwistorFiber Q x =>
      (⟨L.symm A.1, by rw [heq A]; exact ((preferredFiberEquiv Q x).symm A).2⟩ :
        coefficientSphere)) :=
    hcoord.subtype_mk _
  exact hsub.congr (fun A => Subtype.ext (heq A))

end
end QuaternionicSymmetry.ManifoldQuaternionicIntrinsicFiberHomeomorph
