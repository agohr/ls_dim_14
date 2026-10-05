import QuaternionicSymmetry.ManifoldRiemannianOneJetInput
import QuaternionicSymmetry.ManifoldQuaternionicProperKernelFixedSet
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Genuine differential fixed vectors at a common fixed point. The
strict dimension bound uses the precisely registered one-jet rigidity
theorem, not a fixed-component dimension bound as an input. Identifying
this subspace with a submanifold tangent remains a separate step. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFixedTangentDimension

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFundamentalSymmetry
open ManifoldQuaternionicTorusAction QuaternionicTorusWeightKernel
open ManifoldRiemannianOneJetInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The common fixed vectors of the actual differentials. The fixed-point
proof makes all these maps endomorphisms of the same geometric fiber. -/
def fixedTangentSpace (S : Subgroup (QuaternionicIsometries Q))
    (x : M) (_hx : x ∈ fixedPoints Q S) :
    Submodule ℝ (TangentSpace 𝓘(ℝ,E) x) where
  carrier := {v | ∀ f ∈ S, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw f hf
    rw [map_add, hv f hf, hw f hf]
  smul_mem' := by
    intro c v hv f hf
    rw [map_smul, hv f hf]

theorem fixedTangentSpace_ne_top [T2Space M] [SecondCountableTopology M]
    [PreconnectedSpace M]
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    (S : Subgroup (QuaternionicIsometries Q)) (hS : ∃ f ∈ S, f ≠ 1)
    (x : M) (hx : x ∈ fixedPoints Q S) :
    fixedTangentSpace Q S x hx ≠ ⊤ := by
  obtain ⟨f, hfS, hf⟩ := hS
  intro htop
  apply hf
  apply Subtype.ext
  apply hjet Q f.1 (Diffeomorph.refl 𝓘(ℝ,E) M ∞) f.2.1 (metric_refl Q) x
  · exact hx f hfS
  · intro v
    have hv : v ∈ fixedTangentSpace Q S x hx := by rw [htop]; trivial
    have hfix := hv f hfS
    simpa only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply]
      using hfix

/-- Strict dimension drop for the genuine invariant tangent subspace.
No dimension of a fixed submanifold is supplied as a premise. -/
theorem fixedTangentSpace_finrank_lt [T2Space M] [SecondCountableTopology M]
    [PreconnectedSpace M]
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    (S : Subgroup (QuaternionicIsometries Q)) (hS : ∃ f ∈ S, f ≠ 1)
    (x : M) (hx : x ∈ fixedPoints Q S) :
      Module.finrank ℝ (fixedTangentSpace Q S x hx) < Module.finrank ℝ E := by
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    (inferInstance : FiniteDimensional ℝ E)
  exact Submodule.finrank_lt (fixedTangentSpace_ne_top Q hjet S hS x hx)

/-- The connected weight kernel of a faithful rank-at-least-two torus
acts with a strictly smaller invariant tangent space at every fixed point. -/
theorem connectedKernel_fixedTangent_finrank_lt [T2Space M]
    [SecondCountableTopology M] [PreconnectedSpace M]
    (hjet : RiemannianOneJetRigidityOnModel (E := E) (M := M))
    {r : ℕ} (A : ContinuousTorusAction Q r) (hA : A.Faithful)
    (hr : 2 ≤ r) (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (x : M) (hx : x ∈ ContinuousTorusAction.connectedKernelFixedSet Q A μ) :
    Module.finrank ℝ (fixedTangentSpace Q
      (ContinuousTorusAction.connectedKernelImage Q A μ) x hx) <
      Module.finrank ℝ E := by
  obtain ⟨t, ht, hne⟩ := connectedKernel_has_nonidentity μ hr hμ
  apply fixedTangentSpace_finrank_lt Q hjet
  refine ⟨A.representation t, ⟨t, ht, rfl⟩, ?_⟩
  intro h
  apply hne
  apply hA
  simpa using h

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedTangentDimension
