import QuaternionicSymmetry.ManifoldQuaternionicFixedComponentComplexAtlas
import QuaternionicSymmetry.ManifoldQuaternionicInducedComplexImmersion

/-! The actual transported kernel-fixed component inclusion is a real
immersion. The derivative is obtained by factoring through the proven
intrinsic twistor immersion and the transported real diffeomorphism. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFixedComponentComplexImmersion

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorFixedComponent
open ManifoldQuaternionicFixedComponentComplexAtlas
open ManifoldQuaternionicInducedComplexImmersion
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorLiftedFixedSet
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [CompactSpace N] [PreconnectedSpace N] [T2Space M]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hInj : Function.Injective ι)
  (S : Subgroup (QuaternionicIsometries P.tangent))
  (z : SphereBundleTotal R.tangent)
  (hRange : Set.range ι = connectedComponentIn (fixedPoints P.tangent S) (ι z.1))
  (hQ : ∀ x ∈ Set.range ι, ∀ f ∈ S, ∀ a : Fin 3 → ℝ,
    coefficientAction P.tangent f x a = a)

private abbrev K := ↥(connectedComponentIn (fixedSpherePoints P.tangent S)
  (sphereTotalMap P R ι hι hR z))

include hSmooth hInj hRange hQ in
theorem inclusion_injective_derivative {m n : ℕ}
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n) :
    letI := A.charts
    letI := B.charts
    letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
      P R ι hι hR hSmooth hInj S z hRange hQ DR A
    ∀ w : K P R ι hι hR S z,
      Function.Injective (mfderiv 𝓘(ℝ,ComplexTwistorModel m)
        𝓘(ℝ,ComplexTwistorModel n)
        (Subtype.val : K P R ι hι hR S z → SphereBundleTotal P.tangent) w) := by
  letI := A.charts
  letI := B.charts
  letI := A.realManifold
  letI := B.realManifold
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
    P R ι hι hR hSmooth hInj S z hRange hQ DR A
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.realManifold
    P R ι hι hR hSmooth hInj S z hRange hQ DR A
  let Ψ : SphereBundleTotal R.tangent ≃ₘ⟮𝓘(ℝ,ComplexTwistorModel m),
      𝓘(ℝ,ComplexTwistorModel m)⟯ K P R ι hι hR S z :=
    HomeomorphTransportedManifold.diffeomorph
    (fixedComponentHomeomorph P R ι hι hR hSmooth hInj S z hRange hQ)
  let Φ := sphereTotalMap P R ι hι hR
  intro w u v huv
  have heq : (Subtype.val : K P R ι hι hR S z →
      SphereBundleTotal P.tangent) = Φ ∘ Ψ.symm := by
    funext a
    change (a : SphereBundleTotal P.tangent) = Φ (Ψ.symm a)
    dsimp only [Φ]
    rw [← fixedComponentHomeomorph_apply P R ι hι hR hSmooth hInj S z hRange hQ
      (Ψ.symm a)]
    change (a : SphereBundleTotal P.tangent) =
      ((Ψ (Ψ.symm a) : K P R ι hι hR S z) : SphereBundleTotal P.tangent)
    rw [Ψ.apply_symm_apply]
  have hΦ := sphereTotalMap_mfderiv_injective_compatible
    P R ι hSmooth hι hR DP DR A B (Ψ.symm w)
  have hΨ : Function.Injective (mfderiv 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel m) Ψ.symm w) :=
    (Ψ.symm.mfderivToContinuousLinearEquiv (by simp) w).injective
  have hchain := mfderiv_comp w
    ((ManifoldQuaternionicInducedComplexAtlas.sphereTotalMap_realSmooth_in_compatibleAtlases
      P R ι hSmooth hι hR DP DR A B).mdifferentiableAt
        (by simp) (x := Ψ.symm w))
    (Ψ.symm.contMDiff.mdifferentiableAt (by simp) (x := w))
  rw [← heq] at hchain
  apply hΨ
  apply hΦ
  have hu := congrArg (fun L : ComplexTwistorModel m →L[ℝ]
    ComplexTwistorModel n => L u) hchain
  have hv := congrArg (fun L : ComplexTwistorModel m →L[ℝ]
    ComplexTwistorModel n => L v) hchain
  exact hu.symm.trans (huv.trans hv)

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedComponentComplexImmersion
