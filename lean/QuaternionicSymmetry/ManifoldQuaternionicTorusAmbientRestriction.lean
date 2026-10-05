import QuaternionicSymmetry.ManifoldQuaternionicTorusContactRestriction
import QuaternionicSymmetry.HolomorphicLineCorePullbackComposition

/-! The constructed intrinsic map of the full-torus component composes with
the induced twistor immersion to the literal ambient subtype inclusion. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientRestriction

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicFixedComponentComplexAtlas
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCorePullbackComposition
open ManifoldQuaternionicTorusToIntrinsicHolomorphic
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldRiemannianFixedComponentGenericInput
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [CompactSpace M] [CompactSpace N] [PreconnectedSpace N] [T2Space M]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hInj : Function.Injective ι)
  {r : ℕ} (T : ContinuousTorusAction P.tangent r)
  (μ : Fin r → ℤ)
  (z : SphereBundleTotal R.tangent)
  (hRange : Set.range ι = connectedComponentIn
    (ManifoldQuaternionicSpanSymmetry.fixedPoints P.tangent
      (T.connectedKernelImage P.tangent μ)) (ι z.1))
  (hQ : ∀ x ∈ Set.range ι, ∀ f ∈ T.connectedKernelImage P.tangent μ,
    ∀ a : Fin 3 → ℝ,
      ManifoldQuaternionicIsometryCoefficients.coefficientAction P.tangent f x a = a)

private abbrev Φ := sphereTotalMap P R ι hι hR
private abbrev c := Φ P R ι hι hR z
private abbrev Y := ↥(component P.tangent T (c P R ι hι hR z))

include hSmooth hInj hRange hQ in
/-- The nested torus-to-kernel map followed by the kernel-to-intrinsic
inverse has precisely the original ambient inclusion as composite with
the induced twistor immersion. -/
theorem sphereTotalMap_comp_torusToIntrinsic_eq_inclusion {m : ℕ}
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (A : CompatibleComplexAtlas R.tangent DR m) :
    letI := A.charts
    letI := charts P R ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
    let j := (biholomorph P R ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ DR A).symm ∘
      inclusionIntoConnectedKernelComponent P.tangent T μ
        (c P R ι hι hR z)
    Φ P R ι hι hR ∘ j =
      (Subtype.val : Y P R ι hι hR T z → SphereBundleTotal P.tangent) := by
  letI := A.charts
  letI := A.complexManifold
  letI := charts P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  letI := complexManifold P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  let Ψ := biholomorph P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  let k := inclusionIntoConnectedKernelComponent P.tangent T μ
    (c P R ι hι hR z)
  funext y
  change sphereTotalMap P R ι hι hR (Ψ.symm (k y)) = (y : SphereBundleTotal P.tangent)
  rw [← biholomorph_apply P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A (Ψ.symm (k y))]
  change ((Ψ (Ψ.symm (k y)) :
    ↥(connectedComponentIn
      (fixedSpherePoints P.tangent (T.connectedKernelImage P.tangent μ))
      (c P R ι hι hR z))) : SphereBundleTotal P.tangent) = y.1
  rw [Ψ.apply_symm_apply]
  rfl

include hSmooth hInj hRange hQ in
/-- For the actual full-torus component, the line obtained by first
restricting to the intrinsic smaller twistor and then to `Y` is the
literal ambient line restricted by the ambient subtype inclusion. -/
theorem torus_iteratedLine_eq_ambientRestriction {a b m n : ℕ}
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P R ι DP DR)
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (H : FixedComponentAtlas (𝓘(ℝ,E).prod (𝓡 2))
      (liftedSet P.tangent T.imageSubgroup)
      (c P R ι hι hR z) a)
    (C : letI := B.charts
      ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas P.tangent DP B T.imageSubgroup H) b)
    (hLee : GeneralSmoothMapSource.LeeEmbeddedCodomainRestrictionTheorem)
    (L : letI := B.charts
      LineCore 𝓘(ℂ,ComplexTwistorModel n)) :
    letI := A.charts
    letI := B.charts
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      (Y P R ι hι hR T z) := C.charts
    letI := charts P R ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
    let j := (biholomorph P R ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ DR A).symm ∘
      inclusionIntoConnectedKernelComponent P.tangent T μ
        (c P R ι hι hR z)
    let hj := (torusToIntrinsic_holomorphic_injective
      P R ι hι hR hSmooth hInj T μ z hRange hQ
      DP DR hTot A B H C hLee).1
    let hΦ := ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      P R ι hSmooth hι hR DP DR hTot A B
    pullbackLineCore 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,EuclideanSpace ℂ (Fin b))
      (pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,ComplexTwistorModel m) L (Φ P R ι hι hR) hΦ)
      j hj =
      pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,EuclideanSpace ℂ (Fin b)) L
        (Subtype.val : Y P R ι hι hR T z → SphereBundleTotal P.tangent)
        C.inclusion_holomorphic := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞
    (Y P R ι hι hR T z) := C.manifold
  letI := charts P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  letI := complexManifold P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  let j := (biholomorph P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A).symm ∘
    inclusionIntoConnectedKernelComponent P.tangent T μ
      (c P R ι hι hR z)
  let hj := (torusToIntrinsic_holomorphic_injective
    P R ι hι hR hSmooth hInj T μ z hRange hQ
    DP DR hTot A B H C hLee).1
  let hΦ := ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
    P R ι hSmooth hι hR DP DR hTot A B
  have hEq := sphereTotalMap_comp_torusToIntrinsic_eq_inclusion
    P R ι hι hR hSmooth hInj T μ z hRange hQ DR A
  exact pullbackLineCore_comp_congr
    𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ,ComplexTwistorModel m)
    𝓘(ℂ,EuclideanSpace ℂ (Fin b))
    L (Φ P R ι hι hR) hΦ j hj
    (Subtype.val : Y P R ι hι hR T z → SphereBundleTotal P.tangent)
    C.inclusion_holomorphic hEq

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusAmbientRestriction
