import QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization
import QuaternionicSymmetry.ManifoldQuaternionicFixedComponentComplexImmersion
import QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent

/-! Holomorphicity of the actual nested full-torus component inside the
connected kernel component, and then inside the intrinsic smaller twistor.
The torus component may be a proper subset of the latter. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusToIntrinsicHolomorphic

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorFixedComponent
open ManifoldQuaternionicFixedComponentComplexAtlas
open ManifoldQuaternionicFixedComponentComplexImmersion
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldComplexHolomorphicFactorization
open ManifoldQuaternionicTorusAction
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldRiemannianFixedComponentGenericInput
open QuaternionicSymmetry.GeneralSmoothMapSource
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
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
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
    (fixedPoints P.tangent (T.connectedKernelImage P.tangent μ)) (ι z.1))
  (hQ : ∀ x ∈ Set.range ι, ∀ f ∈ T.connectedKernelImage P.tangent μ,
    ∀ a : Fin 3 → ℝ, coefficientAction P.tangent f x a = a)

private abbrev c := sphereTotalMap P R ι hι hR z
private abbrev Y := ManifoldQuaternionicTorusFixedComplexComponent.component
  P.tangent T (c P R ι hι hR z)
private abbrev K := ↥(connectedComponentIn
  (fixedSpherePoints P.tangent (T.connectedKernelImage P.tangent μ))
  (c P R ι hι hR z))

include hSmooth hInj hRange hQ in
/-- The literal inclusion `Y ↪ K` is holomorphic for the independently
constructed full-torus atlas and the transported intrinsic kernel atlas. -/
theorem torusToKernel_holomorphic {a m n : ℕ}
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P R ι DP DR)
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (H : FixedComponentAtlas
      (𝓘(ℝ,E).prod (𝓡 2))
      (liftedSet P.tangent T.imageSubgroup)
      (c P R ι hι hR z) a)
    {b : ℕ}
    (C : letI := B.charts
      ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas P.tangent DP B T.imageSubgroup H) b)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := A.charts
    letI := B.charts
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      (Y P R ι hι hR T z) := C.charts
    letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
      P R ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
    ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
      𝓘(ℂ,ComplexTwistorModel m) ∞
      (inclusionIntoConnectedKernelComponent P.tangent T μ
        (c P R ι hι hR z) :
          ↥(connectedComponentIn
            (fixedSpherePoints P.tangent T.imageSubgroup)
            (c P R ι hι hR z)) →
          K P R ι hι hR T μ z) := by
  letI := A.charts
  letI := B.charts
  letI := A.realManifold
  letI := B.realManifold
  letI := A.complexManifold
  letI := B.complexManifold
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  letI : IsManifold 𝓘(ℝ,EuclideanSpace ℂ (Fin b)) ∞
    (Y P R ι hι hR T z) := C.realManifold
  letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞
    (Y P R ι hι hR T z) := C.manifold
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
    P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.realManifold
    P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.complexManifold
    P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  let f := inclusionIntoConnectedKernelComponent P.tangent T μ
    (c P R ι hι hR z)
  have hιK := ManifoldQuaternionicFixedComponentComplexAtlas.inclusion_contMDiff
    P R ι hι hR hSmooth hInj (T.connectedKernelImage P.tangent μ)
    z hRange hQ DP DR hTot A B
  have hdf := ManifoldQuaternionicFixedComponentComplexImmersion.inclusion_injective_derivative
    P R ι hι hR hSmooth hInj (T.connectedKernelImage P.tangent μ)
    z hRange hQ DP DR A B
  have hcomp : ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      ((Subtype.val : K P R ι hι hR T μ z → SphereBundleTotal P.tangent) ∘ f) := by
    convert C.inclusion_holomorphic using 1
  exact holomorphic_of_embedded_holomorphic_composite hLee
    (Subtype.val : K P R ι hι hR T μ z → SphereBundleTotal P.tangent)
    f Topology.IsEmbedding.subtypeVal hιK hdf hcomp

include hSmooth hInj hRange hQ in
/-- The actual full-torus component maps holomorphically and injectively
to the smaller intrinsic twistor, through the connected kernel component.
It is not asserted to be all of that twistor. -/
theorem torusToIntrinsic_holomorphic_injective {a m n : ℕ}
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P R ι DP DR)
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (H : FixedComponentAtlas
      (𝓘(ℝ,E).prod (𝓡 2))
      (liftedSet P.tangent T.imageSubgroup)
      (c P R ι hι hR z) a)
    {b : ℕ}
    (C : letI := B.charts
      ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas P.tangent DP B T.imageSubgroup H) b)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := A.charts
    letI := B.charts
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      (Y P R ι hι hR T z) := C.charts
    letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
      P R ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
    let f := (ManifoldQuaternionicFixedComponentComplexAtlas.biholomorph
      P R ι hι hR hSmooth hInj
      (T.connectedKernelImage P.tangent μ) z hRange hQ DR A).symm ∘
      inclusionIntoConnectedKernelComponent P.tangent T μ
        (c P R ι hι hR z)
    ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin b))
      𝓘(ℂ,ComplexTwistorModel m) ∞ f ∧ Function.Injective f := by
  letI := A.charts
  letI := B.charts
  letI := A.realManifold
  letI := B.realManifold
  letI := A.complexManifold
  letI := B.complexManifold
  letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
    (Y P R ι hι hR T z) := C.charts
  letI : IsManifold 𝓘(ℝ,EuclideanSpace ℂ (Fin b)) ∞
    (Y P R ι hι hR T z) := C.realManifold
  letI : IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin b)) ∞
    (Y P R ι hι hR T z) := C.manifold
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.charts
    P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  letI := ManifoldQuaternionicFixedComponentComplexAtlas.complexManifold
    P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  let Ψ := ManifoldQuaternionicFixedComponentComplexAtlas.biholomorph
    P R ι hι hR hSmooth hInj
    (T.connectedKernelImage P.tangent μ) z hRange hQ DR A
  let j := inclusionIntoConnectedKernelComponent P.tangent T μ
    (c P R ι hι hR z)
  constructor
  · exact Ψ.symm.contMDiff.comp
      (torusToKernel_holomorphic P R ι hι hR hSmooth hInj T μ z
        hRange hQ DP DR hTot A B H C hLee)
  · exact Ψ.symm.injective.comp
      (Set.inclusion_injective
        (component_subset_connectedKernelComponent P.tangent T μ
          (c P R ι hι hR z)))

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusToIntrinsicHolomorphic
