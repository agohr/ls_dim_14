import QuaternionicSymmetry.HomeomorphTransportedManifold
import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorFixedComponent
import QuaternionicSymmetry.ManifoldQuaternionicInducedComplexInfinity
import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

/-! The actual lifted fixed component carries the intrinsic complex atlas,
transported along its proven homeomorphism. The subset keeps its inherited
topology; its embedding into the ambient twistor space is the actual induced
twistor map. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFixedComponentComplexAtlas

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorFixedComponent
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorLiftedFixedSet
open Topology
open scoped Manifold ContDiff

noncomputable section

variable {E F M N : Type*}
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

private abbrev fixedLiftedComponent :=
  ↥(connectedComponentIn (fixedSpherePoints P.tangent S)
    (sphereTotalMap P R ι hι hR z))

include hSmooth hInj hRange hQ in
/-- A complex atlas on the actual fixed-component subtype, with its
already inherited topology. No new fixed-set complex structure is assumed. -/
def charts {m : ℕ}
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (A : CompatibleComplexAtlas R.tangent DR m) :
    ChartedSpace (ComplexTwistorModel m)
      (fixedLiftedComponent P R ι hι hR S z) := by
  letI := A.charts
  exact HomeomorphTransportedManifold.chartedSpace
    (H := ComplexTwistorModel m)
    (fixedComponentHomeomorph P R ι hι hR hSmooth hInj S z hRange hQ)

include hSmooth hInj hRange hQ in
theorem complexManifold {m : ℕ}
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (A : CompatibleComplexAtlas R.tangent DR m) :
    letI := charts P R ι hι hR hSmooth hInj S z hRange hQ DR A
    IsManifold 𝓘(ℂ,ComplexTwistorModel m) ∞
      (fixedLiftedComponent P R ι hι hR S z) := by
  letI := A.charts
  letI := A.complexManifold
  exact HomeomorphTransportedManifold.isManifold
    𝓘(ℂ,ComplexTwistorModel m) ∞
    (fixedComponentHomeomorph P R ι hι hR hSmooth hInj S z hRange hQ)

include hSmooth hInj hRange hQ in
/-- The transported complex atlas is also a real smooth atlas. -/
theorem realManifold {m : ℕ}
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (A : CompatibleComplexAtlas R.tangent DR m) :
    letI := charts P R ι hι hR hSmooth hInj S z hRange hQ DR A
    IsManifold 𝓘(ℝ,ComplexTwistorModel m) ∞
      (fixedLiftedComponent P R ι hι hR S z) := by
  letI := A.charts
  letI := A.realManifold
  exact HomeomorphTransportedManifold.isManifold
    𝓘(ℝ,ComplexTwistorModel m) ∞
    (fixedComponentHomeomorph P R ι hι hR hSmooth hInj S z hRange hQ)

include hSmooth hInj hRange hQ in
/-- The proven topological identification is a genuine biholomorphism
for the transported complex atlas. -/
def biholomorph {m : ℕ}
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (A : CompatibleComplexAtlas R.tangent DR m) :
    letI := A.charts
    letI := A.complexManifold
    letI := charts P R ι hι hR hSmooth hInj S z hRange hQ DR A
    letI := complexManifold P R ι hι hR hSmooth hInj S z hRange hQ DR A
    SphereBundleTotal R.tangent ≃ₘ⟮𝓘(ℂ,ComplexTwistorModel m),
      𝓘(ℂ,ComplexTwistorModel m)⟯
      (fixedLiftedComponent P R ι hι hR S z) := by
  letI := A.charts
  letI := A.complexManifold
  exact HomeomorphTransportedManifold.diffeomorph
    (fixedComponentHomeomorph P R ι hι hR hSmooth hInj S z hRange hQ)

include hSmooth hInj hRange hQ in
theorem biholomorph_apply {m : ℕ}
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (A : CompatibleComplexAtlas R.tangent DR m)
    (w : SphereBundleTotal R.tangent) :
    ((biholomorph P R ι hι hR hSmooth hInj S z hRange hQ DR A w).1 :
      SphereBundleTotal P.tangent) = sphereTotalMap P R ι hι hR w :=
  fixedComponentHomeomorph_apply P R ι hι hR hSmooth hInj S z hRange hQ w

include hSmooth hInj hRange hQ in
/-- The inherited-subtype inclusion is holomorphic because its composite
with the intrinsic biholomorphism is exactly the existing holomorphic
induced twistor immersion. -/
theorem inclusion_contMDiff {m n : ℕ}
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic P R ι DP DR)
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n) :
    letI := A.charts
    letI := B.charts
    letI := charts P R ι hι hR hSmooth hInj S z hRange hQ DR A
    letI := complexManifold P R ι hι hR hSmooth hInj S z hRange hQ DR A
    ContMDiff 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (Subtype.val : fixedLiftedComponent P R ι hι hR S z → SphereBundleTotal P.tangent) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI := charts P R ι hι hR hSmooth hInj S z hRange hQ DR A
  letI := complexManifold P R ι hι hR hSmooth hInj S z hRange hQ DR A
  let Ψ := biholomorph P R ι hι hR hSmooth hInj S z hRange hQ DR A
  have hΦ := ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
    P R ι hSmooth hι hR DP DR hTot A B
  have hcomp : ContMDiff 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun w : fixedLiftedComponent P R ι hι hR S z =>
        sphereTotalMap P R ι hι hR (Ψ.symm w)) :=
    hΦ.comp Ψ.symm.contMDiff
  apply hcomp.congr
  intro w
  change (w : SphereBundleTotal P.tangent) =
    sphereTotalMap P R ι hι hR (Ψ.symm w)
  rw [← biholomorph_apply P R ι hι hR hSmooth hInj S z hRange hQ DR A
    (Ψ.symm w), Ψ.apply_symm_apply]

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedComponentComplexAtlas
