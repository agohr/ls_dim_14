import QuaternionicSymmetry.ManifoldQuaternionicInducedComplexAtlas
import QuaternionicSymmetry.ManifoldQuaternionicInducedVerticalComplex
import QuaternionicSymmetry.ManifoldQuaternionicTwistorComplexFixedAtlas

/-! Injectivity of the genuine induced twistor derivative in the compatible
real reductions of both complex atlases. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicInducedComplexImmersion

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorSmooth
open ManifoldQuaternionicInducedVerticalComplex
open ManifoldQuaternionicInducedComplexAtlas
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)

private abbrev JF := 𝓘(ℝ,F).prod (𝓡 2)
private abbrev JE := 𝓘(ℝ,E).prod (𝓡 2)

include hSmooth in
theorem sphereTotalMap_mfderiv_injective_compatible {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (z : SphereBundleTotal R.tangent) :
    letI := A.charts
    letI := B.charts
    Function.Injective (mfderiv 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n)
      (sphereTotalMap P R ι hι hR) z) := by
  letI := A.charts
  letI := B.charts
  letI := A.realManifold
  letI := B.realManifold
  let Φ := sphereTotalMap P R ι hι hR
  let w := Φ z
  let T := mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JF (F := F))
    (id : SphereBundleTotal R.tangent → SphereBundleTotal R.tangent) z
  let U := mfderiv 𝓘(ℝ,ComplexTwistorModel n) (JE (E := E))
    (id : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) w
  have hL := (sphereTotalMap_realSmooth_in_compatibleAtlases
    P R ι hSmooth hι hR DP DR A B).mdifferentiableAt (by simp) (x := z)
  have hH := (sphereTotalMap_contMDiff P R ι hSmooth hι hR).mdifferentiableAt
    (by simp) (x := z)
  have hT := A.smoothToExisting.mdifferentiableAt (by simp) (x := z)
  have hU := B.smoothToExisting.mdifferentiableAt (by simp) (x := w)
  have h₁ := mfderiv_comp z hU hL
  have h₂ := mfderiv_comp z hH hT
  have hnat : U.comp (mfderiv 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n) Φ z) =
      (mfderiv (JF (F := F)) (JE (E := E)) Φ z).comp T := by
    change mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JE (E := E))
        (id ∘ Φ) z = U.comp _ at h₁
    change mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JE (E := E))
        (Φ ∘ id) z =
        (mfderiv (JF (F := F)) (JE (E := E)) Φ z).comp T at h₂
    exact h₁.symm.trans h₂
  intro u v huv
  have hTin : Function.Injective T :=
    (atlasTangentEquiv R.tangent DR A z).injective
  apply hTin
  apply sphereTotalMap_mfderiv_injective P R ι hSmooth hι hR z
  have hu := congrArg (fun L : ComplexTwistorModel m →L[ℝ]
    E × EuclideanSpace ℝ (Fin 2) => L u) hnat
  have hv := congrArg (fun L : ComplexTwistorModel m →L[ℝ]
    E × EuclideanSpace ℝ (Fin 2) => L v) hnat
  exact hu.symm.trans ((congrArg U huv).trans hv)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedComplexImmersion
