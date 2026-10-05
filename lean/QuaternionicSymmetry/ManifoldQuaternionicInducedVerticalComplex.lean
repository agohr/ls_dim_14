import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorDerivative
import QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalAction
import QuaternionicSymmetry.ManifoldTwistorVerticalComplexLine

/-! Complex linearity and injectivity of the actual vertical differential of
an induced quaternionic twistor map. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedVerticalComplex
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorDerivative
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff Matrix
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
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (DP : CompatibleTangentConnection P.tangent)
  (DR : CompatibleTangentConnection R.tangent)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

theorem actualVerticalDerivative_complex
    (z : SphereBundleTotal R.tangent)
    (v : verticalTangentSubmodule R.tangent z) :
    actualVerticalDerivative P R ι hSmooth hι hR z
      (verticalTangentComplex R.tangent DR z v) =
    verticalTangentComplex P.tangent DP (sphereTotalMap P R ι hι hR z)
      (actualVerticalDerivative P R ι hSmooth hι hR z v) := by
  apply (verticalTangentEquiv P.tangent (sphereTotalMap P R ι hι hR z)).injective
  apply Subtype.ext
  have hL := actualVerticalDerivative_coefficient P R ι hSmooth hι hR z
    (verticalTangentComplex R.tangent DR z v)
  have hV := actualVerticalDerivative_coefficient P R ι hSmooth hι hR z v
  rw [hL,
    verticalTangentEquiv_complex R.tangent DR z v,
    verticalTangentEquiv_complex P.tangent DP (sphereTotalMap P R ι hι hR z)
      (actualVerticalDerivative P R ι hSmooth hι hR z v)]
  change coefficientMap P R ι hι hR z.1
      ((coefficientSphereHomeomorph.symm z.2).1 ⨯₃
        (verticalTangentEquiv R.tangent z v).1) =
    (coefficientSphereHomeomorph.symm (sphereTotalMap P R ι hι hR z).2).1 ⨯₃
      (verticalTangentEquiv P.tangent (sphereTotalMap P R ι hι hR z)
        (actualVerticalDerivative P R ι hSmooth hι hR z v)).1
  rw [hV]
  change coefficientMap P R ι hι hR z.1
      ((coefficientSphereHomeomorph.symm z.2).1 ⨯₃
        (verticalTangentEquiv R.tangent z v).1) =
    (coefficientMap P R ι hι hR z.1
      (coefficientSphereHomeomorph.symm z.2).1) ⨯₃
      (coefficientMap P R ι hι hR z.1
        (verticalTangentEquiv R.tangent z v).1)
  exact coefficientMap_cross P R ι hι hR z.1 _ _

def actualVerticalDerivativeComplex
    (z : SphereBundleTotal R.tangent) :
    letI := verticalComplexModule R.tangent DR z
    letI := verticalComplexModule P.tangent DP (sphereTotalMap P R ι hι hR z)
    verticalTangentSubmodule R.tangent z →ₗ[ℂ]
      verticalTangentSubmodule P.tangent (sphereTotalMap P R ι hι hR z) := by
  letI := verticalComplexModule R.tangent DR z
  letI := verticalComplexModule P.tangent DP (sphereTotalMap P R ι hι hR z)
  exact {
    actualVerticalDerivative P R ι hSmooth hι hR z with
    map_smul' := by
      intro c v
      change actualVerticalDerivative P R ι hSmooth hι hR z
          (verticalComplexSmul R.tangent DR z c v) =
        verticalComplexSmul P.tangent DP (sphereTotalMap P R ι hι hR z) c
          (actualVerticalDerivative P R ι hSmooth hι hR z v)
      simp only [verticalComplexSmul, map_add, map_smul,
        actualVerticalDerivative_complex P R ι hSmooth hι hR DP DR z v]
  }

theorem actualVerticalDerivative_injective (z : SphereBundleTotal R.tangent) :
    Function.Injective (actualVerticalDerivative P R ι hSmooth hι hR z) := by
  intro u v h
  apply (verticalTangentEquiv R.tangent z).injective
  apply Subtype.ext
  have hu := actualVerticalDerivative_coefficient P R ι hSmooth hι hR z u
  have hv := actualVerticalDerivative_coefficient P R ι hSmooth hι hR z v
  rw [h] at hu
  have hc : coefficientMap P R ι hι hR z.1
      ((verticalTangentEquiv R.tangent z u).1) =
      coefficientMap P R ι hι hR z.1
        ((verticalTangentEquiv R.tangent z v).1) := hu.symm.trans hv
  exact coefficientMap_injective P R ι hι hR z.1 hc

include hSmooth in
/-- The actual induced twistor map is an immersion: its rectangular base
derivative and its two-dimensional vertical block are both injective. -/
theorem sphereTotalMap_mfderiv_injective (z : SphereBundleTotal R.tangent) :
    Function.Injective (mfderiv (𝓘(ℝ,F).prod (𝓡 2))
      (𝓘(ℝ,E).prod (𝓡 2)) (sphereTotalMap P R ι hι hR) z) := by
  let L := mfderiv (𝓘(ℝ,F).prod (𝓡 2))
    (𝓘(ℝ,E).prod (𝓡 2)) (sphereTotalMap P R ι hι hR) z
  intro u v huv
  have hbase : u.1 = v.1 := hι z.1 (by
    rw [← sphereTotalMap_mfderiv_fst P R ι hSmooth hι hR z u,
      ← sphereTotalMap_mfderiv_fst P R ι hSmooth hι hR z v]
    exact congrArg Prod.fst huv)
  have hdiff : L (u-v) = 0 := by rw [map_sub, huv, sub_self]
  have hmem : u-v ∈ verticalTangentSubmodule R.tangent z := by
    rw [mem_verticalTangentSubmodule_iff]
    exact sub_eq_zero.mpr hbase
  have hv : actualVerticalDerivative P R ι hSmooth hι hR z
      (⟨u-v,hmem⟩ : verticalTangentSubmodule R.tangent z) = 0 := by
    apply Subtype.ext
    exact hdiff
  have h0 : actualVerticalDerivative P R ι hSmooth hι hR z
      (⟨u-v,hmem⟩ : verticalTangentSubmodule R.tangent z) =
      actualVerticalDerivative P R ι hSmooth hι hR z 0 := by
    simpa using hv
  have hw := (actualVerticalDerivative_injective P R ι hSmooth hι hR z) h0
  exact sub_eq_zero.mp (congrArg Subtype.val hw)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedVerticalComplex
