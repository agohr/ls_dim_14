import QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineFiber
import QuaternionicSymmetry.ManifoldQuaternionicInducedComplexInfinity
import QuaternionicSymmetry.ManifoldTwistorContactComplexLinear

/-! Naturality of the actual complex contact form under the holomorphic
induced twistor immersion, obtained by changing atlases in the already
proved real differential/contact identity. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactComplexNaturality
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedContactLineFiber
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
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
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
  (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic P R ι DP DR)

private abbrev JF := 𝓘(ℝ,F).prod (𝓡 2)
private abbrev JE := 𝓘(ℝ,E).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) :=
  ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

include hSmooth hTot in
theorem contactLineFiberEquiv_contactFormComplex {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LR : HolomorphicContactLine R.tangent DR m A)
    (LP : HolomorphicContactLine P.tangent DP n B)
    (z : SphereBundleTotal R.tangent)
    (v : ComplexTwistorModel m) :
    letI := A.charts
    letI := B.charts
    LP.contactFormComplex P.tangent DP
      (sphereTotalMap P R ι hι hR z)
      (mfderiv 𝓘(ℂ,ComplexTwistorModel m)
        𝓘(ℂ,ComplexTwistorModel n)
        (sphereTotalMap P R ι hι hR) z v) =
      contactLineFiberEquivInduced P R ι hSmooth hι hR DP DR A B LR LP z
        (LR.contactFormComplex R.tangent DR z v) := by
  letI := A.charts
  letI := B.charts
  let w := sphereTotalMap P R ι hι hR z
  let T := mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JF (F := F))
    (id : SphereBundleTotal R.tangent → SphereBundleTotal R.tangent) z
  let T' := mfderiv 𝓘(ℝ,ComplexTwistorModel n) (JE (E := E))
    (id : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) w
  let L := mfderiv 𝓘(ℝ,ComplexTwistorModel m) 𝓘(ℝ,ComplexTwistorModel n)
    (sphereTotalMap P R ι hι hR) z
  let LC := mfderiv 𝓘(ℂ,ComplexTwistorModel m) 𝓘(ℂ,ComplexTwistorModel n)
    (sphereTotalMap P R ι hι hR) z
  let H := mfderiv (JF (F := F)) (JE (E := E))
    (sphereTotalMap P R ι hι hR) z
  have hT : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel m) (JF (F := F))
      (id : SphereBundleTotal R.tangent → SphereBundleTotal R.tangent) z :=
    A.smoothToExisting.mdifferentiable (by simp) z
  have hT' : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n) (JE (E := E))
      (id : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) w :=
    B.smoothToExisting.mdifferentiable (by simp) w
  have hL : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n)
      (sphereTotalMap P R ι hι hR) z :=
    (ManifoldQuaternionicInducedComplexAtlas.sphereTotalMap_realSmooth_in_compatibleAtlases
      P R ι hSmooth hι hR DP DR A B).mdifferentiable (by simp) z
  have hH : MDifferentiableAt (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z :=
    (ManifoldQuaternionicInducedTwistorSmooth.sphereTotalMap_contMDiff
      P R ι hSmooth hι hR).mdifferentiable (by simp) z
  have hLC : MDifferentiableAt 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,ComplexTwistorModel n)
      (sphereTotalMap P R ι hι hR) z :=
    ManifoldQuaternionicInducedComplexAtlas.sphereTotalMap_mdifferentiable_complex
      P R ι hSmooth hι hR DP DR hTot A B z
  have hsame : L = LC.restrictScalars ℝ := by
    rw [show L = _ from hL.mfderiv, show LC = _ from hLC.mfderiv]
    simp only [modelWithCornersSelf_coe]
    -- The two self-model charts are definitionally the same, and a complex
    -- derivative becomes the real derivative by scalar restriction.
    rw [show writtenInExtChartAt 𝓘(ℝ,ComplexTwistorModel m)
        𝓘(ℝ,ComplexTwistorModel n) z
        (sphereTotalMap P R ι hι hR) =
      writtenInExtChartAt 𝓘(ℂ,ComplexTwistorModel m)
        𝓘(ℂ,ComplexTwistorModel n) z
        (sphereTotalMap P R ι hι hR) from rfl]
    simp only [Set.range_id, fderivWithin_univ]
    have hc : DifferentiableAt ℂ
        (writtenInExtChartAt 𝓘(ℂ,ComplexTwistorModel m)
          𝓘(ℂ,ComplexTwistorModel n) z
          (sphereTotalMap P R ι hι hR))
        ((extChartAt 𝓘(ℂ,ComplexTwistorModel m) z) z) := by
      simpa [modelWithCornersSelf_coe, Set.range_id,
        differentiableWithinAt_univ] using
        hLC.differentiableWithinAt_writtenInExtChartAt
    exact hc.fderiv_restrictScalars ℝ
  have h₁ := mfderiv_comp z hT' hL
  have h₂ := mfderiv_comp z hH hT
  have hnat : T' ∘L L = H ∘L T := by
    change mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JE (E := E))
        (id ∘ sphereTotalMap P R ι hι hR) z = T' ∘L L at h₁
    change mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JE (E := E))
        (sphereTotalMap P R ι hι hR ∘ id) z = H ∘L T at h₂
    exact h₁.symm.trans h₂
  have hv := congrArg (fun K : ComplexTwistorModel m →L[ℝ]
      TangentSpace (JE (E := E)) w => K v) hnat
  change T' (L v) = H (T v) at hv
  change LP.contactFormReal P.tangent DP w (T' (LC v)) =
    contactLineFiberEquivInduced P R ι hSmooth hι hR DP DR A B LR LP z
      (LR.contactFormReal R.tangent DR z (T v))
  have hvalue := congrArg
    (fun K : ComplexTwistorModel m →L[ℝ] ComplexTwistorModel n => K v) hsame
  change L v = LC v at hvalue
  rw [← hvalue]
  rw [hv]
  exact contactLineFiberEquiv_contactFormReal
    P R ι hSmooth hι hR DP DR A B LR LP hTot z (T v)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactComplexNaturality
