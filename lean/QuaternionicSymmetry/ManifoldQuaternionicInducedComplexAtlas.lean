import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorComplex
import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

/-! Holomorphicity of the actual induced twistor immersion in independently
supplied compatible complex atlases of possibly different dimensions. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedComplexAtlas
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorSmooth
open ManifoldQuaternionicInducedTwistorComplex
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
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

include hSmooth in
theorem sphereTotalMap_realSmooth_in_compatibleAtlases
    {m n : ℕ} (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n) :
    letI := A.charts
    letI := B.charts
    ContMDiff 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n) ∞
      (sphereTotalMap P R ι hι hR) := by
  letI := A.charts
  letI := B.charts
  exact B.smoothFromExisting.comp
    ((sphereTotalMap_contMDiff P R ι hSmooth hι hR).comp
      A.smoothToExisting)

private def complexifyCommutingMap {m n : ℕ}
    (L : ComplexTwistorModel m →L[ℝ] ComplexTwistorModel n)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    ComplexTwistorModel m →L[ℂ] ComplexTwistorModel n where
  toFun := L
  map_add' := L.map_add
  map_smul' := by
    intro c v
    change L (c • v) = c • L v
    conv_lhs => rw [← Complex.re_add_im c]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [add_smul, L.map_add, mul_smul, Complex.coe_smul,
      L.map_smul, hI]
  cont := L.continuous

private theorem complexifyCommutingMap_restrictScalars {m n : ℕ}
    (L : ComplexTwistorModel m →L[ℝ] ComplexTwistorModel n)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    (complexifyCommutingMap L hI).restrictScalars ℝ = L := by
  ext v
  rfl

include hSmooth hTot in
theorem sphereTotalMap_atlas_mfderiv_i
    {m n : ℕ} (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (z : SphereBundleTotal R.tangent)
    (v : ComplexTwistorModel m) :
    letI := A.charts
    letI := B.charts
    mfderiv 𝓘(ℝ,ComplexTwistorModel m) 𝓘(ℝ,ComplexTwistorModel n)
      (sphereTotalMap P R ι hι hR) z (Complex.I • v) =
    Complex.I •
      (show ComplexTwistorModel n from
        mfderiv 𝓘(ℝ,ComplexTwistorModel m)
          𝓘(ℝ,ComplexTwistorModel n)
          (sphereTotalMap P R ι hι hR) z v) := by
  letI := A.charts
  letI := B.charts
  let w := sphereTotalMap P R ι hι hR z
  let T (x : SphereBundleTotal R.tangent) :=
    mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JF (F := F))
      (id : SphereBundleTotal R.tangent → SphereBundleTotal R.tangent) x
  let T' (x : SphereBundleTotal P.tangent) :=
    mfderiv 𝓘(ℝ,ComplexTwistorModel n) (JE (E := E))
      (id : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) x
  let U' (x : SphereBundleTotal P.tangent) :=
    mfderiv (JE (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
      (id : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) x
  let L := mfderiv 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap P R ι hι hR) z
  let H := mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z
  have hT : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel m) (JF (F := F))
      (id : SphereBundleTotal R.tangent → SphereBundleTotal R.tangent) z :=
    A.smoothToExisting.mdifferentiable (by simp) z
  have hT' : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n) (JE (E := E))
      (id : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) w :=
    B.smoothToExisting.mdifferentiable (by simp) w
  have hU' : MDifferentiableAt (JE (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
      (id : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) w :=
    B.smoothFromExisting.mdifferentiable (by simp) w
  have hL : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap P R ι hι hR) z :=
    (sphereTotalMap_realSmooth_in_compatibleAtlases
      P R ι hSmooth hι hR DP DR A B).mdifferentiable (by simp) z
  have hH : MDifferentiableAt (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z :=
    (sphereTotalMap_contMDiff P R ι hSmooth hι hR).mdifferentiable
      (by simp) z
  have hUT := mfderiv_comp w hU' hT'
  change mfderiv 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) id w =
      (U' w).comp (T' w) at hUT
  rw [mfderiv_id] at hUT
  have hTin : Function.Injective (T' w) := by
    intro a b hab
    have hh := congrArg (U' w) hab
    have ha := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
        ComplexTwistorModel n => K a) hUT
    have hb := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
        ComplexTwistorModel n => K b) hUT
    change a = U' w (T' w a) at ha
    change b = U' w (T' w b) at hb
    exact ha.trans (hh.trans hb.symm)
  have h₁ := mfderiv_comp z hT' hL
  have h₂ := mfderiv_comp z hH hT
  have hnat : (T' w).comp L = H.comp (T z) := by
    change mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JE (E := E))
        (id ∘ sphereTotalMap P R ι hι hR) z =
      (T' w).comp L at h₁
    change mfderiv 𝓘(ℝ,ComplexTwistorModel m) (JE (E := E))
        (sphereTotalMap P R ι hι hR ∘ id) z = H.comp (T z) at h₂
    exact h₁.symm.trans h₂
  apply hTin
  calc
    T' w (L (Complex.I • v)) = H (T z (Complex.I • v)) := by
      exact congrArg (fun K : ComplexTwistorModel m →L[ℝ]
        TangentSpace (JE (E := E)) w => K (Complex.I • v)) hnat
    _ = H (tangentComplex R.tangent DR z (T z v)) :=
      congrArg H (A.tangentI z v)
    _ = tangentComplex P.tangent DP w (H (T z v)) :=
      sphereTotalMap_mfderiv_intertwines_tangentComplex
        P R ι hSmooth hι hR DP DR hTot z (T z v)
    _ = tangentComplex P.tangent DP w (T' w (L v)) := by
      have hv := congrArg (fun K : ComplexTwistorModel m →L[ℝ]
          TangentSpace (JE (E := E)) w => K v) hnat
      change T' w (L v) = H (T z v) at hv
      exact congrArg (tangentComplex P.tangent DP w) hv.symm
    _ = T' w (Complex.I • (show ComplexTwistorModel n from L v)) :=
      (B.tangentI w (L v)).symm

private theorem writtenInExtChartAt_real_eq_complex
    {m n : ℕ} (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (f : SphereBundleTotal R.tangent → SphereBundleTotal P.tangent)
    (z : SphereBundleTotal R.tangent) :
    letI := A.charts
    letI := B.charts
    writtenInExtChartAt 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n) z f =
    writtenInExtChartAt 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,ComplexTwistorModel n) z f := by
  letI := A.charts
  letI := B.charts
  rfl

include hSmooth hTot in
theorem sphereTotalMap_mdifferentiable_complex
    {m n : ℕ} (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n) :
    letI := A.charts
    letI := B.charts
    MDifferentiable 𝓘(ℂ,ComplexTwistorModel m)
      𝓘(ℂ,ComplexTwistorModel n)
      (sphereTotalMap P R ι hι hR) := by
  letI := A.charts
  letI := B.charts
  intro z
  let g := writtenInExtChartAt 𝓘(ℝ,ComplexTwistorModel m)
    𝓘(ℝ,ComplexTwistorModel n) z (sphereTotalMap P R ι hι hR)
  let c := (extChartAt 𝓘(ℝ,ComplexTwistorModel m) z) z
  have hReal : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel m)
      𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap P R ι hι hR) z :=
    (sphereTotalMap_realSmooth_in_compatibleAtlases
      P R ι hSmooth hι hR DP DR A B).mdifferentiable (by simp) z
  have hDiffReal : DifferentiableAt ℝ g c := by
    simpa [g, c, modelWithCornersSelf_coe, differentiableWithinAt_univ]
      using hReal.differentiableWithinAt_writtenInExtChartAt
  have hDeriv : fderiv ℝ g c =
      mfderiv 𝓘(ℝ,ComplexTwistorModel m)
        𝓘(ℝ,ComplexTwistorModel n)
        (sphereTotalMap P R ι hι hR) z := by
    simpa [g, c, modelWithCornersSelf_coe, fderivWithin_univ]
      using hReal.mfderiv.symm
  have hI (v : ComplexTwistorModel m) :
      fderiv ℝ g c (Complex.I • v) = Complex.I • fderiv ℝ g c v := by
    rw [hDeriv]
    exact sphereTotalMap_atlas_mfderiv_i
      P R ι hSmooth hι hR DP DR hTot A B z v
  have hDiffComplex : DifferentiableAt ℂ g c :=
    (differentiableAt_iff_restrictScalars ℝ hDiffReal).2
      ⟨complexifyCommutingMap (fderiv ℝ g c) hI,
        complexifyCommutingMap_restrictScalars (fderiv ℝ g c) hI⟩
  apply (mdifferentiableAt_iff
    (I := 𝓘(ℂ,ComplexTwistorModel m))
    (I' := 𝓘(ℂ,ComplexTwistorModel n))
    (sphereTotalMap P R ι hι hR) z).2
  constructor
  · exact hReal.continuousAt
  · simpa [g, c, writtenInExtChartAt_real_eq_complex
      P R ι DP DR A B, modelWithCornersSelf_coe,
      differentiableWithinAt_univ] using hDiffComplex

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedComplexAtlas
