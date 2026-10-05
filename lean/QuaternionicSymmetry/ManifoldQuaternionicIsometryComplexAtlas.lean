import QuaternionicSymmetry.ManifoldQuaternionicIsometryTwistorComplex
import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

/-! Transport of the actual smooth isometry lift into an externally supplied
integrable complex atlas compatible with the checked twistor almost-complex
field. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexAtlas

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorLiftSmooth
open ManifoldQuaternionicIsometryTwistorComplex
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

/-- The actual lift is smooth in any compatible complex atlas when viewed
as a real manifold, by the explicitly supplied two-way smooth atlas
comparison. -/
theorem sphereTotalMap_realSmooth_in_compatibleAtlas
    {n : ℕ} (A : CompatibleComplexAtlas Q D n)
    (f : QuaternionicIsometries Q) :
    letI := A.charts
    ContMDiff 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) ∞ (sphereTotalMap Q f) := by
  letI := A.charts
  exact A.smoothFromExisting.comp
    ((sphereTotalMap_contMDiff Q f).comp A.smoothToExisting)

private theorem writtenInExtChartAt_real_eq_complex
    {n : ℕ} (A : CompatibleComplexAtlas Q D n)
    (f : SphereBundleTotal Q → SphereBundleTotal Q)
    (z : SphereBundleTotal Q) :
    letI := A.charts
    writtenInExtChartAt 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) z f =
    writtenInExtChartAt 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n) z f := by
  letI := A.charts
  rfl

/-- A bounded real-linear map commuting with the complex structure is
complex-linear. Kept local to avoid imposing a stronger global API. -/
private def complexifyCommutingMap {n : ℕ}
    (L : ComplexTwistorModel n →L[ℝ] ComplexTwistorModel n)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    ComplexTwistorModel n →L[ℂ] ComplexTwistorModel n where
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

private theorem complexifyCommutingMap_restrictScalars {n : ℕ}
    (L : ComplexTwistorModel n →L[ℝ] ComplexTwistorModel n)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    (complexifyCommutingMap L hI).restrictScalars ℝ = L := by
  ext v
  rfl

/-- In the compatible complex atlas, the actual lift's real differential
commutes with multiplication by `i`. This transports the independently
proved twistor-complex intertwining through the supplied atlas comparison. -/
theorem sphereTotalMap_atlas_mfderiv_i
    {n : ℕ} (A : CompatibleComplexAtlas Q D n)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : ComplexTwistorModel n) :
    letI := A.charts
    mfderiv 𝓘(ℝ,ComplexTwistorModel n) 𝓘(ℝ,ComplexTwistorModel n)
      (sphereTotalMap Q f) z (Complex.I • v) =
    Complex.I •
      (show ComplexTwistorModel n from
        mfderiv 𝓘(ℝ,ComplexTwistorModel n)
          𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap Q f) z v) := by
  letI := A.charts
  let w := sphereTotalMap Q f z
  let T (x : SphereBundleTotal Q) :=
    mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
      (id : SphereBundleTotal Q → SphereBundleTotal Q) x
  let U (x : SphereBundleTotal Q) :=
    mfderiv (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
      (id : SphereBundleTotal Q → SphereBundleTotal Q) x
  let L := mfderiv 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap Q f) z
  let H := mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z
  have hT (x : SphereBundleTotal Q) :
      MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
        (id : SphereBundleTotal Q → SphereBundleTotal Q) x :=
    A.smoothToExisting.mdifferentiable (by simp) x
  have hU (x : SphereBundleTotal Q) :
      MDifferentiableAt (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
        (id : SphereBundleTotal Q → SphereBundleTotal Q) x :=
    A.smoothFromExisting.mdifferentiable (by simp) x
  have hL : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap Q f) z :=
    (sphereTotalMap_realSmooth_in_compatibleAtlas Q D A f).mdifferentiable
      (by simp) z
  have hH : MDifferentiableAt (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z :=
    (sphereTotalMap_contMDiff Q f).mdifferentiable (by simp) z
  have hUT := mfderiv_comp w (hU w) (hT w)
  change mfderiv 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) id w =
      (U w).comp (T w) at hUT
  rw [mfderiv_id] at hUT
  have hTin : Function.Injective (T w) := by
    intro a b hab
    have hh := congrArg (U w) hab
    have ha := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
        ComplexTwistorModel n => K a) hUT
    have hb := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
        ComplexTwistorModel n => K b) hUT
    change a = U w (T w a) at ha
    change b = U w (T w b) at hb
    exact ha.trans (hh.trans hb.symm)
  have h₁ := mfderiv_comp z (hT w) hL
  have h₂ := mfderiv_comp z hH (hT z)
  have hnat : (T w).comp L = H.comp (T z) := by
    change mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
        (id ∘ sphereTotalMap Q f) z = (T w).comp L at h₁
    change mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
        (sphereTotalMap Q f ∘ id) z = H.comp (T z) at h₂
    exact h₁.symm.trans h₂
  apply hTin
  calc
    T w (L (Complex.I • v)) = H (T z (Complex.I • v)) := by
      exact congrArg (fun K : ComplexTwistorModel n →L[ℝ]
        TangentSpace (J (E := E)) w => K (Complex.I • v)) hnat
    _ = H (tangentComplex Q D z (T z v)) :=
      congrArg H (A.tangentI z v)
    _ = tangentComplex Q D w (H (T z v)) :=
      sphereTotalMap_mfderiv_intertwines_tangentComplex Q D f z (T z v)
    _ = tangentComplex Q D w (T w (L v)) := by
      have hv := congrArg (fun K : ComplexTwistorModel n →L[ℝ]
          TangentSpace (J (E := E)) w => K v) hnat
      change T w (L v) = H (T z v) at hv
      exact congrArg (tangentComplex Q D w) hv.symm
    _ = T w (Complex.I • (show ComplexTwistorModel n from L v)) :=
      (A.tangentI w (L v)).symm

/-- Every genuine quaternionic isometry acts holomorphically on the twistor
space in any complex atlas whose tangent complex structure is the checked
twistor almost-complex structure. -/
theorem sphereTotalMap_mdifferentiable_complex
    {n : ℕ} (A : CompatibleComplexAtlas Q D n)
    (f : QuaternionicIsometries Q) :
    letI := A.charts
    MDifferentiable 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n) (sphereTotalMap Q f) := by
  letI := A.charts
  intro z
  let g := writtenInExtChartAt 𝓘(ℝ,ComplexTwistorModel n)
    𝓘(ℝ,ComplexTwistorModel n) z (sphereTotalMap Q f)
  let c := (extChartAt 𝓘(ℝ,ComplexTwistorModel n) z) z
  have hReal : MDifferentiableAt 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap Q f) z :=
    (sphereTotalMap_realSmooth_in_compatibleAtlas Q D A f).mdifferentiable
      (by simp) z
  have hDiffReal : DifferentiableAt ℝ g c := by
    simpa [g, c, modelWithCornersSelf_coe, differentiableWithinAt_univ]
      using hReal.differentiableWithinAt_writtenInExtChartAt
  have hDeriv : fderiv ℝ g c =
      mfderiv 𝓘(ℝ,ComplexTwistorModel n)
        𝓘(ℝ,ComplexTwistorModel n) (sphereTotalMap Q f) z := by
    simpa [g, c, modelWithCornersSelf_coe, fderivWithin_univ]
      using hReal.mfderiv.symm
  have hI (v : ComplexTwistorModel n) :
      fderiv ℝ g c (Complex.I • v) = Complex.I • fderiv ℝ g c v := by
    rw [hDeriv]
    exact sphereTotalMap_atlas_mfderiv_i Q D A f z v
  have hDiffComplex : DifferentiableAt ℂ g c :=
    (differentiableAt_iff_restrictScalars ℝ hDiffReal).2
      ⟨complexifyCommutingMap (fderiv ℝ g c) hI,
        complexifyCommutingMap_restrictScalars (fderiv ℝ g c) hI⟩
  apply (mdifferentiableAt_iff
    (I := 𝓘(ℂ,ComplexTwistorModel n))
    (I' := 𝓘(ℂ,ComplexTwistorModel n))
    (sphereTotalMap Q f) z).2
  constructor
  · exact hReal.continuousAt
  · simpa [g, c, writtenInExtChartAt_real_eq_complex Q D A,
      modelWithCornersSelf_coe, differentiableWithinAt_univ]
      using hDiffComplex

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexAtlas
