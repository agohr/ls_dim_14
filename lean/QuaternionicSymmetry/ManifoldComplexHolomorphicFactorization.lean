import QuaternionicSymmetry.GeneralSmoothMapSource
import QuaternionicSymmetry.ComplexSmoothRealInfinity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Holomorphic factorization through an embedded complex submanifold,
using Lee's embedded-codomain smoothness theorem only for the real-smooth
step. -/

namespace QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization

open QuaternionicSymmetry.GeneralSmoothMapSource
open QuaternionicSymmetry.ComplexSmoothRealInfinity
open QuaternionicSymmetry.ComplexSmoothRealDerivativeField
open scoped Manifold ContDiff
noncomputable section

variable {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ,E) ∞ M] [IsManifold 𝓘(ℂ,F) ∞ N]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N]

/-- Complex-C∞ implies real-C∞ for the same complex self-model charts. -/
theorem holomorphic_is_real_smooth {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ∞ f) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f := by
  obtain ⟨hcont, hcharts⟩ := contMDiff_iff.mp hf
  apply contMDiff_iff.mpr
  refine ⟨hcont, ?_⟩
  intro x y
  exact (hcharts x y).restrict_scalars ℝ

/-- A real-smooth map with complex-linear actual derivative is holomorphic.
This is the manifold version of the Cauchy–Riemann criterion in complex
self-model charts. -/
theorem holomorphic_of_real_smooth_and_derivative
    {f : M → N}
    (hreal : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hlin : ∀ x : M, ∀ v : E,
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x (Complex.I • v) =
        Complex.I • (show F from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x v)) :
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ∞ f := by
  have hc : MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) f := by
    intro x
    let g := writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,F) x f
    let c := (extChartAt 𝓘(ℝ,E) x) x
    have hr := hreal.mdifferentiable (by simp) x
    have hdr : DifferentiableAt ℝ g c := by
      simpa [g, c, modelWithCornersSelf_coe, differentiableWithinAt_univ]
        using hr.differentiableWithinAt_writtenInExtChartAt
    have hderiv : fderiv ℝ g c = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x := by
      simpa [g, c, modelWithCornersSelf_coe, fderivWithin_univ]
        using hr.mfderiv.symm
    have hi (v : E) : fderiv ℝ g c (Complex.I • v) =
        Complex.I • fderiv ℝ g c v := by
      rw [hderiv]
      exact hlin x v
    have hdc : DifferentiableAt ℂ g c :=
      (differentiableAt_iff_restrictScalars ℝ hdr).2
        ⟨complexifyCommutingMap (fderiv ℝ g c) hi,
          complexifyCommutingMap_restrictScalars (fderiv ℝ g c) hi⟩
    apply (mdifferentiableAt_iff (I := 𝓘(ℂ,E))
      (I' := 𝓘(ℂ,F)) f x).2
    constructor
    · exact hr.continuousAt
    · simpa [g, c, modelWithCornersSelf_coe,
        differentiableWithinAt_univ] using hdc
  obtain ⟨hcont, hrealCharts⟩ := contMDiff_iff.mp hreal
  obtain ⟨_, hcCharts⟩ := mdifferentiable_iff.mp hc
  apply contMDiff_iff.mpr
  refine ⟨hcont, ?_⟩
  intro x y
  let s : Set E := (extChartAt 𝓘(ℂ,E) x).target ∩
    (extChartAt 𝓘(ℂ,E) x).symm ⁻¹'
      (f ⁻¹' (extChartAt 𝓘(ℂ,F) y).source)
  have hs : IsOpen s := by
    apply (continuousOn_extChartAt_symm (I := 𝓘(ℂ,E)) x).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℂ,E)) x)
    exact (isOpen_extChartAt_source (I := 𝓘(ℂ,F)) y).preimage hcont
  have hrealOn : ContDiffOn ℝ ∞
      (extChartAt 𝓘(ℂ,F) y ∘ f ∘ (extChartAt 𝓘(ℂ,E) x).symm) s := by
    simpa only [s] using hrealCharts x y
  have hcOn : DifferentiableOn ℂ
      (extChartAt 𝓘(ℂ,F) y ∘ f ∘ (extChartAt 𝓘(ℂ,E) x).symm) s := by
    simpa only [s] using hcCharts x y
  exact contDiffOn_infty_of_real_complex hs hrealOn hcOn

/-- The real derivative of a holomorphic map commutes with ambient `i`. -/
theorem real_derivative_commutes_i_of_holomorphic {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ∞ f)
    (x : M) (v : E) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x (Complex.I • v) =
      Complex.I • (show F from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x v) := by
  let g := writtenInExtChartAt 𝓘(ℂ,E) 𝓘(ℂ,F) x f
  let c := (extChartAt 𝓘(ℂ,E) x) x
  have hc := hf.mdifferentiable (by simp) x
  have hcr : DifferentiableAt ℂ g c := by
    simpa [g, c, modelWithCornersSelf_coe, differentiableWithinAt_univ]
      using hc.differentiableWithinAt_writtenInExtChartAt
  have hr := (holomorphic_is_real_smooth hf).mdifferentiable (by simp) x
  have hderiv : fderiv ℝ g c = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x := by
    simpa [g, c, modelWithCornersSelf_coe, fderivWithin_univ]
      using hr.mfderiv.symm
  rw [← hderiv]
  rw [hcr.fderiv_restrictScalars ℝ]
  exact map_smul (fderiv ℂ g c) Complex.I v

variable {V P : Type}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace P] [ChartedSpace V P]
  [IsManifold 𝓘(ℂ,V) ∞ P] [IsManifold 𝓘(ℝ,V) ∞ P]

/-- Holomorphicity descends through an actual embedded holomorphic
immersion. Lee's theorem supplies the real smoothness of the factored map;
complex linearity then follows by cancelling the injective ambient
derivative. -/
theorem holomorphic_of_embedded_holomorphic_composite
    [T2Space M] [SecondCountableTopology M]
    [T2Space N] [SecondCountableTopology N]
    [T2Space P] [SecondCountableTopology P]
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (ι : N → P) (f : M → N)
    (hemb : Topology.IsEmbedding ι)
    (hι : ContMDiff 𝓘(ℂ,F) 𝓘(ℂ,V) ∞ ι)
    (hιinj : ∀ y : N,
      Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ι y))
    (hcomp : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,V) ∞ (ι ∘ f)) :
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ∞ f := by
  have hιreal := holomorphic_is_real_smooth hι
  have hcompreal := holomorphic_is_real_smooth hcomp
  have hreal : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f :=
    hLee ι f hemb hιreal hιinj hcompreal
  apply holomorphic_of_real_smooth_and_derivative hreal
  intro x v
  apply hιinj (f x)
  have hchain := mfderiv_comp x
    (hιreal.mdifferentiableAt (by simp) (x := f x))
    (hreal.mdifferentiableAt (by simp) (x := x))
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) (ι ∘ f) x =
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ι (f x)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) at hchain
  calc
    _ = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) (ι ∘ f) x (Complex.I • v) := by
      rw [hchain]
      rfl
    _ = Complex.I • (show V from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V)
      (ι ∘ f) x v) := real_derivative_commutes_i_of_holomorphic hcomp x v
    _ = Complex.I • (show V from mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ι (f x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x v)) := by rw [hchain]; rfl
    _ = mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ι (f x)
      (Complex.I • (show F from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x v)) :=
      (real_derivative_commutes_i_of_holomorphic hι (f x) _).symm

end
end QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization
