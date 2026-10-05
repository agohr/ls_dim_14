import QuaternionicSymmetry.ManifoldQuaternionicPreferredEinsteinLocallyConstant
import Mathlib.Analysis.Calculus.MeanValue

/-! Schur's pointwise derivative argument from an actual local Einstein
equation. The second Bianchi, metricity, and finite contraction results are
the existing internal proofs; no Eq38 decomposition is used in this route. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicEinsteinSchurFromEquation

open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateEinstein
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicCoordinateMetricity
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicEinsteinDerivative
open ManifoldQuaternionicPreferredEinsteinFactor
open ManifoldQuaternionicSchurTensor
open ManifoldQuaternionicSchurRicciDerivative
open ManifoldQuaternionicScalarCurvature
open QuaternionicSymmetry.AlgebraicSchurContraction
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- The actual Einstein equation with the coefficient prescribed by the
dimension of the tangent model. This is a condition on the existing Ricci
and scalar tensors, not a new source or structure. -/
def LocalEinsteinEquation : Prop :=
  ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (v w : E),
    localRicci Q D p y hy v w =
      (localScalarCurvature Q D p y hy /
        (Module.finrank ℝ E : ℝ)) * inner ℝ v w

theorem coordinateRicci_einstein_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    coordinateRicci Q D p y v w =
      (localScalarCurvature Q D p y hy /
        (Module.finrank ℝ E : ℝ)) * coordinateMetric Q p y v w := by
  rw [coordinateRicci_eq_adapted Q D p y hy,
    hEinstein p y hy (solder Q p y v) (solder Q p y w)]
  rfl

theorem einsteinFactor_eq_scalar_div_dim
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (c : E) (hc : c ≠ 0) :
    einsteinFactor Q D p c y =
      localScalarCurvature Q D p y hy /
        (Module.finrank ℝ E : ℝ) := by
  rw [einsteinFactor,
    coordinateRicci_einstein_fromEquation Q D hEinstein p y hy c c]
  exact mul_div_cancel_right₀ _
    (ne_of_gt (coordinateMetric_self_pos Q p y hy c hc))

theorem coordinateRicci_einsteinFactor_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    coordinateRicci Q D p y v w =
      einsteinFactor Q D p c y * coordinateMetric Q p y v w := by
  rw [coordinateRicci_einstein_fromEquation Q D hEinstein p y hy v w,
    einsteinFactor_eq_scalar_div_dim Q D hEinstein p y hy c hc]

theorem coordinateRicci_covariant_einsteinFactor_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a v w : E) :
    fderiv ℝ (fun z => coordinateRicci Q D p z v w) y a -
      coordinateRicci Q D p y (coordinateConnection Q D p y a v) w -
        coordinateRicci Q D p y v (coordinateConnection Q D p y a w) =
      fderiv ℝ (einsteinFactor Q D p c) y a *
        coordinateMetric Q p y v w := by
  have heq : (fun z => coordinateRicci Q D p z v w) =ᶠ[𝓝 y]
      (fun z => einsteinFactor Q D p c z * coordinateMetric Q p z v w) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateRicci_einsteinFactor_fromEquation Q D hEinstein
      p c hc z hz v w
  have hfactor := einsteinFactor_differentiableAt Q D p y hy c hc
  have hg := coordinateMetric_differentiableAt Q p y hy v w
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_mul hfactor hg] at hd
  have hdA := congrArg (fun L : E →L[ℝ] ℝ => L a) hd
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hdA
  have hm := coordinateConnection_metric Q D p y hy a v w
  rw [coordinateRicci_einsteinFactor_fromEquation Q D hEinstein
      p c hc y hy (coordinateConnection Q D p y a v) w,
    coordinateRicci_einsteinFactor_fromEquation Q D hEinstein
      p c hc y hy v (coordinateConnection Q D p y a w)]
  rw [hdA, hm]
  ring

theorem einsteinFactor_fderiv_basis_zero_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hcard : 3 ≤ Module.finrank ℝ E)
    (a : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (einsteinFactor Q D p c) y
      (coordinateOrthonormalBasis Q p y hy a) = 0 := by
  refine schur_derivative_zero (schurTensor Q D p y hy)
    (fun i => fderiv ℝ (einsteinFactor Q D p c) y
      (coordinateOrthonormalBasis Q p y hy i))
    (by simpa using hcard)
    (schurTensor_pairSymmetric Q D p y hy)
    (schurTensor_secondBianchi Q D p y hy) ?_ a
  intro i v w
  rw [schurTensor_covariantRicci Q D p y hy i v w]
  rw [coordinateRicci_covariant_einsteinFactor_fromEquation Q D hEinstein
    p c hc y hy (coordinateOrthonormalBasis Q p y hy i)
    (coordinateOrthonormalBasis Q p y hy v)
    (coordinateOrthonormalBasis Q p y hy w)]
  rw [← coordinateMetricField_apply Q p y hy,
    coordinateOrthonormalBasis_metric Q p y hy v w]

theorem einsteinFactor_fderiv_eq_zero_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hcard : 3 ≤ Module.finrank ℝ E) :
    fderiv ℝ (einsteinFactor Q D p c) y = 0 := by
  let e := solderEquiv Q p y hy
  let L := fderiv ℝ (einsteinFactor Q D p c) y
  have hcomp : (L.comp e.symm.toContinuousLinearMap).toLinearMap = 0 := by
    apply (stdOrthonormalBasis ℝ E).toBasis.ext
    intro i
    change L (e.symm (stdOrthonormalBasis ℝ E i)) = 0
    exact einsteinFactor_fderiv_basis_zero_fromEquation Q D hEinstein
      p c hc y hy hcard i
  ext u
  have h := congrArg (fun A : E →ₗ[ℝ] ℝ => A (e u)) hcomp
  change L (e.symm (e u)) = 0 at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply, L] using h

theorem target_factor_fiber_open_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (c : E) (hc : c ≠ 0)
    (hcard : 3 ≤ Module.finrank ℝ E) (r : ℝ) :
    IsOpen ((extChartAt 𝓘(ℝ,E) p).target ∩
      (einsteinFactor Q D p c) ⁻¹' {r}) := by
  let U := (extChartAt 𝓘(ℝ,E) p).target
  have hdiff : DifferentiableOn ℝ (einsteinFactor Q D p c) U := by
    intro y hy
    exact (einsteinFactor_differentiableAt Q D p y hy c hc).differentiableWithinAt
  have hzero : U.EqOn (fderiv ℝ (einsteinFactor Q D p c)) 0 := by
    intro y hy
    exact einsteinFactor_fderiv_eq_zero_fromEquation Q D hEinstein
      p c hc y hy hcard
  exact (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).isOpen_inter_preimage_of_fderiv_eq_zero
    hdiff hzero {r}

theorem factor_chart_eq_preferred_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (p : M) (c : E) (hc : c ≠ 0) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    einsteinFactor Q D p c y =
      preferredEinsteinFactor Q D c ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hx := (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hxy := (extChartAt 𝓘(ℝ,E) p).right_inv hy
  have hlocal := localScalarCurvature_eq_preferred Q D p x hx
    (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  have hlocal' : localScalarCurvature Q D p y hy =
      preferredScalarCurvature Q D x := by
    simpa only [x, hxy] using hlocal
  rw [einsteinFactor_eq_scalar_div_dim Q D hEinstein p y hy c hc]
  rw [preferredEinsteinFactor,
    einsteinFactor_eq_scalar_div_dim Q D hEinstein x
      (extChartAt 𝓘(ℝ,E) x x)
      ((extChartAt 𝓘(ℝ,E) x).map_source (by simp)) c hc]
  simpa only [preferredScalarCurvature] using
    congrArg (fun t : ℝ => t / (Module.finrank ℝ E : ℝ)) hlocal'

theorem preferredEinsteinFactor_isLocallyConstant_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (c : E) (hc : c ≠ 0)
    (hcard : 3 ≤ Module.finrank ℝ E) :
    IsLocallyConstant (preferredEinsteinFactor Q D c) := by
  intro r
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let C := extChartAt 𝓘(ℝ,E) x
  let s := preferredEinsteinFactor Q D c x
  let T := C.target ∩ (einsteinFactor Q D x c) ⁻¹' {s}
  have hT : IsOpen T := target_factor_fiber_open_fromEquation Q D hEinstein
    x c hc hcard s
  have hU : IsOpen (C.source ∩ C ⁻¹' T) :=
    (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source x) hT
  have hxsrc : x ∈ C.source := by simp [C]
  have hy : C x ∈ C.target := C.map_source hxsrc
  have hxT : C x ∈ T := by
    refine ⟨hy, ?_⟩
    have h := factor_chart_eq_preferred_fromEquation Q D hEinstein
      x c hc (C x) hy
    rw [C.left_inv hxsrc] at h
    simp [s, h]
  have hxU : x ∈ C.source ∩ C ⁻¹' T := ⟨hxsrc, hxT⟩
  have hsubset : C.source ∩ C ⁻¹' T ⊆
      (preferredEinsteinFactor Q D c) ⁻¹' r := by
    intro z hz
    have hfactor : einsteinFactor Q D x c (C z) = s := hz.2.2
    have h := factor_chart_eq_preferred_fromEquation Q D hEinstein
      x c hc (C z) (hz.2.1)
    rw [C.left_inv hz.1] at h
    have hzx : preferredEinsteinFactor Q D c z = s := h.symm.trans hfactor
    change preferredEinsteinFactor Q D c z ∈ r
    rw [hzx]
    exact hx
  exact Filter.mem_of_superset (hU.mem_nhds hxU) hsubset

theorem preferredEinsteinFactor_eq_scalar_div_dim
    (hEinstein : LocalEinsteinEquation Q D)
    (c : E) (hc : c ≠ 0) (x : M) :
    preferredEinsteinFactor Q D c x =
      preferredScalarCurvature Q D x / (Module.finrank ℝ E : ℝ) := by
  rw [preferredEinsteinFactor,
    einsteinFactor_eq_scalar_div_dim Q D hEinstein x
      (extChartAt 𝓘(ℝ,E) x x)
      ((extChartAt 𝓘(ℝ,E) x).map_source (by simp)) c hc]
  rfl

theorem preferredScalarCurvature_eq_of_preconnected_fromEquation
    (hEinstein : LocalEinsteinEquation Q D)
    (hcard : 3 ≤ Module.finrank ℝ E)
    (hconn : IsPreconnected (Set.univ : Set M))
    (c : E) (hc : c ≠ 0) (x y : M) :
    preferredScalarCurvature Q D x = preferredScalarCurvature Q D y := by
  have hfactor :=
    (preferredEinsteinFactor_isLocallyConstant_fromEquation Q D hEinstein
      c hc hcard).apply_eq_of_isPreconnected hconn (by simp : x ∈ Set.univ)
        (by simp : y ∈ Set.univ)
  rw [preferredEinsteinFactor_eq_scalar_div_dim Q D hEinstein c hc x,
    preferredEinsteinFactor_eq_scalar_div_dim Q D hEinstein c hc y] at hfactor
  exact (div_left_inj' (by exact_mod_cast (by omega : Module.finrank ℝ E ≠ 0))).mp hfactor

end
end QuaternionicSymmetry.ManifoldQuaternionicEinsteinSchurFromEquation
