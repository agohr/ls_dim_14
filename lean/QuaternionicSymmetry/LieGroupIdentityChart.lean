import QuaternionicSymmetry.LocalAdjointDifferential
import QuaternionicSymmetry.GeneralRealAdjointDifferentialSource
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Multiplication matrices in the actual chart at the identity. -/
namespace QuaternionicSymmetry.LieGroupIdentityChart

open LocalAdjointDifferential GeneralRealAdjointDifferentialSource
open scoped Manifold ContDiff Topology
open Filter Function Set
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]

abbrev identityChart := extChartAt 𝓘(ℝ,E) (1 : G)
abbrev identityCoordinate : E := identityChart (E := E) (G := G) 1

def chartMul (p : E × E) : E :=
  identityChart (identityChart.symm p.1 * identityChart.symm p.2 : G)

local notation "e₁" => identityChart (E := E) (G := G)
local notation "a₁" => identityCoordinate (E := E) (G := G)

lemma chart_center_derivative :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (e₁) 1 =
      ContinuousLinearMap.id ℝ E := by
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E (1 : G)) 1 = _
  rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source E 1)]
  ext v
  exact tangentCoordChange_self (mem_extChartAt_source (1 : G))

lemma chart_symm_center_derivative :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (e₁).symm
      (a₁) = ContinuousLinearMap.id ℝ E := by
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := 𝓘(ℝ,E)) (x := (1 : G)) (mem_extChartAt_target (1 : G))
  rw [extChartAt_to_inv, chart_center_derivative] at h
  ext v
  have hv := congrArg (fun T : E →L[ℝ] E => T v) h
  change (mfderivWithin 𝓘(ℝ,E) 𝓘(ℝ,E) (e₁).symm (Set.range 𝓘(ℝ,E)) a₁) v = v at hv
  simpa using hv

lemma chartMul_smooth : ContDiffAt ℝ ∞ (chartMul (E := E) (G := G))
    (a₁, a₁) := by
  let e := e₁
  let a := a₁
  have he : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm a :=
    (contMDiffOn_extChartAt_symm (1 : G) a (mem_extChartAt_target (1 : G))).contMDiffAt
      (extChartAt_target_mem_nhds (I := 𝓘(ℝ,E)) (1 : G))
  have hp : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => e.symm p.1 * e.symm p.2) (a,a) :=
    (he.comp (f := fun p : E × E => p.1) (a,a)
      (contDiffAt_fst.contMDiffAt)).mul
        (he.comp (f := fun p : E × E => p.2) (a,a) contDiffAt_snd.contMDiffAt)
  have hec : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e (e.symm a * e.symm a) := by
    simpa [e, a, identityCoordinate] using (contMDiffAt_extChartAt (I := 𝓘(ℝ,E)) (x := (1 : G)) (n := ∞))
  exact (hec.comp (a,a) hp).contDiffAt

lemma chart_symm_smoothAt {x : E}
    (hx : x ∈ (e₁).target) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (e₁).symm x :=
  (contMDiffOn_extChartAt_symm (1 : G) x hx).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) (1 : G)).mem_nhds hx)

lemma chart_expression_derivative {f : G → G}
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f 1)
    (hfs : f 1 ∈ (e₁).source) :
    fderiv ℝ (e₁ ∘ f ∘ (e₁).symm)
      (a₁) =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e₁ (f 1)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f 1) := by
  let e := e₁
  let a := a₁
  have hsa : e.symm a = 1 := extChartAt_to_inv (1 : G)
  have hs := (chart_symm_smoothAt (E := E) (G := G) (mem_extChartAt_target (1 : G))).mdifferentiableAt (by simp)
  have hff : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) f (e.symm a) := by
    rw [hsa]; exact hf.mdifferentiableAt (by simp)
  have ht : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) e (f (e.symm a)) := by
    rw [hsa]; exact mdifferentiableAt_extChartAt (by simpa using hfs)
  rw [← mfderiv_eq_fderiv]
  calc
    _ = (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e (f (e.symm a))).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f ∘ e.symm) a) :=
      mfderiv_comp a ht (hff.comp a hs)
    _ = _ := by
      have hh := mfderiv_comp a hff hs
      rw [hsa, chart_symm_center_derivative] at hh
      have hh' : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f ∘ e.symm) a =
          mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f 1 := by
        ext v
        exact congrArg (fun T : E →L[ℝ] E => T v) hh
      rw [hh', hsa]

lemma leftMatrix_eq_mfderiv {x : E}
    (hx : x ∈ (e₁).target)
    (hm : DifferentiableAt ℝ (chartMul (E := E) (G := G))
      (x, a₁)) :
    leftMatrix (chartMul (E := E) (G := G)) a₁ x =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e₁ ((e₁).symm x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h : G => (e₁).symm x * h) 1) := by
  rw [leftMatrix_eq_fderiv hm]
  have hs : (e₁).symm x * (1 : G) ∈
      (e₁).source := by
    simpa only [mul_one] using (e₁).map_target hx
  have h := chart_expression_derivative
    (contMDiff_mul_left (I := 𝓘(ℝ,E)) (a := (e₁).symm x) (n := ∞)).contMDiffAt hs
  rw [mul_one] at h
  exact h

lemma rightMatrix_eq_mfderiv {x : E}
    (hx : x ∈ (e₁).target)
    (hm : DifferentiableAt ℝ (chartMul (E := E) (G := G))
      (a₁, x)) :
    rightMatrix (chartMul (E := E) (G := G)) a₁ x =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e₁ ((e₁).symm x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h : G => h * (e₁).symm x) 1) := by
  rw [rightMatrix_eq_fderiv hm]
  have hs : (1 : G) * (e₁).symm x ∈
      (e₁).source := by
    simpa only [one_mul] using (e₁).map_target hx
  have h := chart_expression_derivative
    (contMDiff_mul_right (I := 𝓘(ℝ,E)) (a := (e₁).symm x) (n := ∞)).contMDiffAt hs
  rw [one_mul] at h
  exact h

lemma leftMatrix_center :
    leftMatrix (chartMul (E := E) (G := G)) a₁ a₁ =
      ContinuousLinearMap.id ℝ E := by
  rw [leftMatrix_eq_mfderiv (mem_extChartAt_target (1 : G))
    (chartMul_smooth.differentiableAt (by simp))]
  rw [show (e₁).symm a₁ = 1 from extChartAt_to_inv (1 : G)]
  have hf : (fun h : G => (1 : G) * h) = id := by funext h; exact one_mul h
  rw [hf, mfderiv_id, chart_center_derivative]
  rfl

lemma rightMatrix_center :
    rightMatrix (chartMul (E := E) (G := G)) a₁ a₁ =
      ContinuousLinearMap.id ℝ E := by
  rw [rightMatrix_eq_mfderiv (mem_extChartAt_target (1 : G))
    (chartMul_smooth.differentiableAt (by simp))]
  rw [show (e₁).symm a₁ = 1 from extChartAt_to_inv (1 : G)]
  have hf : (fun h : G => h * (1 : G)) = id := by funext h; exact mul_one h
  rw [hf, mfderiv_id, chart_center_derivative]
  rfl

lemma eventually_regular_chart :
    ∀ᶠ x in 𝓝 a₁,
      x ∈ (e₁).target ∧
      DifferentiableAt ℝ (chartMul (E := E) (G := G)) (x,a₁) ∧
      DifferentiableAt ℝ (chartMul (E := E) (G := G)) (a₁,x) := by
  have hs : ∀ᶠ p in 𝓝 (a₁,a₁),
      DifferentiableAt ℝ (chartMul (E := E) (G := G)) p := by
    filter_upwards [((contDiffAt_infty.mp (chartMul_smooth (E := E) (G := G))) 1).eventually
      (by simp)] with p hp
    exact hp.differentiableAt (by norm_num)
  have ht : ∀ᶠ x in 𝓝 a₁, x ∈ (e₁).target :=
    extChartAt_target_mem_nhds (I := 𝓘(ℝ,E)) (1 : G)
  have hl : ContinuousAt (fun x : E => (x,a₁)) a₁ := by fun_prop
  have hr : ContinuousAt (fun x : E => (a₁,x)) a₁ := by fun_prop
  exact ht.and ((hl.eventually hs).and (hr.eventually hs))

lemma rightMatrix_eventually_invertible :
    ∀ᶠ x in 𝓝 a₁, (rightMatrix (chartMul (E := E) (G := G)) a₁ x).IsInvertible := by
  let B := rightMatrix (chartMul (E := E) (G := G)) a₁
  have hc : ContinuousAt B a₁ :=
    (rightMatrix_contDiffAt ((contDiffAt_infty.mp chartMul_smooth) 2)).continuousAt
  have hi : ∀ᶠ x in 𝓝 a₁, Function.Injective (B x) := by
    have hn : ∀ᶠ A : E →L[ℝ] E in 𝓝 (B a₁), Function.Injective A := by
      apply ContinuousLinearMap.isOpen_injective.mem_nhds
      rw [show B a₁ = ContinuousLinearMap.id ℝ E from rightMatrix_center]
      exact Function.injective_id
    exact hc.eventually hn
  filter_upwards [hi] with x hx
  exact ⟨(LinearEquiv.ofBijective (B x).toLinearMap
    ⟨hx, (LinearMap.injective_iff_surjective).mp hx⟩).toContinuousLinearEquiv, rfl⟩

lemma right_comp_conjugation_derivative (g : G) :
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h : G => h * g) 1).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h : G => g * h * g⁻¹) 1) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h : G => g * h) 1 := by
  have hR : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun h : G => h * g) := contMDiff_mul_right
  have hC : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun h : G => g * h * g⁻¹) :=
    contMDiff_mul_left.mul contMDiff_const
  have h := mfderiv_comp (1 : G) (hR.mdifferentiableAt (by simp))
    (hC.mdifferentiableAt (by simp))
  have heq : (fun h : G => h * g) ∘ (fun h : G => g * h * g⁻¹) =
      (fun h : G => g * h) := by funext h; simp [Function.comp_apply, mul_assoc]
  rw [heq, mul_one, mul_inv_cancel] at h
  exact h.symm

lemma adjoint_eq_matrix_quotient (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    (fun x => adjointOrbitReal v ((e₁).symm x)) =ᶠ[𝓝 a₁]
      (fun x => (rightMatrix (chartMul (E := E) (G := G)) a₁ x).inverse
        (leftMatrix (chartMul (E := E) (G := G)) a₁ x v)) := by
  filter_upwards [eventually_regular_chart (E := E) (G := G),
    rightMatrix_eventually_invertible (E := E) (G := G)] with x hx hi
  have hcomp : (rightMatrix (chartMul (E := E) (G := G)) a₁ x)
      (adjointOrbitReal v ((e₁).symm x)) =
      leftMatrix (chartMul (E := E) (G := G)) a₁ x v := by
    rw [leftMatrix_eq_mfderiv hx.1 hx.2.1, rightMatrix_eq_mfderiv hx.1 hx.2.2]
    change (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e₁ ((e₁).symm x))
      (((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h : G => h * (e₁).symm x) 1).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h : G => (e₁).symm x * h * ((e₁).symm x)⁻¹) 1)) v) = _
    rw [right_comp_conjugation_derivative]
    rfl
  rw [← hcomp]
  exact (hi.inverse_apply_self _).symm

end
end QuaternionicSymmetry.LieGroupIdentityChart
