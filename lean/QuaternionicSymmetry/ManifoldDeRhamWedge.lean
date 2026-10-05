import QuaternionicSymmetry.ManifoldDifferentialForms
import QuaternionicSymmetry.ContinuousWedgeLeibniz

/-!
The normalized wedge of genuine tangent-fiber forms. Smoothness and closedness
are deduced in charts from the all-degree local wedge calculus.
-/

namespace QuaternionicSymmetry.ManifoldDeRhamWedge

open QuaternionicSymmetry.ManifoldDifferentialForms
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {p q : ℕ}

-- Mathlib deliberately does not register normed instances for tangent fibers:
-- their norm comes from the model `E` and depends on the chosen chart.
private noncomputable instance tangentNormedGroup (x : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedAddCommGroup E
  infer_instance

private noncomputable instance tangentNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  change NormedSpace ℝ E
  infer_instance

/-- Transport from the preferred chart back to the tangent fiber recovers
the original value of a form at the chart center. -/
theorem inChartModel_center_transport {n : ℕ}
    (α : Form 𝓘(ℝ, E) M n) (x : M) :
    (inChartModel x α (extChartAt 𝓘(ℝ, E) x x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x) = α x := by
  let C := extChartAt 𝓘(ℝ, E) x
  have hx : x ∈ C.source := mem_extChartAt_source x
  have hcomp :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C.symm (C x)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) =
          ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x) := by
    simpa [C, mfderivWithin_univ] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (I := 𝓘(ℝ, E)) hx)
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    inChartModel_self_apply]
  rw [C.left_inv hx]
  have hv : ∀ i, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C.symm (C x))
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) (v i)) = v i := by
    intro i
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun L : TangentSpace 𝓘(ℝ, E) x →L[ℝ]
        TangentSpace 𝓘(ℝ, E) x => L (v i)) hcomp
  congr 1
  funext i
  exact hv i

theorem form_ext_center {n : ℕ} (α β : Form 𝓘(ℝ, E) M n)
    (h : ∀ x : M, inChartModel x α (extChartAt 𝓘(ℝ, E) x x) =
      inChartModel x β (extChartAt 𝓘(ℝ, E) x x)) : α = β := by
  funext x
  calc
    α x = ContinuousAlternatingMap.compContinuousLinearMap
      (inChartModel x α (extChartAt 𝓘(ℝ, E) x x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x) :=
        (inChartModel_center_transport α x).symm
    _ = ContinuousAlternatingMap.compContinuousLinearMap
      (inChartModel x β (extChartAt 𝓘(ℝ, E) x x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) x) := by rw [h x]
    _ = β x := inChartModel_center_transport β x

private theorem wedge_comp {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F)
    (a : F [⋀^Fin p]→L[ℝ] ℝ) (b : F [⋀^Fin q]→L[ℝ] ℝ) :
    ContinuousAlternatingMap.compContinuousLinearMap
      (ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) a b) L =
    ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
      (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) := by
  ext v
  simp only [ContinuousWedge.wedge_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1

/-- Pointwise normalized wedge on the actual tangent fibers. -/
noncomputable def formWedge
    (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q) :
    Form 𝓘(ℝ, E) M (p + q) :=
  fun x => ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) (α x) (β x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem inChartModel_formWedge
    (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q)
    (x : M) (y : E) :
    inChartModel x (formWedge α β) y =
      ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (inChartModel x α y) (inChartModel x β y) := by
  unfold inChartModel inChart formWedge
  exact wedge_comp
    (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) x).symm (Set.range 𝓘(ℝ, E)) y)
    (α ((extChartAt 𝓘(ℝ, E) x).symm y))
    (β ((extChartAt 𝓘(ℝ, E) x).symm y))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem chartSmooth_formWedge
    (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q)
    (hα : ChartSmooth α) (hβ : ChartSmooth β) :
    ChartSmooth (formWedge α β) := by
  intro x
  have hleft : ContDiffOn ℝ ∞
      (fun y => (ContinuousWedge.wedgeCLM
        (E := E) (p := p) (q := q) (ContinuousLinearMap.mul ℝ ℝ))
          (inChartModel x α y))
      (extChartAt 𝓘(ℝ, E) x).target :=
    (hα x).continuousLinearMap_comp _
  have hw : ContDiffOn ℝ ∞
      (fun y => ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (inChartModel x α y) (inChartModel x β y))
      (extChartAt 𝓘(ℝ, E) x).target := by
    simpa only [ContinuousWedge.wedgeCLM_apply] using
      hleft.clm_apply (hβ x)
  exact hw.congr (fun y _ => inChartModel_formWedge α β x y)

theorem formWedge_closed
    (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q)
    (hα : ChartSmooth α) (hβ : ChartSmooth β)
    (hcα : exteriorDerivative α = 0)
    (hcβ : exteriorDerivative β = 0) :
    exteriorDerivative (formWedge α β) = 0 := by
  funext x
  let C := extChartAt 𝓘(ℝ, E) x
  let y := C x
  have hy : y ∈ C.target := mem_extChartAt_target x
  have hdα : extDeriv (inChartModel x α) y = 0 := by
    rw [← inChartModel_exteriorDerivative_at_center]
    rw [hcα]
    simp only [inChartModel_zero, Pi.zero_apply]
  have hdβ : extDeriv (inChartModel x β) y = 0 := by
    rw [← inChartModel_exteriorDerivative_at_center]
    rw [hcβ]
    simp only [inChartModel_zero, Pi.zero_apply]
  have hdiffα : DifferentiableAt ℝ (inChartModel x α) y :=
    ((hα x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  have hdiffβ : DifferentiableAt ℝ (inChartModel x β) y :=
    ((hβ x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  have heq : inChartModel x (formWedge α β) =
      fun z => ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (inChartModel x α z) (inChartModel x β z) := by
    funext z
    exact inChartModel_formWedge α β x z
  change ContinuousAlternatingMap.compContinuousLinearMap
    (extDeriv (inChartModel x (formWedge α β)) y)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) C x) = 0
  rw [heq]
  have hz : extDeriv (fun z => ContinuousWedge.wedge
      (ContinuousLinearMap.mul ℝ ℝ)
      (inChartModel x α z) (inChartModel x β z)) y = 0 := by
    ext v
    rw [ContinuousWedgeLeibniz.extDeriv_wedge_apply
      (ContinuousLinearMap.mul ℝ ℝ)
      (inChartModel x α) (inChartModel x β) y hdiffα hdiffβ v,
      hdα, hdβ]
    simp [ContinuousWedge.wedge_apply]
  rw [hz]
  ext v
  rfl

/-- Degree transport for alternating forms. -/
noncomputable def castAlternating {m n : ℕ} (h : m = n)
    (eta : E [⋀^Fin m]→L[ℝ] ℝ) : E [⋀^Fin n]→L[ℝ] ℝ := by
  cases h
  exact eta

theorem castAlternating_apply {m n : ℕ} (h : m = n)
    (eta : E [⋀^Fin m]→L[ℝ] ℝ) (v : Fin n → E) :
    castAlternating h eta v = eta (v ∘ finCongr h) := by
  cases h
  rfl

/-- Degree transport for genuine manifold forms. -/
noncomputable def castForm {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) : Form 𝓘(ℝ, E) M n := by
  cases h
  exact α

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem inChartModel_castForm {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) (x : M) (y : E) :
    inChartModel x (castForm h α) y =
      castAlternating h (inChartModel x α y) := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem chartSmooth_castForm {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) (ha : ChartSmooth α) :
    ChartSmooth (castForm h α) := by
  cases h
  exact ha

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem castForm_comp {a b c : ℕ} (h₁ : a = b) (h₂ : b = c)
    (α : Form 𝓘(ℝ, E) M a) :
    castForm h₂ (castForm h₁ α) = castForm (h₁.trans h₂) α := by
  cases h₁
  cases h₂
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem castForm_smul {m n : ℕ} (h : m = n) (c : ℝ)
    (α : Form 𝓘(ℝ, E) M m) :
    castForm h (c • α) = c • castForm h α := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem castForm_sub {m n : ℕ} (h : m = n)
    (α β : Form 𝓘(ℝ, E) M m) :
    castForm h (α - β) = castForm h α - castForm h β := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem castForm_add {m n : ℕ} (h : m = n)
    (α β : Form 𝓘(ℝ, E) M m) :
    castForm h (α + β) = castForm h α + castForm h β := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem exteriorDerivative_castForm {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) :
    exteriorDerivative (castForm h α) =
      castForm (congrArg Nat.succ h) (exteriorDerivative α) := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem exteriorDerivative_castForm_zero {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) (hc : exteriorDerivative α = 0) :
    exteriorDerivative (castForm h α) = 0 := by
  cases h
  exact hc

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_add_left
    (α₁ α₂ : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q) :
    formWedge (α₁ + α₂) β = formWedge α₁ β + formWedge α₂ β := by
  funext x
  exact ContinuousWedge.wedge_add_left (ContinuousLinearMap.mul ℝ ℝ)
    (α₁ x) (α₂ x) (β x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_add_right
    (α : Form 𝓘(ℝ, E) M p) (β₁ β₂ : Form 𝓘(ℝ, E) M q) :
    formWedge α (β₁ + β₂) = formWedge α β₁ + formWedge α β₂ := by
  funext x
  exact ContinuousWedge.wedge_add_right (ContinuousLinearMap.mul ℝ ℝ)
    (α x) (β₁ x) (β₂ x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_smul_left
    (c : ℝ) (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q) :
    formWedge (c • α) β = c • formWedge α β := by
  funext x
  exact ContinuousWedge.wedge_smul_left (ContinuousLinearMap.mul ℝ ℝ)
    c (α x) (β x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_smul_right
    (c : ℝ) (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q) :
    formWedge α (c • β) = c • formWedge α β := by
  funext x
  exact ContinuousWedge.wedge_smul_right (ContinuousLinearMap.mul ℝ ℝ)
    c (α x) (β x)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_sub_left
    (α₁ α₂ : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q) :
    formWedge (α₁ - α₂) β = formWedge α₁ β - formWedge α₂ β := by
  rw [sub_eq_add_neg, formWedge_add_left]
  have hneg := formWedge_smul_left (-1 : ℝ) α₂ β
  simpa only [neg_one_smul] using congrArg
    (fun z => formWedge α₁ β + z) hneg

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_sub_right
    (α : Form 𝓘(ℝ, E) M p) (β₁ β₂ : Form 𝓘(ℝ, E) M q) :
    formWedge α (β₁ - β₂) = formWedge α β₁ - formWedge α β₂ := by
  rw [sub_eq_add_neg, formWedge_add_right]
  have hneg := formWedge_smul_right (-1 : ℝ) α β₂
  simpa only [neg_one_smul] using congrArg
    (fun z => formWedge α β₁ + z) hneg

theorem formWedge_exteriorDerivative_left
    (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q)
    (hα : ChartSmooth α) (hβ : ChartSmooth β)
    (hcβ : exteriorDerivative β = 0) :
    castForm (show (p + 1) + q = (p + q) + 1 by omega)
      (formWedge (exteriorDerivative α) β) =
        exteriorDerivative (formWedge α β) := by
  let hdegree : (p + 1) + q = (p + q) + 1 := by omega
  apply form_ext_center
  intro x
  let C := extChartAt 𝓘(ℝ, E) x
  let y := C x
  have hy : y ∈ C.target := mem_extChartAt_target x
  have hdβ : extDeriv (inChartModel x β) y = 0 := by
    rw [← inChartModel_exteriorDerivative_at_center]
    rw [hcβ]
    simp only [inChartModel_zero, Pi.zero_apply]
  have hdiffα : DifferentiableAt ℝ (inChartModel x α) y :=
    ((hα x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  have hdiffβ : DifferentiableAt ℝ (inChartModel x β) y :=
    ((hβ x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  have heq : inChartModel x (formWedge α β) =
      fun z => ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (inChartModel x α z) (inChartModel x β z) := by
    funext z
    exact inChartModel_formWedge α β x z
  rw [inChartModel_castForm, inChartModel_formWedge,
    inChartModel_exteriorDerivative_at_center,
    inChartModel_exteriorDerivative_at_center, heq]
  ext v
  rw [castAlternating_apply]
  have hindex : finCongr hdegree = ContinuousWedgeShuffle.wedgeLeftIndex p q := rfl
  rw [hindex]
  rw [ContinuousWedgeLeibniz.extDeriv_wedge_apply
    (ContinuousLinearMap.mul ℝ ℝ)
    (inChartModel x α) (inChartModel x β) y hdiffα hdiffβ v,
    hdβ]
  have hz : ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
      (inChartModel x α y)
      (0 : E [⋀^Fin (q + 1)]→L[ℝ] ℝ) = 0 := by
    ext w
    simp [ContinuousWedge.wedge_apply]
  rw [hz]
  simp
  rfl

/-- The other half of the graded Leibniz rule when the left factor is closed.
The degree equality here is definitional because addition recurses on its
right argument. -/
theorem exteriorDerivative_formWedge_right
    (α : Form 𝓘(ℝ, E) M p) (β : Form 𝓘(ℝ, E) M q)
    (hα : ChartSmooth α) (hβ : ChartSmooth β)
    (hcα : exteriorDerivative α = 0) :
    exteriorDerivative (formWedge α β) =
      (-1 : ℝ) ^ p • formWedge α (exteriorDerivative β) := by
  apply form_ext_center
  intro x
  let C := extChartAt 𝓘(ℝ, E) x
  let y := C x
  have hy : y ∈ C.target := mem_extChartAt_target x
  have hdα : extDeriv (inChartModel x α) y = 0 := by
    rw [← inChartModel_exteriorDerivative_at_center]
    rw [hcα]
    simp only [inChartModel_zero, Pi.zero_apply]
  have hdiffα : DifferentiableAt ℝ (inChartModel x α) y :=
    ((hα x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  have hdiffβ : DifferentiableAt ℝ (inChartModel x β) y :=
    ((hβ x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt
      (by norm_num)
  have heq : inChartModel x (formWedge α β) =
      fun z => ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (inChartModel x α z) (inChartModel x β z) := by
    funext z
    exact inChartModel_formWedge α β x z
  rw [inChartModel_exteriorDerivative_at_center, heq,
    inChartModel_smul]
  simp only [Pi.smul_apply]
  rw [inChartModel_formWedge,
    inChartModel_exteriorDerivative_at_center]
  ext v
  rw [ContinuousWedgeLeibniz.extDeriv_wedge_apply
    (ContinuousLinearMap.mul ℝ ℝ)
    (inChartModel x α) (inChartModel x β) y hdiffα hdiffβ v,
    hdα]
  have hz : ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
      (0 : E [⋀^Fin (p + 1)]→L[ℝ] ℝ)
      (inChartModel x β y) = 0 := by
    ext w
    simp [ContinuousWedge.wedge_apply]
  rw [hz]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  simpa only [ContinuousAlternatingMap.smul_apply, y, C] using
    (show (0 : E [⋀^Fin ((p + 1) + q)]→L[ℝ] ℝ)
      (v ∘ ContinuousWedgeShuffle.wedgeLeftIndex p q) +
      (-1 : ℝ) ^ p *
        ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
          (inChartModel x α y) (extDeriv (inChartModel x β) y) v =
      (-1 : ℝ) ^ p *
        ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
          (inChartModel x α y) (extDeriv (inChartModel x β) y) v by simp)

/-- The wedge of an exact form with a closed form is the derivative of the
wedge of its primitive with the closed factor. -/
theorem exactWedgeLeft_identity (k l : ℕ)
    (η : Form 𝓘(ℝ, E) M k)
    (β : Form 𝓘(ℝ, E) M (l + 1))
    (hη : ChartSmooth η) (hβ : ChartSmooth β)
    (hcβ : exteriorDerivative β = 0) :
    castForm (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
      (formWedge (exteriorDerivative η) β) =
        exteriorDerivative
          (castForm (show k + (l + 1) = k + l + 1 by omega)
            (formWedge η β)) := by
  let hleft : (k + 1) + (l + 1) = (k + (l + 1)) + 1 := by omega
  let hprim : k + (l + 1) = k + l + 1 := by omega
  let htotal : (k + 1) + (l + 1) = (k + l + 1) + 1 := by omega
  rw [exteriorDerivative_castForm]
  rw [← formWedge_exteriorDerivative_left η β hη hβ hcβ]
  rw [castForm_comp]

theorem exactWedgeRight_identity (k l : ℕ)
    (α : Form 𝓘(ℝ, E) M (k + 1))
    (η : Form 𝓘(ℝ, E) M l)
    (hα : ChartSmooth α) (hη : ChartSmooth η)
    (hcα : exteriorDerivative α = 0) :
    castForm (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
      (formWedge α (exteriorDerivative η)) =
        exteriorDerivative
          (((-1 : ℝ) ^ (k + 1)) •
            castForm (show (k + 1) + l = k + l + 1 by omega)
              (formWedge α η)) := by
  let hprim : (k + 1) + l = k + l + 1 := by omega
  let htotal : (k + 1) + (l + 1) = (k + l + 1) + 1 := by omega
  have hsign : ((-1 : ℝ) ^ (k + 1)) * ((-1 : ℝ) ^ (k + 1)) = 1 := by
    rw [← pow_add]
    have heq : (k + 1) + (k + 1) = 2 * (k + 1) := by omega
    rw [heq, pow_mul]
    norm_num
  calc
    castForm htotal (formWedge α (exteriorDerivative η)) =
        ((-1 : ℝ) ^ (k + 1)) •
          castForm (congrArg Nat.succ hprim)
            (((-1 : ℝ) ^ (k + 1)) •
              formWedge α (exteriorDerivative η)) := by
      rw [castForm_smul, smul_smul, hsign, one_smul]
    _ = ((-1 : ℝ) ^ (k + 1)) •
          castForm (congrArg Nat.succ hprim)
            (exteriorDerivative (formWedge α η)) := by
      rw [exteriorDerivative_formWedge_right α η hα hη hcα]
    _ = exteriorDerivative
          (((-1 : ℝ) ^ (k + 1)) •
            castForm hprim (formWedge α η)) := by
      rw [exteriorDerivative_smul, exteriorDerivative_castForm]

/-- Wedge of closed positive-degree forms, with the degree equality explicit. -/
noncomputable def closedWedge (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedForms (E := E) (M₀ := M) ((k + l + 1) + 1) := by
  let h : (k + 1) + (l + 1) = (k + l + 1) + 1 := by omega
  have hcα : exteriorDerivative α.1.1 = 0 := by
    exact congrArg Subtype.val α.2
  have hcβ : exteriorDerivative β.1.1 = 0 := by
    exact congrArg Subtype.val β.2
  refine ⟨⟨castForm h (formWedge α.1.1 β.1.1), ?_⟩, ?_⟩
  · exact chartSmooth_castForm h _ (chartSmooth_formWedge α.1.1 β.1.1
      α.1.2 β.1.2)
  · change smoothExteriorDerivative (E := E) (M₀ := M) ((k + l + 1) + 1)
      ⟨castForm h (formWedge α.1.1 β.1.1),
        chartSmooth_castForm h _ (chartSmooth_formWedge α.1.1 β.1.1
          α.1.2 β.1.2)⟩ = 0
    apply Subtype.ext
    exact exteriorDerivative_castForm_zero h _
      (formWedge_closed α.1.1 β.1.1 α.1.2 β.1.2 hcα hcβ)

theorem closedWedge_sub_left (k l : ℕ)
    (α₁ α₂ : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedWedge k l (α₁ - α₂) β =
      closedWedge k l α₁ β - closedWedge k l α₂ β := by
  apply Subtype.ext
  apply Subtype.ext
  change castForm
      (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
        (formWedge (α₁.1.1 - α₂.1.1) β.1.1) =
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α₁.1.1 β.1.1) -
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α₂.1.1 β.1.1)
  rw [formWedge_sub_left, castForm_sub]

theorem closedWedge_sub_right (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β₁ β₂ : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedWedge k l α (β₁ - β₂) =
      closedWedge k l α β₁ - closedWedge k l α β₂ := by
  apply Subtype.ext
  apply Subtype.ext
  change castForm
      (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
        (formWedge α.1.1 (β₁.1.1 - β₂.1.1)) =
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α.1.1 β₁.1.1) -
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α.1.1 β₂.1.1)
  rw [formWedge_sub_right, castForm_sub]

theorem closedWedge_add_left (k l : ℕ)
    (α₁ α₂ : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedWedge k l (α₁ + α₂) β =
      closedWedge k l α₁ β + closedWedge k l α₂ β := by
  apply Subtype.ext
  apply Subtype.ext
  change castForm
      (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
        (formWedge (α₁.1.1 + α₂.1.1) β.1.1) =
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α₁.1.1 β.1.1) +
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α₂.1.1 β.1.1)
  rw [formWedge_add_left, castForm_add]

theorem closedWedge_add_right (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β₁ β₂ : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedWedge k l α (β₁ + β₂) =
      closedWedge k l α β₁ + closedWedge k l α β₂ := by
  apply Subtype.ext
  apply Subtype.ext
  change castForm
      (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
        (formWedge α.1.1 (β₁.1.1 + β₂.1.1)) =
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α.1.1 β₁.1.1) +
      castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α.1.1 β₂.1.1)
  rw [formWedge_add_right, castForm_add]

theorem closedWedge_smul_left (k l : ℕ) (c : ℝ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedWedge k l (c • α) β = c • closedWedge k l α β := by
  apply Subtype.ext
  apply Subtype.ext
  change castForm
      (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
        (formWedge (c • α.1.1) β.1.1) =
      c • castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α.1.1 β.1.1)
  rw [formWedge_smul_left, castForm_smul]

theorem closedWedge_smul_right (k l : ℕ) (c : ℝ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedWedge k l α (c • β) = c • closedWedge k l α β := by
  apply Subtype.ext
  apply Subtype.ext
  change castForm
      (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
        (formWedge α.1.1 (c • β.1.1)) =
      c • castForm
        (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
          (formWedge α.1.1 β.1.1)
  rw [formWedge_smul_right, castForm_smul]

theorem closedWedge_exact_left (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1))
    (hα : α ∈ exactClosedAddSubgroup (E := E) (M₀ := M) k) :
    closedWedge k l α β ∈
      exactClosedAddSubgroup (E := E) (M₀ := M) (k + l + 1) := by
  change (α.1 : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := k + 1)) ∈
    exactForms (E := E) (M₀ := M) k at hα
  rcases hα with ⟨η, hη⟩
  have hform : exteriorDerivative η.1 = α.1.1 :=
    congrArg Subtype.val hη
  have hcβ : exteriorDerivative β.1.1 = 0 :=
    congrArg Subtype.val β.2
  change (closedWedge k l α β).1 ∈ exactForms (E := E) (M₀ := M) (k + l + 1)
  let hprim : k + (l + 1) = k + l + 1 := by omega
  let primitive : smoothForms (I := 𝓘(ℝ, E)) (M := M)
      (n := k + l + 1) :=
    ⟨castForm hprim (formWedge η.1 β.1.1),
      chartSmooth_castForm hprim _
        (chartSmooth_formWedge η.1 β.1.1 η.2 β.1.2)⟩
  refine ⟨primitive, ?_⟩
  apply Subtype.ext
  change exteriorDerivative
      (castForm hprim (formWedge η.1 β.1.1)) =
    castForm (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
      (formWedge α.1.1 β.1.1)
  rw [← hform]
  exact (exactWedgeLeft_identity k l η.1 β.1.1 η.2 β.1.2 hcβ).symm

theorem closedWedge_exact_right (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1))
    (hβ : β ∈ exactClosedAddSubgroup (E := E) (M₀ := M) l) :
    closedWedge k l α β ∈
      exactClosedAddSubgroup (E := E) (M₀ := M) (k + l + 1) := by
  change (β.1 : smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := l + 1)) ∈
    exactForms (E := E) (M₀ := M) l at hβ
  rcases hβ with ⟨η, hη⟩
  have hform : exteriorDerivative η.1 = β.1.1 :=
    congrArg Subtype.val hη
  have hcα : exteriorDerivative α.1.1 = 0 :=
    congrArg Subtype.val α.2
  change (closedWedge k l α β).1 ∈ exactForms (E := E) (M₀ := M) (k + l + 1)
  let hprim : (k + 1) + l = k + l + 1 := by omega
  let primitiveForm : Form 𝓘(ℝ, E) M (k + l + 1) :=
    ((-1 : ℝ) ^ (k + 1)) •
      castForm hprim (formWedge α.1.1 η.1)
  have hprimitive : ChartSmooth primitiveForm := by
    change ChartSmooth (((-1 : ℝ) ^ (k + 1)) •
      castForm hprim (formWedge α.1.1 η.1))
    exact (smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := k + l + 1)).smul_mem
      _ (chartSmooth_castForm hprim _
        (chartSmooth_formWedge α.1.1 η.1 α.1.2 η.2))
  refine ⟨⟨primitiveForm, hprimitive⟩, ?_⟩
  apply Subtype.ext
  change exteriorDerivative primitiveForm =
    castForm (show (k + 1) + (l + 1) = (k + l + 1) + 1 by omega)
      (formWedge α.1.1 β.1.1)
  rw [← hform]
  exact (exactWedgeRight_identity k l α.1.1 η.1 α.1.2 η.2 hcα).symm

/-- The normalized wedge induces a product of positive-degree de Rham
classes. The proof uses both exact-factor lemmas, so the result is independent
of the chosen closed representatives. -/
noncomputable def cohomologyWedge (k l : ℕ) :
    positiveDegreeCohomology (E := E) (M₀ := M) k →
      positiveDegreeCohomology (E := E) (M₀ := M) l →
        positiveDegreeCohomology (E := E) (M₀ := M) (k + l + 1) :=
  fun a b => Quotient.liftOn₂ a b
    (fun α β => QuotientAddGroup.mk (closedWedge k l α β))
    (by
      intro α₁ β₁ α₂ β₂ hα hβ
      have ha : α₁ - α₂ ∈ exactClosedAddSubgroup (E := E) (M₀ := M) k := by
        have hh : -α₁ + α₂ ∈
            exactClosedAddSubgroup (E := E) (M₀ := M) k :=
          QuotientAddGroup.leftRel_apply.mp hα
        have hh' := (exactClosedAddSubgroup (E := E) (M₀ := M) k).neg_mem hh
        convert hh' using 1; abel
      have hb : β₁ - β₂ ∈ exactClosedAddSubgroup (E := E) (M₀ := M) l := by
        have hh : -β₁ + β₂ ∈
            exactClosedAddSubgroup (E := E) (M₀ := M) l :=
          QuotientAddGroup.leftRel_apply.mp hβ
        have hh' := (exactClosedAddSubgroup (E := E) (M₀ := M) l).neg_mem hh
        convert hh' using 1; abel
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have hsplit :
          closedWedge k l α₁ β₁ - closedWedge k l α₂ β₂ =
            closedWedge k l (α₁ - α₂) β₁ +
              closedWedge k l α₂ (β₁ - β₂) := by
        rw [closedWedge_sub_left, closedWedge_sub_right]
        abel
      rw [hsplit]
      exact (exactClosedAddSubgroup (E := E) (M₀ := M)
        (k + l + 1)).add_mem
        (closedWedge_exact_left k l (α₁ - α₂) β₁ ha)
        (closedWedge_exact_right k l α₂ (β₁ - β₂) hb))

theorem cohomologyWedge_mk (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    cohomologyWedge k l (QuotientAddGroup.mk α) (QuotientAddGroup.mk β) =
      QuotientAddGroup.mk (closedWedge k l α β) := rfl

/-- The canonical map from smooth closed forms to their positive-degree
de Rham classes. -/
noncomputable def closedFormClass (k : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1)) :
    positiveDegreeCohomology (E := E) (M₀ := M) k :=
  QuotientAddGroup.mk α

theorem closedFormClass_wedge (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    closedFormClass (k + l + 1) (closedWedge k l α β) =
      cohomologyWedge k l (closedFormClass k α) (closedFormClass l β) := by
  rfl

theorem cohomologyWedge_add_left (k l : ℕ)
    (a a' : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    cohomologyWedge k l (a + a') b =
      cohomologyWedge k l a b + cohomologyWedge k l a' b := by
  refine QuotientAddGroup.induction_on a ?_
  intro α
  refine QuotientAddGroup.induction_on a' ?_
  intro α'
  refine QuotientAddGroup.induction_on b ?_
  intro β
  change QuotientAddGroup.mk (closedWedge k l (α + α') β) =
    QuotientAddGroup.mk (closedWedge k l α β) +
      QuotientAddGroup.mk (closedWedge k l α' β)
  rw [closedWedge_add_left, QuotientAddGroup.mk_add]

theorem cohomologyWedge_add_right (k l : ℕ)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (b b' : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    cohomologyWedge k l a (b + b') =
      cohomologyWedge k l a b + cohomologyWedge k l a b' := by
  refine QuotientAddGroup.induction_on a ?_
  intro α
  refine QuotientAddGroup.induction_on b ?_
  intro β
  refine QuotientAddGroup.induction_on b' ?_
  intro β'
  change QuotientAddGroup.mk (closedWedge k l α (β + β')) =
    QuotientAddGroup.mk (closedWedge k l α β) +
      QuotientAddGroup.mk (closedWedge k l α β')
  rw [closedWedge_add_right, QuotientAddGroup.mk_add]

/-- Real scalar multiplication on positive-degree de Rham classes, induced
from the existing scalar multiplication on closed smooth forms. -/
noncomputable def cohomologyScalar (k : ℕ) (c : ℝ) :
    positiveDegreeCohomology (E := E) (M₀ := M) k →
      positiveDegreeCohomology (E := E) (M₀ := M) k :=
  fun a => Quotient.liftOn a (fun α => QuotientAddGroup.mk (c • α))
    (by
      intro α β hab
      have hdiff : α - β ∈ exactClosedAddSubgroup (E := E) (M₀ := M) k := by
        have hh : -α + β ∈
            exactClosedAddSubgroup (E := E) (M₀ := M) k :=
          QuotientAddGroup.leftRel_apply.mp hab
        have hh' := (exactClosedAddSubgroup (E := E) (M₀ := M) k).neg_mem hh
        convert hh' using 1; abel
      have hscaled : c • (α - β) ∈
          exactClosedAddSubgroup (E := E) (M₀ := M) k := by
        change c • ((α - β).1 :
          smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := k + 1)) ∈
            exactForms (E := E) (M₀ := M) k
        exact (exactForms (E := E) (M₀ := M) k).smul_mem c hdiff
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have hrew : c • (α - β) = c • α - c • β := by
        exact smul_sub c α β
      rw [hrew] at hscaled
      exact hscaled)

theorem cohomologyScalar_mk (k : ℕ) (c : ℝ)
    (α : closedForms (E := E) (M₀ := M) (k + 1)) :
    cohomologyScalar k c (QuotientAddGroup.mk α) =
      QuotientAddGroup.mk (c • α) := rfl

theorem cohomologyWedge_smul_left (k l : ℕ) (c : ℝ)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    cohomologyWedge k l (cohomologyScalar k c a) b =
      cohomologyScalar (k + l + 1) c (cohomologyWedge k l a b) := by
  refine QuotientAddGroup.induction_on a ?_
  intro α
  refine QuotientAddGroup.induction_on b ?_
  intro β
  change QuotientAddGroup.mk (closedWedge k l (c • α) β) =
    QuotientAddGroup.mk (c • closedWedge k l α β)
  rw [closedWedge_smul_left]

theorem cohomologyWedge_smul_right (k l : ℕ) (c : ℝ)
    (a : positiveDegreeCohomology (E := E) (M₀ := M) k)
    (b : positiveDegreeCohomology (E := E) (M₀ := M) l) :
    cohomologyWedge k l a (cohomologyScalar l c b) =
      cohomologyScalar (k + l + 1) c (cohomologyWedge k l a b) := by
  refine QuotientAddGroup.induction_on a ?_
  intro α
  refine QuotientAddGroup.induction_on b ?_
  intro β
  change QuotientAddGroup.mk (closedWedge k l α (c • β)) =
    QuotientAddGroup.mk (c • closedWedge k l α β)
  rw [closedWedge_smul_right]

end QuaternionicSymmetry.ManifoldDeRhamWedge
