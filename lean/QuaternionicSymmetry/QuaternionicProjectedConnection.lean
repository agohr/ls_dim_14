import QuaternionicSymmetry.QuaternionicFrameInjectionSpan
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Orthogonal projection of a connection through a smooth rectangular
orthonormal frame. Metricity and quaternionic compatibility are internal
calculations and do not assume an induced submanifold connection. -/
namespace QuaternionicSymmetry.QuaternionicProjectedConnection
open QuaternionicFrameInjectionSpan QuaternionicRangeFrameCoordinates
open VectorBundleFrameTransitions Filter
open scoped ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000
variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]

def covariantFrameDerivative (Γ : X → X →L[ℝ] E →L[ℝ] E) (B : X → F →L[ℝ] E)
    (y : X) : X →L[ℝ] F →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ F E E).flip (B y)).comp (Γ y) + fderiv ℝ B y

def form (Γ : X → X →L[ℝ] E →L[ℝ] E) (B : X → F →L[ℝ] E)
    (y : X) : X →L[ℝ] F →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ F E F (B y).adjoint).comp (covariantFrameDerivative Γ B y)

theorem form_apply (Γ : X → X →L[ℝ] E →L[ℝ] E) (B : X → F →L[ℝ] E)
    (y u : X) (v : F) :
    form Γ B y u v = (B y).adjoint (Γ y u (B y v) + fderiv ℝ B y u v) := rfl

theorem derivative_metric (B : X → F →L[ℝ] E) (y : X)
    (hB : DifferentiableAt ℝ B y)
    (horth : ∀ᶠ z in 𝓝 y, ∀ v w, inner ℝ (B z v) (B z w) = inner ℝ v w)
    (u : X) (v w : F) :
    inner ℝ (fderiv ℝ B y u v) (B y w) + inner ℝ (B y v) (fderiv ℝ B y u w) = 0 := by
  have he : (fun z => inner ℝ (B z v) (B z w)) =ᶠ[𝓝 y] fun _ => inner ℝ v w :=
    horth.mono fun z hz => hz v w
  have hd := congrArg (fun L : X →L[ℝ] ℝ => L u) he.fderiv_eq
  have hc : fderiv ℝ (fun _ : X => inner ℝ v w) y = 0 := by simp
  rw [hc] at hd
  change fderiv ℝ (fun z => inner ℝ (B z v) (B z w)) y u = 0 at hd
  rw [fderiv_inner_apply ℝ (hB.clm_apply (differentiableAt_const v))
    (hB.clm_apply (differentiableAt_const w)) u] at hd
  have hvc : fderiv ℝ (fun _ : X => v) y = 0 := by simp
  have hwc : fderiv ℝ (fun _ : X => w) y = 0 := by simp
  simpa only [fderiv_clm_apply hB (differentiableAt_const v),
    fderiv_clm_apply hB (differentiableAt_const w),hvc,hwc,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.flip_apply,map_zero,zero_add,add_comm] using hd

theorem metric (Γ : X → X →L[ℝ] E →L[ℝ] E) (B : X → F →L[ℝ] E) (y : X)
    (hB : DifferentiableAt ℝ B y)
    (horth : ∀ᶠ z in 𝓝 y, ∀ v w, inner ℝ (B z v) (B z w) = inner ℝ v w)
    (hΓ : ∀ u v w, inner ℝ (Γ y u v) w + inner ℝ v (Γ y u w) = 0)
    (u : X) (v w : F) :
    inner ℝ (form Γ B y u v) w + inner ℝ v (form Γ B y u w) = 0 := by
  simp only [form_apply,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right,
    inner_add_left,inner_add_right]
  linarith [hΓ u (B y v) (B y w),derivative_metric B y hB horth u v w]

theorem generator_skew (Q : QuaternionicStructure E) (t : Fin 3) (v w : E) :
    inner ℝ (quaternionicGenerator Q t v) w = -inner ℝ v (quaternionicGenerator Q t w) := by
  fin_cases t
  · exact Q.I_skew v w
  · exact Q.J_skew v w
  · exact Q.K_skew v w

theorem adjoint_generator (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
    (B : F →L[ℝ] E)
    (hI : ∀ v, B (S.I v) = Q.I (B v)) (hJ : ∀ v, B (S.J v) = Q.J (B v))
    (t : Fin 3) (z : E) :
    B.adjoint (quaternionicGenerator Q t z) = quaternionicGenerator S t (B.adjoint z) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,generator_skew Q,
    ← generator_intertwines S Q B hI hJ,← ContinuousLinearMap.adjoint_inner_left,generator_skew S]

theorem compression_mem_span (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
    (B : F →L[ℝ] E) (hB : ∀ v w, inner ℝ (B v) (B w) = inner ℝ v w)
    (hI : ∀ v, B (S.I v) = Q.I (B v)) (hJ : ∀ v, B (S.J v) = Q.J (B v))
    (A : E →L[ℝ] E) (hA : A ∈ quaternionicSpan Q) :
    B.adjoint.comp (A.comp B) ∈ quaternionicSpan S := by
  classical
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hA
  have he : B.adjoint.comp (A.comp B) = ∑ t, a t • quaternionicGenerator S t := by
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ha]
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul,
      adjoint_generator S Q B hI hJ,adjoint_left_inverse B hB]
  rw [he]
  exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (generator_mem_span S t))

theorem span_preserves_image (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
    (B : F →L[ℝ] E)
    (hI : ∀ v, B (S.I v) = Q.I (B v)) (hJ : ∀ v, B (S.J v) = Q.J (B v))
    (A : E →L[ℝ] E) (hA : A ∈ quaternionicSpan Q) (v : F) :
    ∃ w, A (B v) = B w := by
  classical
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hA
  refine ⟨∑ t, a t • quaternionicGenerator S t v,?_⟩
  rw [← ha]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul,
    generator_intertwines S Q B hI hJ]

theorem derivative_generator (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
    (B : X → F →L[ℝ] E) (y : X) (hB : DifferentiableAt ℝ B y)
    (hI : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.I v) = Q.I (B z v))
    (hJ : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.J v) = Q.J (B z v))
    (t : Fin 3) (u : X) (v : F) :
    fderiv ℝ B y u (quaternionicGenerator S t v) =
      quaternionicGenerator Q t (fderiv ℝ B y u v) := by
  have he : (fun z => B z (quaternionicGenerator S t v)) =ᶠ[𝓝 y]
      (fun z => quaternionicGenerator Q t (B z v)) := by
    filter_upwards [hI,hJ] with z hi hj
    exact generator_intertwines S Q (B z) hi hj t v
  have hl := hB.hasFDerivAt.clm_apply (hasFDerivAt_const (quaternionicGenerator S t v) y)
  have hr := (quaternionicGenerator Q t).hasFDerivAt.comp y
    (hB.hasFDerivAt.clm_apply (hasFDerivAt_const v y))
  change HasFDerivAt (fun z => quaternionicGenerator Q t (B z v)) _ y at hr
  have hd := congrArg (fun L : X →L[ℝ] E => L u) he.fderiv_eq
  rw [hl.fderiv,hr.fderiv] at hd
  simpa using hd

theorem quaternionic (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
    (Γ : X → X →L[ℝ] E →L[ℝ] E) (B : X → F →L[ℝ] E) (y : X)
    (hB : DifferentiableAt ℝ B y)
    (horth : ∀ v w, inner ℝ (B y v) (B y w) = inner ℝ v w)
    (hI : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.I v) = Q.I (B z v))
    (hJ : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.J v) = Q.J (B z v))
    (hΓ : ∀ u t, (Γ y u).comp (quaternionicGenerator Q t) -
      (quaternionicGenerator Q t).comp (Γ y u) ∈ quaternionicSpan Q)
    (u : X) (t : Fin 3) :
    (form Γ B y u).comp (quaternionicGenerator S t) -
      (quaternionicGenerator S t).comp (form Γ B y u) ∈ quaternionicSpan S := by
  have hi := hI.self_of_nhds
  have hj := hJ.self_of_nhds
  have he : (form Γ B y u).comp (quaternionicGenerator S t) -
      (quaternionicGenerator S t).comp (form Γ B y u) =
      (B y).adjoint.comp (((Γ y u).comp (quaternionicGenerator Q t) -
        (quaternionicGenerator Q t).comp (Γ y u)).comp (B y)) := by
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,form_apply]
    rw [generator_intertwines S Q (B y) hi hj,derivative_generator S Q B y hB hI hJ,
      ← adjoint_generator S Q (B y) hi hj]
    simp only [map_add,map_sub]
    abel
  rw [he]
  exact compression_mem_span S Q (B y) horth hi hj _ (hΓ u t)

theorem smooth_form (Γ : X → X →L[ℝ] E →L[ℝ] E) (B : X → F →L[ℝ] E)
    (U : Set X) (hU : IsOpen U) (hΓ : ContDiffOn ℝ ∞ Γ U) (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (form Γ B) U := by
  have hdB := hB.fderiv_of_isOpen hU (m := ∞) (by simp)
  let R : (F →L[ℝ] E) →L[ℝ] ((E →L[ℝ] E) →L[ℝ] F →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ F E E).flip
  have hR : ContDiff ℝ ∞ R := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (n := ∞) (E := F →L[ℝ] E) (F := (E →L[ℝ] E) →L[ℝ] F →L[ℝ] E) R
  have hRight : ContDiffOn ℝ ∞
      (fun y => (ContinuousLinearMap.compL ℝ F E E).flip (B y)) U :=
    hR.comp_contDiffOn hB
  have hC : ContDiffOn ℝ ∞ (covariantFrameDerivative Γ B) U := by
    exact (hRight.clm_comp hΓ).add hdB
  have hAdj : ContDiffOn ℝ ∞ (fun y => (B y).adjoint) U :=
    (ContinuousLinearMap.adjoint : (F →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] F)).contDiff.comp_contDiffOn hB
  have hL : ContDiff ℝ ∞ (ContinuousLinearMap.compL ℝ F E F) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := E →L[ℝ] F) (F := (F →L[ℝ] E) →L[ℝ] F →L[ℝ] F)
      (ContinuousLinearMap.compL ℝ F E F)
  have hLeft : ContDiffOn ℝ ∞
      (fun y => ContinuousLinearMap.compL ℝ F E F (B y).adjoint) U :=
    hL.comp_contDiffOn hAdj
  exact hLeft.clm_comp hC

end
end QuaternionicSymmetry.QuaternionicProjectedConnection
