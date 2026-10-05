import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Differential rank for smooth maps with finite fibers. The local argument
constructs a smooth kernel vector field at a point of maximal rank and uses
an integral curve to rule out a nonzero kernel. -/

namespace QuaternionicSymmetry.FiniteFiberDifferentialRank

open scoped ContDiff Topology
open Filter Function Set Module
noncomputable section

variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

lemma ker_eq_ker_comp_of_rank_le (D : E →L[ℝ] F) (L : F →L[ℝ] W)
    (hSurj : Function.Surjective (L.comp D))
    (hRank : finrank ℝ (LinearMap.range D.toLinearMap) ≤ finrank ℝ W) :
    LinearMap.ker D.toLinearMap = LinearMap.ker (L.comp D).toLinearMap := by
  apply Submodule.eq_of_le_of_finrank_eq (LinearMap.ker_le_ker_comp _ _)
  change finrank ℝ (LinearMap.ker D.toLinearMap) =
    finrank ℝ (LinearMap.ker (L.comp D).toLinearMap)
  have h₁ := D.toLinearMap.finrank_range_add_finrank_ker
  have h₂ := (L.comp D).toLinearMap.finrank_range_add_finrank_ker
  have hR : LinearMap.range (L.comp D).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hSurj
  rw [hR, finrank_top] at h₂
  have hle := Submodule.finrank_mono
    (LinearMap.ker_le_ker_comp D.toLinearMap L.toLinearMap)
  change finrank ℝ (LinearMap.ker D.toLinearMap) ≤
    finrank ℝ (LinearMap.ker (L.comp D).toLinearMap) at hle
  omega

/-- At a local maximum of derivative rank, each kernel vector extends to
a smooth local vector field annihilated by the derivative. -/
theorem exists_smooth_kernel_field {f : E → F} {a : E}
    (hf : ContDiffAt ℝ ∞ f a)
    (hRank : ∀ᶠ x in 𝓝 a,
      finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap))
    (v : E) (hv : fderiv ℝ f a v = 0) :
    ∃ X : E → E, ContDiffAt ℝ 1 X a ∧ X a = v ∧
      ∀ᶠ x in 𝓝 a, fderiv ℝ f x (X x) = 0 := by
  let D := fderiv ℝ f a
  let W := LinearMap.range D.toLinearMap
  obtain ⟨L, hL⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
      (f := W.subtypeL) Subtype.val_injective
  obtain ⟨R, hR⟩ :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
      (f := D.rangeRestrict) (by
        rintro ⟨w, v, rfl⟩
        exact ⟨v, rfl⟩)
  have hLDR (w : W) : L (D (R w)) = w := by
    have hr : D (R w) = w := congrArg Subtype.val (hR w)
    rw [hr]
    exact hL w
  let A : E → W →L[ℝ] W := fun x => L.comp ((fderiv ℝ f x).comp R)
  have hAa : A a = ContinuousLinearMap.id ℝ W := by
    apply ContinuousLinearMap.ext
    intro w
    exact hLDR w
  have hDiff : ContDiffAt ℝ 1 (fderiv ℝ f) a :=
    ((contDiffAt_infty.mp hf) 2).fderiv_right (by norm_num)
  have hA : ContDiffAt ℝ 1 A a :=
    contDiffAt_const.clm_comp (hDiff.clm_comp contDiffAt_const)
  have hInv : ContDiffAt ℝ 1 (fun x => (A x).inverse) a := by
    have hi : ContDiffAt ℝ 1 ContinuousLinearMap.inverse (A a) := by
      rw [hAa]
      exact contDiffAt_map_inverse (ContinuousLinearEquiv.refl ℝ W)
    exact hi.comp a hA
  let X : E → E := fun x => v - R ((A x).inverse (L (fderiv ℝ f x v)))
  refine ⟨X, ?_, ?_, ?_⟩
  · exact contDiffAt_const.sub
      (R.contDiff.contDiffAt.comp a
        (hInv.clm_apply (L.contDiff.contDiffAt.comp a
          (hDiff.clm_apply contDiffAt_const))))
  · dsimp only [X]
    rw [hv, map_zero, map_zero, map_zero, sub_zero]
  · have hInj : ∀ᶠ x in 𝓝 a, Function.Injective (A x) := by
      have hn : ∀ᶠ B : W →L[ℝ] W in 𝓝 (A a), Function.Injective B := by
        apply ContinuousLinearMap.isOpen_injective.mem_nhds
        rw [hAa]
        exact Function.injective_id
      exact hA.continuousAt.eventually hn
    filter_upwards [hRank, hInj] with x hr hi
    have hAi : (A x).IsInvertible := by
      refine ⟨(LinearEquiv.ofBijective (A x).toLinearMap
        ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩).toContinuousLinearEquiv, rfl⟩
    have hs : Function.Surjective (L.comp (fderiv ℝ f x)) := by
      intro w
      obtain ⟨z, hz⟩ := hAi.surjective w
      exact ⟨R z, hz⟩
    have hk := ker_eq_ker_comp_of_rank_le (fderiv ℝ f x) L hs hr
    change X x ∈ LinearMap.ker (fderiv ℝ f x).toLinearMap
    rw [hk]
    change L (fderiv ℝ f x (v - R ((A x).inverse (L (fderiv ℝ f x v))))) = 0
    rw [map_sub, map_sub]
    change L (fderiv ℝ f x v) - A x ((A x).inverse (L (fderiv ℝ f x v))) = 0
    rw [hAi.self_apply_inverse, sub_self]

/-- A locally isolated fiber rules out a nontrivial kernel wherever the
derivative rank is locally maximal. -/
theorem injective_fderiv_of_locally_maximal_rank {f : E → F} {a : E}
    (hf : ContDiffAt ℝ ∞ f a)
    (hRank : ∀ᶠ x in 𝓝 a,
      finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap))
    (hIsolated : ∀ᶠ x in 𝓝 a, f x = f a → x = a) :
    Function.Injective (fderiv ℝ f a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  obtain ⟨X, hX, hXa, hKer⟩ := exists_smooth_kernel_field hf hRank v hv
  obtain ⟨γ, hγa, ε, hε, hγ⟩ :=
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have h0 : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by constructor <;> linarith
  have hγ0 : ContinuousAt γ 0 := (hγ 0 h0).continuousAt
  have hDiff : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x := by
    filter_upwards [((contDiffAt_infty.mp hf) 1).eventually (by simp)] with x hx
    exact hx.differentiableAt (by norm_num)
  have hN : ∀ᶠ t in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ f (γ t) ∧ fderiv ℝ f (γ t) (X (γ t)) = 0 ∧
      (f (γ t) = f a → γ t = a) := by
    have hc : Tendsto γ (𝓝 0) (𝓝 a) := hγa ▸ hγ0
    exact hc.eventually (hDiff.and (hKer.and hIsolated))
  obtain ⟨δ, hδ, hδN⟩ := Metric.eventually_nhds_iff_ball.mp
    (hN.and (Ioo_mem_nhds h0.1 h0.2))
  have hder (t : ℝ) (ht : t ∈ Metric.ball 0 δ) :
      HasDerivAt (f ∘ γ) 0 t := by
    obtain ⟨⟨hd, hk, _⟩, hi⟩ := hδN t ht
    simpa only [hk] using hd.hasFDerivAt.comp_hasDerivAt t (hγ t hi)
  have heq : ∀ᶠ t in 𝓝 (0 : ℝ), γ t = a := by
    filter_upwards [Metric.ball_mem_nhds 0 hδ] with t ht
    apply (hδN t ht).1.2.2
    have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : ℝ) δ).isPreconnected
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv)
      ht (Metric.mem_ball_self hδ)
    simpa only [Function.comp_apply, hγa] using hconst
  have hz : HasDerivAt γ 0 0 := (hasDerivAt_const (0 : ℝ) a).congr_of_eventuallyEq heq
  have hv0 := (hγ 0 h0).unique hz
  rwa [hγa, hXa] at hv0

/-- A smooth map with locally isolated fibers has an injective derivative
somewhere on each nonempty open set. -/
theorem exists_injective_fderiv_on {f : E → F} {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) (hf : ContDiffOn ℝ ∞ f U)
    (hIsolated : ∀ a ∈ U, ∀ᶠ x in 𝓝 a, f x = f a → x = a) :
    ∃ a ∈ U, Function.Injective (fderiv ℝ f a) := by
  let rank : E → ℕ := fun x => finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)
  have hFinite : (rank '' U).Finite := (Set.finite_le_nat (finrank ℝ E)).subset (by
    rintro _ ⟨x, _, rfl⟩
    exact (fderiv ℝ f x).toLinearMap.finrank_range_le)
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ :=
    Set.exists_max_image (rank '' U) id hFinite (hne.image rank)
  refine ⟨a, ha, injective_fderiv_of_locally_maximal_rank
    (hf a ha |>.contDiffAt (hU.mem_nhds ha)) ?_ (hIsolated a ha)⟩
  filter_upwards [hU.mem_nhds ha] with x hx
  exact hmax _ ⟨x, hx, rfl⟩

/-- The dimension bound only uses locally isolated fibers and smoothness. -/
theorem finrank_le_of_locally_isolated_fibers {f : E → F} {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) (hf : ContDiffOn ℝ ∞ f U)
    (hIsolated : ∀ a ∈ U, ∀ᶠ x in 𝓝 a, f x = f a → x = a) :
    finrank ℝ E ≤ finrank ℝ F := by
  obtain ⟨a, _, ha⟩ := exists_injective_fderiv_on hU hne hf hIsolated
  exact LinearMap.finrank_le_finrank_of_injective ha

end

/-- In a Hausdorff space, a finite set has isolated points. The formulation
also works when the center is not a member of the set. -/
theorem eventually_eq_of_mem_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hs : s.Finite) (a : X) :
    ∀ᶠ x in 𝓝 a, x ∈ s → x = a := by
  have hc : IsClosed (s \ {a}) := (hs.subset Set.diff_subset).isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds (by simp)] with x hx hxs
  by_contra hne
  exact hx ⟨hxs, hne⟩

end QuaternionicSymmetry.FiniteFiberDifferentialRank
