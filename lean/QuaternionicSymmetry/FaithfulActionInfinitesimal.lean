import QuaternionicSymmetry.CompactLieOneParameterSubgroup

/-! The differential of a faithful smooth action detects every Lie algebra
vector. Local integral curves suffice; the acting group need not be compact. -/
namespace QuaternionicSymmetry.FaithfulActionInfinitesimal
open Set Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ,F) ∞ M] [T2Space M]
  (a : G × M → M)
  (ha : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,F) ∞ a)
  (h1 : ∀ x, a (1,x) = x)
  (hmul : ∀ g h x, a (g*h,x) = a (g,a (h,x)))
  (hfaithful : ∀ g, (∀ x, a (g,x) = x) → g = 1)

include ha h1 hmul hfaithful
theorem eq_zero_of_orbit_derivative_zero (v : GroupLieAlgebra 𝓘(ℝ,E) G)
    (hv : ∀ x, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun g => a (g,x)) 1 v = 0) : v = 0 := by
  have horbit (x : M) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (fun g => a (g,x)) :=
    ha.comp (contMDiff_id.prodMk contMDiff_const)
  have hact (g : G) : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (fun x => a (g,x)) :=
    ha.comp (contMDiff_const.prodMk contMDiff_id)
  have hz (g : G) (x : M) : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun g => a (g,x)) g
      (mulInvariantVectorField v g) = 0 := by
    have he : (fun h => a (h,x)) ∘ (fun h => g*h) =
        (fun y => a (g,y)) ∘ (fun h => a (h,x)) := funext (fun h => hmul g h x)
    have hleft := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,F)) 1
      ((horbit x).mdifferentiableAt (by simp) (x := g*1))
      ((contMDiff_mul_left (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableAt (by simp) (x := 1))
    have hright := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,F)) (I'' := 𝓘(ℝ,F)) 1
      ((hact g).mdifferentiableAt (by simp) (x := a (1,x)))
      ((horbit x).mdifferentiableAt (by simp) (x := 1))
    rw [he] at hleft
    rw [hright] at hleft
    have hh := congrArg (fun A : E →L[ℝ] F => A v) hleft.symm
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun h => a (h,x)) (g*1)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun h => g*h) 1 v) =
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (fun y => a (g,y)) (a (1,x))
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun h => a (h,x)) 1 v) at hh
    have hp : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun h => a (h,x)) (g*1) : E →L[ℝ] F) =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun h => a (h,x)) g := by
      congr 1 <;> exact mul_one g
    rw [hp] at hh
    simpa only [hv,map_zero,mulInvariantVectorField] using hh
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  have hfield : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun g => (⟨g,mulInvariantVectorField v g⟩ : TangentBundle 𝓘(ℝ,E) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by
      simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
  obtain ⟨U,_,hU,ε,hε,hlocal⟩ := CompactVectorFieldCompleteness.local_uniform_manifold
    (mulInvariantVectorField v) 1 (hfield 1)
  obtain ⟨γ,hγ0,hγ⟩ := hlocal 1 hU
  have ht0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hγeq (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : γ t = 1 := by
    apply hfaithful
    intro x
    have hi : IsMIntegralCurveOn (fun t => a (γ t,x))
        (fun y : M => (0 : TangentSpace 𝓘(ℝ,F) y)) (Ioo (-ε) ε) := by
      intro s hs
      have hd := ((horbit x).mdifferentiableAt (by simp) (x := γ s)).hasMFDerivAt.comp s
        ((hγ s hs).hasMFDerivAt (isOpen_Ioo.mem_nhds hs))
      apply HasMFDerivAt.hasMFDerivWithinAt
      apply hd.congr_mfderiv
      apply ContinuousLinearMap.ext
      intro r
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply,map_smul,hz,smul_zero]
    have he := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht0
      (v := fun y : M => (0 : TangentSpace 𝓘(ℝ,F) y))
      (Bundle.contMDiff_zeroSection _ _) hi
      ((isMIntegralCurve_const (x := x) rfl).isMIntegralCurveOn _)
      (by simp only [hγ0,h1])
    exact he ht
  have hevent : γ =ᶠ[𝓝 0] (fun _ => (1 : G)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht0] with t ht
    exact hγeq t ht
  have hconst := (hasMFDerivAt_const (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,E)) (1 : G) (0 : ℝ)).congr_of_eventuallyEq hevent
  have hi := (hγ 0 ht0).hasMFDerivAt (isOpen_Ioo.mem_nhds ht0)
  have he := congrArg (fun A : ℝ →L[ℝ] E => A 1) (hi.mfderiv.symm.trans hconst.mfderiv)
  change (1 : ℝ) • mulInvariantVectorField v (γ 0) = 0 at he
  rw [one_smul,hγ0] at he
  unfold mulInvariantVectorField at he
  have hone : (fun x : G => 1*x) = id := funext one_mul
  rw [hone,mfderiv_id] at he
  exact he

end
end QuaternionicSymmetry.FaithfulActionInfinitesimal
