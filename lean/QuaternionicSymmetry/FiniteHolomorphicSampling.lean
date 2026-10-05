import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Finite sampling determines a family of holomorphic functions when its
outer-ball bounds are controlled by its inner-ball bounds. This is the
elementary compactness argument behind finite-dimensional section spaces. -/
namespace QuaternionicSymmetry.FiniteHolomorphicSampling
open scoped Topology
open Metric Set
noncomputable section

variable {F W I : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] [AddCommGroup W] [Module ℂ W]
  [Fintype I] [Nonempty I]

theorem finiteDimensional_of_sampling
    (a : I → F) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (eval : I → F → W →ₗ[ℂ] ℂ)
    (hhol : ∀ s i, DifferentiableOn ℂ (fun z => eval i z s) (ball (a i) (3 * r i)))
    (C : ℝ) (hC : 1 ≤ C)
    (hbound : ∀ (s : W) (M : ℝ), 0 ≤ M →
      (∀ i z, z ∈ closedBall (a i) (r i) → ‖eval i z s‖ ≤ M) →
      ∀ i z, z ∈ ball (a i) (3 * r i) → ‖eval i z s‖ ≤ C * M)
    (hzero : ∀ s : W,
      (∀ i z, z ∈ closedBall (a i) (r i) → eval i z s = 0) → s = 0) :
    FiniteDimensional ℂ W := by
  classical
  let ε : I → ℝ := fun i => r i / (2 * C)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hε : ∀ i, 0 < ε i := fun i => div_pos (hr i) (by positivity)
  obtain ⟨d,hd⟩ : ∃ d : ∀ i, Finset (closedBall (a i) (r i)),
      ∀ i z, z ∈ closedBall (a i) (r i) → ∃ w ∈ d i, dist z w < ε i := by
    have hi (i : I) := (isCompact_closedBall (a i) (r i)).elim_finite_subcover
      (fun w : closedBall (a i) (r i) => ball (w : F) (ε i))
      (fun _ => isOpen_ball) (by
        intro z hz
        exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (hε i)⟩)
    choose d hd using hi
    refine ⟨d,?_⟩
    intro i z hz
    obtain ⟨w,hw,hz⟩ := mem_iUnion₂.mp (hd i hz)
    exact ⟨w,hw,hz⟩
  let T : W →ₗ[ℂ] (∀ i, ↥(d i) → ℂ) :=
    { toFun := fun s i z => eval i z.1.1 s
      map_add' := by intros; ext i z; exact map_add _ _ _
      map_smul' := by intros; ext i z; exact map_smul _ _ _ }
  apply FiniteDimensional.of_injective T
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro s hs
  have hsample : ∀ i (w : closedBall (a i) (r i)), w ∈ d i → eval i w s = 0 := by
    intro i w hw
    exact congrFun (congrFun hs i) ⟨w,hw⟩
  let K := Σ i, closedBall (a i) (r i)
  letI (i : I) : CompactSpace (closedBall (a i) (r i)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  letI (i : I) : Nonempty (closedBall (a i) (r i)) :=
    ⟨⟨a i,mem_closedBall_self (hr i).le⟩⟩
  letI : Nonempty K := ⟨⟨Classical.arbitrary I,
    ⟨a (Classical.arbitrary I),mem_closedBall_self (hr _).le⟩⟩⟩
  let φ : K → ℝ := fun p => ‖eval p.1 p.2 s‖
  have hφ : Continuous φ := by
    apply continuous_sigma_iff.mpr
    intro i
    have hsmall : closedBall (a i) (r i) ⊆ ball (a i) (3 * r i) :=
      closedBall_subset_ball (by linarith [hr i])
    exact (((hhol s i).continuousOn.mono hsmall).comp_continuous
      continuous_subtype_val (fun z => z.2)).norm
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set K).Nonempty)
    hφ.continuousOn
  let M := φ p
  have hM : 0 ≤ M := norm_nonneg _
  have hinner : ∀ i z, z ∈ closedBall (a i) (r i) → ‖eval i z s‖ ≤ M := by
    intro i z hz
    exact hp (Set.mem_univ (⟨i,⟨z,hz⟩⟩ : K))
  have hhalf : ∀ i z, z ∈ closedBall (a i) (r i) → ‖eval i z s‖ ≤ M / 2 := by
    intro i z hz
    obtain ⟨w,hw,hzw⟩ := hd i z hz
    have hw0 := hsample i w hw
    have hεle : ε i ≤ r i := by
      dsimp [ε]
      apply (div_le_iff₀ (by positivity : 0 < 2 * C)).2
      nlinarith [hr i]
    have hball : ball (w : F) (r i) ⊆ ball (a i) (3 * r i) := by
      intro v hv
      have hdist := dist_triangle v (w : F) (a i)
      have hwmem := w.2
      simp only [mem_ball, mem_closedBall] at hv hwmem ⊢
      linarith [hr i]
    have hmaps : MapsTo (fun v => eval i v s) (ball (w : F) (r i))
        (closedBall (eval i w s) (C * M)) := by
      intro v hv
      simpa only [mem_closedBall, hw0, dist_zero_right] using hbound s M hM hinner i v (hball hv)
    have hdist := Complex.dist_le_div_mul_dist_of_mapsTo_ball
      ((hhol s i).mono hball) hmaps (lt_of_lt_of_le hzw hεle)
    rw [hw0,dist_zero_right] at hdist
    have hnonneg : 0 ≤ C * M / r i := div_nonneg (mul_nonneg hCpos.le hM) (hr i).le
    calc
      ‖eval i z s‖ ≤ C * M / r i * dist z w := hdist
      _ ≤ C * M / r i * ε i := mul_le_mul_of_nonneg_left hzw.le hnonneg
      _ = M / 2 := by dsimp [ε]; field_simp [(hr i).ne',hCpos.ne']
  have hMz : M = 0 := by
    have hh := hhalf p.1 p.2 p.2.2
    change M ≤ M / 2 at hh
    linarith
  apply hzero s
  intro i z hz
  apply norm_eq_zero.mp
  exact le_antisymm (hMz ▸ hinner i z hz) (norm_nonneg _)

end
end QuaternionicSymmetry.FiniteHolomorphicSampling
