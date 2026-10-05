import QuaternionicSymmetry.QuaternionicNormalizerCurvature
import QuaternionicSymmetry.QuaternionicKSWModelAlgebra
import QuaternionicSymmetry.HyperkahlerRicciZero
import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
import QuaternionicSymmetry.AlgebraicRiemannPairSymmetry

/-! The quaternionic scalar/Weyl decomposition follows internally from the
algebraic Riemann identities and membership in the quaternionic normalizer. -/
namespace QuaternionicSymmetry.QuaternionicAlgebraicKSWDecomposition
open QuaternionicLieAlgebraProjection QuaternionicKSWModelAlgebra
open QuaternionicKSWModelRicci QuaternionicKSWUpperModel QuaternionicStandardSolderSquare
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicRankThreeOrthogonal
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] (S : QuaternionicStructure E)

set_option maxHeartbeats 1500000 in
theorem decomposition (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hn : 2 ≤ S.quaternionicDimension)
    (hfirst : ∀ u v, R u v = -R v u)
    (hlast : ∀ u v w z, inner ℝ (R u v w) z = -inner ℝ (R u v z) w)
    (hB : ∀ u v w, R u v w + R v w u + R w u v = 0)
    (hA : ∀ u v b, symplecticProjection S (R u v) * synth S b =
      synth S b * symplecticProjection S (R u v)) :
    ∃ (lam : ℝ) (W : E →L[ℝ] E →L[ℝ] E →L[ℝ] E),
      HyperWeylFiber S W ∧ ∀ u v, R u v = lam • scalarModelR0 S u v + W u v := by
  obtain ⟨c,hc⟩ := QuaternionicNormalizerCurvature.exists_scalar S R hn hfirst hlast hB hA
  let lam : ℝ := -c / 2
  let W := R - lam • modelBilinear S
  have hWe (u v : E) : W u v = R u v - lam • scalarModelR0 S u v := rfl
  have hWf (u v : E) : W u v = -W v u := by
    rw [hWe, hWe, hfirst u v, model_skew_first S u v]
    module
  have hWl (u v w z : E) : inner ℝ (W u v w) z = -inner ℝ (W u v z) w := by
    simp only [hWe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    rw [hlast u v w z, model_skew_last S u v w z]
    ring
  have hWB (u v w : E) : W u v w + W v w u + W w u v = 0 := by
    simp only [hWe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    have hr := hB u v w
    have hm := model_first_bianchi S u v w
    calc
      _ = (R u v w + R v w u + R w u v) -
          lam • (scalarModelR0 S u v w + scalarModelR0 S v w u + scalarModelR0 S w u v) := by module
      _ = 0 := by rw [hr, hm, smul_zero, sub_self]
  have hWft (u v w z : E) : inner ℝ (W u v w) z = -inner ℝ (W v u w) z := by
    rw [hWf, ContinuousLinearMap.neg_apply, inner_neg_left]
  have hWBt (u v w z : E) : inner ℝ (W u v w) z + inner ℝ (W v w u) z +
      inner ℝ (W w u v) z = 0 := by
    have he := congrArg (fun t : E => inner ℝ t z) (hWB u v w)
    simpa only [inner_add_left, inner_zero_left] using he
  have hWp (u v w z : E) : inner ℝ (W u v w) z = inner ℝ (W w z u) v :=
    AlgebraicRiemannPairSymmetry.pair_symmetry (fun u v w z => inner ℝ (W u v w) z)
      hWft hWl hWBt u v w z
  have hWsplit (u v : E) : W u v =
      symplecticProjection S (R u v) + lam • upperSquare S u v := by
    have hr := projection_sum S (R u v)
    rw [hc] at hr
    rw [hWe, scalarModelR0]
    conv_lhs => rw [← hr]
    dsimp only [lam]
    module
  have hWi (u v w : E) : W u v (S.I w) = S.I (W u v w) := by
    have he := congrArg (fun B : E →L[ℝ] E => B w)
      (hA u v (Pi.basisFun ℝ (Fin 3) 0))
    rw [synth_basis] at he
    change symplecticProjection S (R u v) (S.I w) =
      S.I (symplecticProjection S (R u v) w) at he
    simp only [hWsplit, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      map_add, map_smul, he, upperSquare_commutes_I]
  have hWj (u v w : E) : W u v (S.J w) = S.J (W u v w) := by
    have he := congrArg (fun B : E →L[ℝ] E => B w)
      (hA u v (Pi.basisFun ℝ (Fin 3) 1))
    rw [synth_basis] at he
    change symplecticProjection S (R u v) (S.J w) =
      S.J (symplecticProjection S (R u v) w) at he
    simp only [hWsplit, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      map_add, map_smul, he, upperSquare_commutes_J]
  refine ⟨lam, W, ?_, ?_⟩
  · refine ⟨hWf, ?_, ?_, ?_, hWp, ?_⟩
    · intro u v w z
      rw [hWl]
      congr 1
      exact real_inner_comm _ _
    · intro u v
      apply ContinuousLinearMap.ext
      exact hWi u v
    · intro u v
      apply ContinuousLinearMap.ext
      exact hWj u v
    · exact HyperkahlerRicciZero.ricci_zero S W hWft hWl hWp hWBt hWi hWj
  · intro u v
    rw [hWe]
    module

theorem ricci_of_decomposition
    (R W : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (lam : ℝ)
    (hW : HyperWeylFiber S W)
    (he : ∀ u v, R u v = lam • scalarModelR0 S u v + W u v) (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E), inner ℝ (R (stdOrthonormalBasis ℝ E a) v w)
      (stdOrthonormalBasis ℝ E a)) =
      (lam * ((Module.finrank ℝ E : ℝ) + 8)) * inner ℝ v w := by
  simp_rw [he]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, real_inner_smul_left, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [scalarModelR0_ricci S, hW.2.2.2.2.2 v w]
  ring

end
end QuaternionicSymmetry.QuaternionicAlgebraicKSWDecomposition
