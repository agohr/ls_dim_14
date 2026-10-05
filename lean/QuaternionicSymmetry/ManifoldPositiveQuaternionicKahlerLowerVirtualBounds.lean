import QuaternionicSymmetry.ManifoldFiniteVirtualNumbers
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerTwoSixQuarterNumbers
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerSevenTenQuarterNumbers

/-! Bounds for the actual tangent virtual-character functional in quaternionic
dimensions two through ten, integrated against the canonical quarter class. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerLowerVirtualBounds
open Module
open ManifoldTangentCharacterNumber ManifoldFiniteVirtualNumbers
open ManifoldPositiveQuaternionicKahlerTwoSixQuarterNumbers
open ManifoldPositiveQuaternionicKahlerSevenTenQuarterNumbers
open ManifoldQuaternionicQuarterVolume ManifoldQuaternionicCanonicalIntegration
open ManifoldPositiveQuaternionicKahlerGeometry
open scoped Manifold ContDiff
noncomputable section

variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem virtual2_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 2) (b : Basis ι ℝ E) :
    16 * integral P.tangent
      (quarterTop P.tangent P.connection 2
        (show 4*2 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 2 1
        (show 4*(1+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 2) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density2_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 2
    (by omega) (by omega) hn
    (show 4*(1+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual3_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 3) (b : Basis ι ℝ E) :
    32 * integral P.tangent
      (quarterTop P.tangent P.connection 3
        (show 4*3 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 3 2
        (show 4*(2+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 3) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density3_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 3
    (by omega) (by omega) hn
    (show 4*(2+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual4_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 4) (b : Basis ι ℝ E) :
    48 * integral P.tangent
      (quarterTop P.tangent P.connection 4
        (show 4*4 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 4 3
        (show 4*(3+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 4) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density4_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 4
    (by omega) (by omega) hn
    (show 4*(3+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual5_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 5) (b : Basis ι ℝ E) :
    72 * integral P.tangent
      (quarterTop P.tangent P.connection 5
        (show 4*5 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 5 4
        (show 4*(4+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 5) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density5_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 5
    (by omega) (by omega) hn
    (show 4*(4+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual6_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 6) (b : Basis ι ℝ E) :
    96 * integral P.tangent
      (quarterTop P.tangent P.connection 6
        (show 4*6 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 6 5
        (show 4*(5+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 6) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density6_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 6
    (by omega) (by omega) hn
    (show 4*(5+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual7_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 7) (b : Basis ι ℝ E) :
    128 * integral P.tangent
      (quarterTop P.tangent P.connection 7
        (show 4*7 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 7 6
        (show 4*(6+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 7) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density7_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 7
    (by omega) (by omega) hn
    (show 4*(6+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual8_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 8) (b : Basis ι ℝ E) :
    160 * integral P.tangent
      (quarterTop P.tangent P.connection 8
        (show 4*8 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 8 7
        (show 4*(7+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 8) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density8_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 8
    (by omega) (by omega) hn
    (show 4*(7+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual9_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 9) (b : Basis ι ℝ E) :
    200 * integral P.tangent
      (quarterTop P.tangent P.connection 9
        (show 4*9 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 9 8
        (show 4*(8+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 9) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density9_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 9
    (by omega) (by omega) hn
    (show 4*(8+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem virtual10_quarter_bound
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 10) (b : Basis ι ℝ E) :
    240 * integral P.tangent
      (quarterTop P.tangent P.connection 10
        (show 4*10 = Module.finrank ℝ E by
          have h := S.real_finrank; omega)) ≤
      characteristicFunctional P.tangent P.connection 10 9
        (show 4*(9+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (Characters.virtual 10) := by
  obtain ⟨t, _ht, hb⟩ :=
    exists_density10_sourceNumber_quarter_bound S P hsp heq38 hn b
  rw [virtual_eq_source S P.tangent P.connection 10
    (by omega) (by omega) hn
    (show 4*(9+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega) t]
  simpa only [FiniteVirtualDensity.density] using hb

theorem quarterTop_positive (n : ℕ)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn2 : 2 ≤ S.quaternionicDimension)
    (hdim : 4*n = Module.finrank ℝ E) :
    0 < integral P.tangent (quarterTop P.tangent P.connection n hdim) := by
  let hd := ManifoldQuaternionicKSWEq38Input.decomposition_of_KSWEq38OnModel
    S P.tangent heq38 P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ :=
    ManifoldQuaternionicKSWScalarConstancyDerived.exists_global_parameter_of_eq38
      S P.tangent P.toPositiveScalarTangentGeometry hd hn2 P.connected
  rw [quarterTop_integral_normalized P.tangent P.connection S
    (ManifoldQuaternionicKSWScalarInput.formula_of_KSWLemma310OnModel
      S P.tangent hsp P.toPositiveScalarTangentGeometry hn2)
    t (fun p y hy => (ht p y hy).symm) n hdim]
  exact mul_pos (by positivity) (ManifoldQuaternionicCanonicalIntegration.integral_topForm_pos P.tangent)

theorem virtual2_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 2) :
    0 < characteristicFunctional P.tangent P.connection 2 1
      (show 4*(1+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 2) := by
  have hbound := virtual2_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 2 hsp heq38
    (by omega) (show 4*2 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 16) hquarter) hbound

theorem virtual3_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 3) :
    0 < characteristicFunctional P.tangent P.connection 3 2
      (show 4*(2+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 3) := by
  have hbound := virtual3_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 3 hsp heq38
    (by omega) (show 4*3 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 32) hquarter) hbound

theorem virtual4_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 4) :
    0 < characteristicFunctional P.tangent P.connection 4 3
      (show 4*(3+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 4) := by
  have hbound := virtual4_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 4 hsp heq38
    (by omega) (show 4*4 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 48) hquarter) hbound

theorem virtual5_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 5) :
    0 < characteristicFunctional P.tangent P.connection 5 4
      (show 4*(4+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 5) := by
  have hbound := virtual5_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 5 hsp heq38
    (by omega) (show 4*5 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 72) hquarter) hbound

theorem virtual6_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 6) :
    0 < characteristicFunctional P.tangent P.connection 6 5
      (show 4*(5+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 6) := by
  have hbound := virtual6_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 6 hsp heq38
    (by omega) (show 4*6 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 96) hquarter) hbound

theorem virtual7_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 7) :
    0 < characteristicFunctional P.tangent P.connection 7 6
      (show 4*(6+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 7) := by
  have hbound := virtual7_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 7 hsp heq38
    (by omega) (show 4*7 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 128) hquarter) hbound

theorem virtual8_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 8) :
    0 < characteristicFunctional P.tangent P.connection 8 7
      (show 4*(7+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 8) := by
  have hbound := virtual8_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 8 hsp heq38
    (by omega) (show 4*8 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 160) hquarter) hbound

theorem virtual9_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 9) :
    0 < characteristicFunctional P.tangent P.connection 9 8
      (show 4*(8+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 9) := by
  have hbound := virtual9_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 9 hsp heq38
    (by omega) (show 4*9 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 200) hquarter) hbound

theorem virtual10_positive
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 10) :
    0 < characteristicFunctional P.tangent P.connection 10 9
      (show 4*(9+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega) (Characters.virtual 10) := by
  have hbound := virtual10_quarter_bound S P hsp heq38 hn (Module.finBasis ℝ E)
  have hquarter := quarterTop_positive S P 10 hsp heq38
    (by omega) (show 4*10 = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 240) hquarter) hbound

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerLowerVirtualBounds
