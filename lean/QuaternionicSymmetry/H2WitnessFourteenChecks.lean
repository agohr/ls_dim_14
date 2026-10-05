import QuaternionicSymmetry.H2WitnessFourteen

/-! Finite sign, spectrum, and homogeneity checks for the new dimension-fourteen H2 witness. -/
namespace QuaternionicSymmetry.H2WitnessFourteenChecks
open MvPolynomial FiniteTypeCSchurSix H2WitnessFourteen
open scoped BigOperators
noncomputable section
abbrev P := FiniteTypeCSchurSix.P

def sumWeight {m : ℕ} (k : ℕ) (terms : Fin m → List ℕ × ℚ) : P :=
  ∑ i, C (terms i).2 * orbital 14 k (terms i).1

def terms1 : Fin 1 → List ℕ × ℚ := ![
  ([1], 23680744832/675675)]
theorem w1_entries : w1 = sumWeight 1 terms1 := by
  simp [w1, sumWeight, terms1]

theorem terms1_positive (i : Fin 1) : 0 < (terms1 i).2 := by
  fin_cases i
  all_goals norm_num [terms1]

theorem terms1_admissible (i : Fin 1) :
    (terms1 i).1.length ≤ 14 ∧ (terms1 i).1 ≠ [] ∧
      ∀ x ∈ (terms1 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms1]

def terms2 : Fin 2 → List ℕ × ℚ := ![
  ([50, 1], 171676659316/1674848175),
  ([5, 5, 4, 3, 3, 2], 17216030238103/19897196319)]
theorem w2_entries : w2 = sumWeight 2 terms2 := by
  simp [w2, sumWeight, terms2, Fin.sum_univ_succ]

theorem terms2_positive (i : Fin 2) : 0 < (terms2 i).2 := by
  fin_cases i
  all_goals norm_num [terms2]

theorem terms2_admissible (i : Fin 2) :
    (terms2 i).1.length ≤ 14 ∧ (terms2 i).1 ≠ [] ∧
      ∀ x ∈ (terms2 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms2]
  all_goals simp

def terms3 : Fin 3 → List ℕ × ℚ := ![
  ([2, 2, 1], 273783296517568/672296625),
  ([1, 1, 1, 1], 46347112829804/80675595),
  ([5, 3, 3, 3, 3, 1, 1, 1], 1484602223596/288127125)]
theorem w3_entries : w3 = sumWeight 3 terms3 := by
  simp [w3, sumWeight, terms3, Fin.sum_univ_succ]
  all_goals ring

theorem terms3_positive (i : Fin 3) : 0 < (terms3 i).2 := by
  fin_cases i
  all_goals norm_num [terms3]

theorem terms3_admissible (i : Fin 3) :
    (terms3 i).1.length ≤ 14 ∧ (terms3 i).1 ≠ [] ∧
      ∀ x ∈ (terms3 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms3]
  all_goals simp

def terms4 : Fin 5 → List ℕ × ℚ := ![
  ([1, 1, 1], 356808331361902532433624693713/37332699024560940000000),
  ([20, 20, 20, 1, 1, 1, 1, 1], 127495476249371257585032337/1866634951228047000000000),
  ([10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 122169414208022993203547391499/25199571841578634500000000),
  ([10, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1], 2494744228248597073220802007/2015965747326290760000000),
  ([20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 4837968937363248196357649/24888466016373960000000)]
theorem w4_entries : w4 = sumWeight 4 terms4 := by
  simp [w4, sumWeight, terms4, Fin.sum_univ_succ]
  all_goals ring

theorem terms4_positive (i : Fin 5) : 0 < (terms4 i).2 := by
  fin_cases i
  all_goals norm_num [terms4]

theorem terms4_admissible (i : Fin 5) :
    (terms4 i).1.length ≤ 14 ∧ (terms4 i).1 ≠ [] ∧
      ∀ x ∈ (terms4 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms4]
  all_goals simp

def terms5 : Fin 7 → List ℕ × ℚ := ![
  ([1, 1, 1], 66425800394330667209269014307960/2158186208921284109709141),
  ([4, 1, 1, 1, 1], 14177200569401784892753879755658/5994961691448011415858725),
  ([7, 1, 1, 1, 1, 1], 10615050899403199814419057598/700709808091326009645825),
  ([20, 20, 1, 1, 1, 1, 1, 1], 11705729862598199204367895328/161863965669096308228185575),
  ([10, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1931899571750201774241699455512/269773276115160513713642625),
  ([20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1], 428766438320297179182003308488/5665238798418370787986495125),
  ([20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1225410205325640489589309598/23123423667013758318312225)]
theorem w5_entries : w5 = sumWeight 5 terms5 := by
  simp [w5, sumWeight, terms5, Fin.sum_univ_succ]
  all_goals ring

theorem terms5_positive (i : Fin 7) : 0 < (terms5 i).2 := by
  fin_cases i
  all_goals norm_num [terms5]

theorem terms5_admissible (i : Fin 7) :
    (terms5 i).1.length ≤ 14 ∧ (terms5 i).1 ≠ [] ∧
      ∀ x ∈ (terms5 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms5]
  all_goals simp

def terms6 : Fin 11 → List ℕ × ℚ := ![
  ([2, 1], 143165778678727315577100302989967862553190190411890616611/13538193449181579688147426271630700000000000000000),
  ([3, 1], 30108004661665175052607763476328586914084097175449594871/5479744967525877492821577300421950000000000000000),
  ([1, 1, 1], 7925048720206486642385289299606499841386824073239482372319/230149288636086854698506246617721900000000000000000),
  ([13, 4, 3], 7904185324346295923596513556450109864952395212499119/5415277379672631875258970508652280000000000000000),
  ([1, 1, 1, 1, 1], 794300393518454199293023657035292225075709414701143590603/805522510226303991444771863162026650000000000000000),
  ([11, 4, 2, 1, 1, 1], 189659299265698663493575850330116572066642545499151733/7671642954536228489950208220590730000000000000000),
  ([15, 2, 1, 1, 1, 1], 945271277695911598512837768333383198960259974816453/2001298162052929171291358666241060000000000000000),
  ([7, 7, 1, 1, 1, 1, 1], 616011666803318092230596046586234060566011034931782349/537015006817535994296514575441351100000000000000000),
  ([12, 2, 2, 1, 1, 1, 1, 1], 23312416219410482719862006390327939304072498738107963/19179107386340571224875520551476825000000000000000),
  ([20, 20, 1, 1, 1, 1, 1, 1, 1, 1], 2991811056066578951260518660513141612851619092830597/613731436362898279196016657647258400000000000000000),
  ([20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 20423584410265784907068635569039992351910060708735919/920597154544347418794024986470887600000000000000000)]
theorem w6_entries : w6 = sumWeight 6 terms6 := by
  simp [w6, sumWeight, terms6, Fin.sum_univ_succ]
  all_goals ring

theorem terms6_positive (i : Fin 11) : 0 < (terms6 i).2 := by
  fin_cases i
  all_goals norm_num [terms6]

theorem terms6_admissible (i : Fin 11) :
    (terms6 i).1.length ≤ 14 ∧ (terms6 i).1 ≠ [] ∧
      ∀ x ∈ (terms6 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms6]
  all_goals simp

/-- All 29 coefficients in the orbital part of the actual witness are positive. -/
theorem all_coefficients_positive :
    (∀ i : Fin 1, 0 < (terms1 i).2) ∧
    (∀ i : Fin 2, 0 < (terms2 i).2) ∧
    (∀ i : Fin 3, 0 < (terms3 i).2) ∧
    (∀ i : Fin 5, 0 < (terms4 i).2) ∧
    (∀ i : Fin 7, 0 < (terms5 i).2) ∧
    (∀ i : Fin 11, 0 < (terms6 i).2) := by
  exact ⟨terms1_positive, terms2_positive, terms3_positive,
    terms4_positive, terms5_positive, terms6_positive⟩

/-- Every listed spectrum is nonempty, strictly positive, and fits in 14 slots. -/
theorem all_spectra_admissible :
    (∀ i : Fin 1, (terms1 i).1.length ≤ 14 ∧ (terms1 i).1 ≠ [] ∧
      ∀ x ∈ (terms1 i).1, 0 < x) ∧
    (∀ i : Fin 2, (terms2 i).1.length ≤ 14 ∧ (terms2 i).1 ≠ [] ∧
      ∀ x ∈ (terms2 i).1, 0 < x) ∧
    (∀ i : Fin 3, (terms3 i).1.length ≤ 14 ∧ (terms3 i).1 ≠ [] ∧
      ∀ x ∈ (terms3 i).1, 0 < x) ∧
    (∀ i : Fin 5, (terms4 i).1.length ≤ 14 ∧ (terms4 i).1 ≠ [] ∧
      ∀ x ∈ (terms4 i).1, 0 < x) ∧
    (∀ i : Fin 7, (terms5 i).1.length ≤ 14 ∧ (terms5 i).1 ≠ [] ∧
      ∀ x ∈ (terms5 i).1, 0 < x) ∧
    (∀ i : Fin 11, (terms6 i).1.length ≤ 14 ∧ (terms6 i).1 ≠ [] ∧
      ∀ x ∈ (terms6 i).1, 0 < x) := by
  exact ⟨terms1_admissible, terms2_admissible, terms3_admissible,
    terms4_admissible, terms5_admissible, terms6_admissible⟩

theorem orbitalSum_entries :
    H2WitnessFourteen.orbitalSum =
      DimensionThirteenFourteenDensity.u ^ 13 * H2WitnessFourteen.embed (sumWeight 1 terms1) +
      DimensionThirteenFourteenDensity.u ^ 12 * H2WitnessFourteen.embed (sumWeight 2 terms2) +
      DimensionThirteenFourteenDensity.u ^ 11 * H2WitnessFourteen.embed (sumWeight 3 terms3) +
      DimensionThirteenFourteenDensity.u ^ 10 * H2WitnessFourteen.embed (sumWeight 4 terms4) +
      DimensionThirteenFourteenDensity.u ^ 9 * H2WitnessFourteen.embed (sumWeight 5 terms5) +
      DimensionThirteenFourteenDensity.u ^ 8 * H2WitnessFourteen.embed (sumWeight 6 terms6) := by
  rw [← w1_entries, ← w2_entries, ← w3_entries, ← w4_entries,
    ← w5_entries, ← w6_entries]
  rfl

private theorem factor_explicit : H2WitnessFourteen.factor =
    DimensionThirteenFourteenDensity.u ^ 2 * DimensionThirteenFourteenDensity.p1 +
    C (88656 / 1000000000 : ℚ) * DimensionThirteenFourteenDensity.p3 +
    C (251370 / 1000000000 : ℚ) *
      DimensionThirteenFourteenDensity.p1 * DimensionThirteenFourteenDensity.p2 +
    C (223959 / 1000000000 : ℚ) * DimensionThirteenFourteenDensity.p1 ^ 3 := by
  simp [H2WitnessFourteen.factor, H2WitnessFourteen.embed,
    H2WitnessThirteen.embed, H2WitnessFourteen.f1, H2WitnessFourteen.f3,
    FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3]
  ring

theorem factor_homogeneous (t : DimensionThirteenFourteenDensity.P) :
    MvPolynomial.aeval ![t * DimensionThirteenFourteenDensity.u,
      t * DimensionThirteenFourteenDensity.p1,
      t ^ 2 * DimensionThirteenFourteenDensity.p2,
      t ^ 3 * DimensionThirteenFourteenDensity.p3,
      t ^ 4 * DimensionThirteenFourteenDensity.p4,
      t ^ 5 * DimensionThirteenFourteenDensity.p5,
      t ^ 6 * DimensionThirteenFourteenDensity.p6] H2WitnessFourteen.factor =
      t ^ 3 * H2WitnessFourteen.factor := by
  rw [factor_explicit]
  simp [DimensionThirteenFourteenDensity.u,
    DimensionThirteenFourteenDensity.p1,
    DimensionThirteenFourteenDensity.p2,
    DimensionThirteenFourteenDensity.p3]
  ring

theorem witness_homogeneous (t : DimensionThirteenFourteenDensity.P) :
    MvPolynomial.aeval ![t * DimensionThirteenFourteenDensity.u,
      t * DimensionThirteenFourteenDensity.p1,
      t ^ 2 * DimensionThirteenFourteenDensity.p2,
      t ^ 3 * DimensionThirteenFourteenDensity.p3,
      t ^ 4 * DimensionThirteenFourteenDensity.p4,
      t ^ 5 * DimensionThirteenFourteenDensity.p5,
      t ^ 6 * DimensionThirteenFourteenDensity.p6] H2WitnessFourteen.witness =
      t ^ 14 * H2WitnessFourteen.witness := by
  rw [← H2WitnessFourteen.density14_witness]
  exact DimensionThirteenFourteenDensity.density14_homogeneous t

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The complete identity remains valid after specialization into any
commutative rational algebra, including algebras with nilpotents. -/
theorem density14_witness_eval (v : Fin 7 → R) :
    MvPolynomial.aeval v DimensionThirteenFourteenDensity.density14 =
      MvPolynomial.aeval v H2WitnessFourteen.witness :=
  congrArg (MvPolynomial.aeval v) H2WitnessFourteen.density14_witness

end
end QuaternionicSymmetry.H2WitnessFourteenChecks
