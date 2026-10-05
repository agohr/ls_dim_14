import QuaternionicSymmetry.KillingFieldsPaperMoments
namespace QuaternionicSymmetry.KillingFieldsPaperCertificate
open MvPolynomial DimensionThirteenFourteenDensity
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

def weights4_1 : Fin 1 → ℚ := ![3248 / 15]
def support4_1 : Fin 1 → Fin 12 := ![0]
theorem weights4_1_positive (i : Fin 1) : 0 < weights4_1 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights4_1]

def group4_1 : P :=
  ∑ i : Fin 1, C (weights4_1 i) * moment 1 (support4_1 i)

def weights6_1 : Fin 1 → ℚ := ![168896 / 225]
def support6_1 : Fin 1 → Fin 12 := ![0]
theorem weights6_1_positive (i : Fin 1) : 0 < weights6_1 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights6_1]

def group6_1 : P :=
  ∑ i : Fin 1, C (weights6_1 i) * moment 1 (support6_1 i)

def weights6_2 : Fin 2 → ℚ := ![20068 / 33, 59044 / 4125]
def support6_2 : Fin 2 → Fin 12 := ![0, 6]
theorem weights6_2_positive (i : Fin 2) : 0 < weights6_2 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights6_2]

def group6_2 : P :=
  ∑ i : Fin 2, C (weights6_2 i) * moment 2 (support6_2 i)

def weights8_1 : Fin 1 → ℚ := ![373984 / 225]
def support8_1 : Fin 1 → Fin 12 := ![0]
theorem weights8_1_positive (i : Fin 1) : 0 < weights8_1 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights8_1]

def group8_1 : P :=
  ∑ i : Fin 1, C (weights8_1 i) * moment 1 (support8_1 i)

def weights8_2 : Fin 2 → ℚ := ![3478898 / 2079, 15666206 / 259875]
def support8_2 : Fin 2 → Fin 12 := ![0, 6]
theorem weights8_2_positive (i : Fin 2) : 0 < weights8_2 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights8_2]

def group8_2 : P :=
  ∑ i : Fin 2, C (weights8_2 i) * moment 2 (support8_2 i)

def weights8_3 : Fin 3 → ℚ := ![1555997407 / 462765477, 69513876931 / 462765477, 8363273489 / 462765477]
def support8_3 : Fin 3 → Fin 12 := ![6, 7, 10]
theorem weights8_3_positive (i : Fin 3) : 0 < weights8_3 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights8_3]

def group8_3 : P :=
  ∑ i : Fin 3, C (weights8_3 i) * moment 3 (support8_3 i)

def weights10_1 : Fin 1 → ℚ := ![3364928 / 1125]
def support10_1 : Fin 1 → Fin 12 := ![0]
theorem weights10_1_positive (i : Fin 1) : 0 < weights10_1 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights10_1]

def group10_1 : P :=
  ∑ i : Fin 1, C (weights10_1 i) * moment 1 (support10_1 i)

def weights10_2 : Fin 2 → ℚ := ![11252696 / 4455, 86450624 / 556875]
def support10_2 : Fin 2 → Fin 12 := ![0, 6]
theorem weights10_2_positive (i : Fin 2) : 0 < weights10_2 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights10_2]

def group10_2 : P :=
  ∑ i : Fin 2, C (weights10_2 i) * moment 2 (support10_2 i)

def weights10_3 : Fin 3 → ℚ := ![218013654061 / 6941482155, 20876910519307 / 48590375085, 578272362323 / 6941482155]
def support10_3 : Fin 3 → Fin 12 := ![6, 7, 10]
theorem weights10_3_positive (i : Fin 3) : 0 < weights10_3 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights10_3]

def group10_3 : P :=
  ∑ i : Fin 3, C (weights10_3 i) * moment 3 (support10_3 i)

def weights10_4 : Fin 5 → ℚ := ![76725377446472029 / 3420042727095, 6526042748888190253 / 246243076350840, 920100557319229 / 4560056969460, 490127959830784 / 10260128181285, 2710003708106171 / 246243076350840]
def support10_4 : Fin 5 → Fin 12 := ![2, 5, 7, 10, 11]
theorem weights10_4_positive (i : Fin 5) : 0 < weights10_4 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights10_4]

def group10_4 : P :=
  ∑ i : Fin 5, C (weights10_4 i) * moment 4 (support10_4 i)

def weights12_1 : Fin 1 → ℚ := ![176945008 / 37125]
def support12_1 : Fin 1 → Fin 12 := ![0]
theorem weights12_1_positive (i : Fin 1) : 0 < weights12_1 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights12_1]

def group12_1 : P :=
  ∑ i : Fin 1, C (weights12_1 i) * moment 1 (support12_1 i)

def weights12_2 : Fin 2 → ℚ := ![2271693134 / 1029105, 40597517426 / 128638125]
def support12_2 : Fin 2 → Fin 12 := ![0, 6]
theorem weights12_2_positive (i : Fin 2) : 0 < weights12_2 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights12_2]

def group12_2 : P :=
  ∑ i : Fin 2, C (weights12_2 i) * moment 2 (support12_2 i)

def weights12_3 : Fin 3 → ℚ := ![29350862284804 / 229068911115, 1059395618359648 / 1603482377805, 8566273325788 / 45813782223]
def support12_3 : Fin 3 → Fin 12 := ![6, 7, 10]
theorem weights12_3_positive (i : Fin 3) : 0 < weights12_3 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights12_3]

def group12_3 : P :=
  ∑ i : Fin 3, C (weights12_3 i) * moment 3 (support12_3 i)

def weights12_4 : Fin 5 → ℚ := ![1177945968325523269 / 112861409994135, 1578553797143219004613 / 8126021519577720, 34057685089397437 / 150481879992180, 114826637782819744 / 338584229982405, 315399374278428371 / 8126021519577720]
def support12_4 : Fin 5 → Fin 12 := ![2, 5, 7, 10, 11]
theorem weights12_4_positive (i : Fin 5) : 0 < weights12_4 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights12_4]

def group12_4 : P :=
  ∑ i : Fin 5, C (weights12_4 i) * moment 4 (support12_4 i)

def weights12_5 : Fin 7 → ℚ := ![177789292632790634232653856136 / 1424114964987280699682475, 29811535712150602654640335552 / 284822992997456139936495, 42853074781477443378952 / 18988199533163742662433, 221215195239914960994909008563 / 854468978992368419809485, 12494969262296799354550586 / 18988199533163742662433, 8181990891313418724990256 / 94940997665818713312165, 53261846158644562302798617 / 854468978992368419809485]
def support12_5 : Fin 7 → Fin 12 := ![0, 2, 4, 5, 7, 8, 11]
theorem weights12_5_positive (i : Fin 7) : 0 < weights12_5 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights12_5]

def group12_5 : P :=
  ∑ i : Fin 7, C (weights12_5 i) * moment 5 (support12_5 i)

def weights14_1 : Fin 1 → ℚ := ![23680744832 / 3378375]
def support14_1 : Fin 1 → Fin 12 := ![0]
theorem weights14_1_positive (i : Fin 1) : 0 < weights14_1 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights14_1]

def group14_1 : P :=
  ∑ i : Fin 1, C (weights14_1 i) * moment 1 (support14_1 i)

def weights14_2 : Fin 2 → ℚ := ![231436254341272 / 13579040475, 5102152712408 / 339476011875]
def support14_2 : Fin 2 → Fin 12 := ![0, 6]
theorem weights14_2_positive (i : Fin 2) : 0 < weights14_2 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights14_2]

def group14_2 : P :=
  ∑ i : Fin 2, C (weights14_2 i) * moment 2 (support14_2 i)

def weights14_3 : Fin 3 → ℚ := ![22494770325271336 / 62535812734395, 1301203583687113784 / 2188753445703825, 77382206271860536 / 312679063671975]
def support14_3 : Fin 3 → Fin 12 := ![6, 7, 10]
theorem weights14_3_positive (i : Fin 3) : 0 < weights14_3 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights14_3]

def group14_3 : P :=
  ∑ i : Fin 3, C (weights14_3 i) * moment 3 (support14_3 i)

def weights14_4 : Fin 5 → ℚ := ![1014038932884089708310268349 / 49684313811785522029875, 855489561800647521595256 / 115930065560832884736375, 28387033650133962991893572 / 23186013112166576947275, 62563465422821843446273 / 13911607867299946168365, 134032010032776312905819762 / 347790196682498654209125]
def support14_4 : Fin 5 → Fin 12 := ![3, 6, 9, 10, 11]
theorem weights14_4_positive (i : Fin 5) : 0 < weights14_4 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights14_4]

def group14_4 : P :=
  ∑ i : Fin 5, C (weights14_4 i) * moment 4 (support14_4 i)

def weights14_5 : Fin 7 → ℚ := ![438558541799627272136918448790844 / 21383086199284019705732362125, 66103550727266560215670880514148 / 4276617239856803941146472425, 5656883182338474128681604796 / 285107815990453596076431495, 30257515773988383948230977525971062 / 12829851719570411823439417275, 12809131697774171116354130998 / 31678646221161510675159055, 879197063032443709149543462104 / 1425539079952267980382157475, 6584990067098314667655707057608 / 12829851719570411823439417275]
def support14_5 : Fin 7 → Fin 12 := ![0, 2, 4, 5, 7, 8, 11]
theorem weights14_5_positive (i : Fin 7) : 0 < weights14_5 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights14_5]

def group14_5 : P :=
  ∑ i : Fin 7, C (weights14_5 i) * moment 5 (support14_5 i)

def weights14_6 : Fin 11 → ℚ := ![1072713099860856215658012944221351564853803 / 11291491069004988985583299169171411550, 200235994468922957393056999584909121102438448131 / 1264646999728558766385329506947198093600, 11242769265826533321210507111460347120647701 / 2867680271493330536021155344551469600, 39508359428371035238657634948304286691561 / 30110642850679970628222131117790430800, 5210091745017796631093004718311475432651121 / 7475745811203303052524115312003141440, 745812544172353353492195216519988624127 / 1354978928280598678269995900300569386000, 10775452588479621047849188090482837414331 / 4153192117335168362513397395557300800, 3649953617987630632603068892691073143591 / 210774499954759794397554917824533015600, 99594696754186270092778299457061134409 / 4301520407239995804031733016827204400, 422864623449995853268401257126800021169 / 3226140305429996853023799762620403300, 154938952549795997151949198682495339 / 6452280610859993706047599525240806600]
def support14_6 : Fin 11 → Fin 12 := ![0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11]
theorem weights14_6_positive (i : Fin 11) : 0 < weights14_6 i := by
  fin_cases i <;> norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, weights14_6]

def group14_6 : P :=
  ∑ i : Fin 11, C (weights14_6 i) * moment 6 (support14_6 i)

theorem certificate2 : reduced 2 =
  C (16 : ℚ) * u ^ 0 := by
  simp only [reduced, reduced2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, add_zero]
  apply MvPolynomial.funext
  intro v
  simp
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem certificate4 : reduced 4 =
  C (48 : ℚ) * u ^ 1 +
    u ^ 0 * group4_1 := by
  simp only [reduced, reduced4, group4_1, weights4_1, support4_1, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, add_zero]
  rw [moment1_0_eq]
  simp only [expanded1_0]
  apply MvPolynomial.funext
  intro v
  simp
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem certificate6 : reduced 6 =
  C (96 : ℚ) * u ^ 2 +
    u ^ 1 * group6_1 +
    u ^ 0 * group6_2 := by
  simp only [reduced, reduced6, group6_1, weights6_1, support6_1, group6_2, weights6_2, support6_2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, add_zero]
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq]
  simp only [expanded1_0, expanded2_0, expanded2_6]
  apply MvPolynomial.funext
  intro v
  simp
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem certificate8 : reduced 8 =
  C (160 : ℚ) * u ^ 3 +
    u ^ 2 * group8_1 +
    u ^ 1 * group8_2 +
    u ^ 0 * group8_3 := by
  simp only [reduced, reduced8, group8_1, weights8_1, support8_1, group8_2, weights8_2, support8_2, group8_3, weights8_3, support8_3, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, add_zero]
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq]
  simp only [expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10]
  apply MvPolynomial.funext
  intro v
  simp
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem certificate10 : reduced 10 =
  C (240 : ℚ) * u ^ 4 +
    u ^ 3 * group10_1 +
    u ^ 2 * group10_2 +
    u ^ 1 * group10_3 +
    u ^ 0 * group10_4 := by
  simp only [reduced, reduced10, group10_1, weights10_1, support10_1, group10_2, weights10_2, support10_2, group10_3, weights10_3, support10_3, group10_4, weights10_4, support10_4, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, add_zero]
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_2_eq, moment4_5_eq, moment4_7_eq, moment4_10_eq, moment4_11_eq]
  simp only [expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_2, expanded4_5, expanded4_7, expanded4_10, expanded4_11]
  apply MvPolynomial.funext
  intro v
  simp
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem certificate12 : reduced 12 =
  C (336 : ℚ) * u ^ 5 +
    u ^ 4 * group12_1 +
    u ^ 3 * group12_2 +
    u ^ 2 * group12_3 +
    u ^ 1 * group12_4 +
    u ^ 0 * group12_5 := by
  simp only [reduced, reduced12, group12_1, weights12_1, support12_1, group12_2, weights12_2, support12_2, group12_3, weights12_3, support12_3, group12_4, weights12_4, support12_4, group12_5, weights12_5, support12_5, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, add_zero]
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_2_eq, moment4_5_eq, moment4_7_eq, moment4_10_eq, moment4_11_eq, moment5_0_eq, moment5_2_eq, moment5_4_eq, moment5_5_eq, moment5_7_eq, moment5_8_eq, moment5_11_eq]
  simp only [expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_2, expanded4_5, expanded4_7, expanded4_10, expanded4_11, expanded5_0, expanded5_2, expanded5_4, expanded5_5, expanded5_7, expanded5_8, expanded5_11]
  apply MvPolynomial.funext
  intro v
  simp
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

theorem certificate14 : reduced 14 =
  C (448 : ℚ) * u ^ 6 +
    eta ^ 2 +
    u ^ 5 * group14_1 +
    u ^ 4 * group14_2 +
    u ^ 3 * group14_3 +
    u ^ 2 * group14_4 +
    u ^ 1 * group14_5 +
    u ^ 0 * group14_6 := by
  simp only [reduced, reduced14, group14_1, weights14_1, support14_1, group14_2, weights14_2, support14_2, group14_3, weights14_3, support14_3, group14_4, weights14_4, support14_4, group14_5, weights14_5, support14_5, group14_6, weights14_6, support14_6, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, add_zero]
  rw [moment1_0_eq, moment2_0_eq, moment2_6_eq, moment3_6_eq, moment3_7_eq, moment3_10_eq, moment4_3_eq, moment4_6_eq, moment4_9_eq, moment4_10_eq, moment4_11_eq, moment5_0_eq, moment5_2_eq, moment5_4_eq, moment5_5_eq, moment5_7_eq, moment5_8_eq, moment5_11_eq, moment6_0_eq, moment6_1_eq, moment6_2_eq, moment6_3_eq, moment6_5_eq, moment6_6_eq, moment6_7_eq, moment6_8_eq, moment6_9_eq, moment6_10_eq, moment6_11_eq, eta_eq]
  simp only [expanded1_0, expanded2_0, expanded2_6, expanded3_6, expanded3_7, expanded3_10, expanded4_3, expanded4_6, expanded4_9, expanded4_10, expanded4_11, expanded5_0, expanded5_2, expanded5_4, expanded5_5, expanded5_7, expanded5_8, expanded5_11, expanded6_0, expanded6_1, expanded6_2, expanded6_3, expanded6_5, expanded6_6, expanded6_7, expanded6_8, expanded6_9, expanded6_10, expanded6_11, expandedEta]
  apply MvPolynomial.funext
  intro v
  simp
  all_goals try dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  all_goals norm_num [Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, Matrix.vecCons, map_ofNat]
  all_goals ring

end
end QuaternionicSymmetry.KillingFieldsPaperCertificate
