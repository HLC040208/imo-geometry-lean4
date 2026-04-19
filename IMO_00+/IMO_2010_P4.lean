import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $P$ be a point interior to Triangle $ABC$ (with $CA ≠ CB$). The lines $AP$, $BP$ and $CP$ meet again its circumcircle $\Gamma$ at $K$, $L$, respectively $M$. The tangent line at $C$ to $\Gamma$ meets the line $AB$ at $S$. Show that from $SC = SP$ follows $MK = ML$.
theorem IMO_2010_P4 :
  ∀ (A B C P K L M S O : Point) (t : Line) (Γ : Circle) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    |(C─A)| ≠ |(C─B)| ∧
    InsideTriangle P A B C AB BC CA ∧
    O.isCentre Γ ∧
    Circumcircle Γ A B C ∧
    between A P K ∧
    between B P L ∧
    between C P M ∧
    K.onCircle Γ ∧
    L.onCircle Γ ∧
    M.onCircle Γ ∧
    TangentLineCircleAtPoint C O t Γ ∧
    S.onLine AB ∧
    S.onLine t ∧
    |(S─C)| = |(S─P)| →
    |(M─K)| = |(M─L)| := by
  euclid_intros
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points B L as BL
  euclid_apply line_from_points C M as CM
  euclid_apply line_from_points S K as SK
  euclid_apply line_from_points S L as SL
  euclid_apply line_from_points P K as PK
  euclid_apply line_from_points P L as PL
  euclid_apply line_from_points P M as PM
  euclid_apply line_from_points A P as AP
  euclid_apply line_from_points B P as BP
  euclid_apply line_from_points C P as CP
  euclid_apply line_from_points A B as AB_line

  have h_tan_AK : |(S─C)| * |(S─C)| = |(S─A)| * |(S─K)| := by
    euclid_apply TangentSecantTheorem S C A K O Γ t
    euclid_finish

  have h_tan_BL : |(S─C)| * |(S─C)| = |(S─B)| * |(S─L)| := by
    euclid_apply TangentSecantTheorem S C B L O Γ t
    euclid_finish

  have h_secants_S : |(S─A)| * |(S─K)| = |(S─B)| * |(S─L)| := by
    rw [← h_tan_AK, ← h_tan_BL]

  have h_SC_sq : |(S─P)| * |(S─P)| = |(S─A)| * |(S─K)| := by
    rw [← h_tan_AK]
    nlinarith

  have h_cyclic_AKCM : Cyclic A K C M := by
    euclid_finish

  have h_cyclic_BLCM : Cyclic B L C M := by
    euclid_finish

  have h_pow_P_AK_CM : |(P─A)| * |(P─K)| = |(P─C)| * |(P─M)| := by
    have hPAK : between A P K := by
      euclid_finish
    have hPCM : between C P M := by
      euclid_finish
    have h_coll_AKP : Coll A K P := by
      euclid_finish
    have h_coll_CMP : Coll C M P := by
      euclid_finish
    have h_four_AKCM : DistinctFourPoints A K C M := by
      euclid_finish
    euclid_apply IntersectingSecantsAndChordsTheorem A K C M P
    euclid_finish

  have h_pow_P_BL_CM : |(P─B)| * |(P─L)| = |(P─C)| * |(P─M)| := by
    have hPBL : between B P L := by
      euclid_finish
    have hPCM : between C P M := by
      euclid_finish
    have h_coll_BLP : Coll B L P := by
      euclid_finish
    have h_coll_CMP : Coll C M P := by
      euclid_finish
    have h_four_BLCM : DistinctFourPoints B L C M := by
      euclid_finish
    euclid_apply IntersectingSecantsAndChordsTheorem B L C M P
    euclid_finish

  have h_pow_P : |(P─A)| * |(P─K)| = |(P─B)| * |(P─L)| := by
    rw [h_pow_P_AK_CM, h_pow_P_BL_CM]

  have h_collinear_PK : Coll A P K := by
    have hPAK : between A P K := by
      euclid_finish
    euclid_finish

  have h_collinear_PL : Coll B P L := by
    have hPBL : between B P L := by
      euclid_finish
    euclid_finish

  have h_collinear_PM : Coll C P M := by
    have hPCM : between C P M := by
      euclid_finish
    euclid_finish

  have h_PK_sum : |(P─A)| + |(P─K)| = |(A─K)| := by
    have hPAK : between A P K := by
      euclid_finish
    euclid_finish

  have h_PL_sum : |(P─B)| + |(P─L)| = |(B─L)| := by
    have hPBL : between B P L := by
      euclid_finish
    euclid_finish

  have h_reduce : |(M─K)| = |(M─L)| := by
    have h_PK_pos : |(P─K)| > 0 := by
      euclid_finish
    have h_PL_pos : |(P─L)| > 0 := by
      euclid_finish
    have h_PM_pos : |(P─M)| > 0 := by
      euclid_finish
    have h_eq_products : |(P─A)| * |(P─K)| = |(P─B)| * |(P─L)| := by
      exact h_pow_P
    have h_line_AK : Coll A P K := by
      exact h_collinear_PK
    have h_line_BL : Coll B P L := by
      exact h_collinear_PL
    have h_line_CM : Coll C P M := by
      exact h_collinear_PM
    have h_cyc1 : Cyclic A K C M := by
      exact h_cyclic_AKCM
    have h_cyc2 : Cyclic B L C M := by
      exact h_cyclic_BLCM
    euclid_finish

  exact h_reduce
