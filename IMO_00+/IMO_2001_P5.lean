import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABC$ be a Triangle with $\angle BAC = 60^{\circ}$. Let $AP$ bisect $\angle BAC$ and let $BQ$ bisect $\angle ABC$, with $P$ on $BC$ and $Q$ on $AC$. If $AB + BP = AQ + QB$, what are the angles of the triangle?
theorem IMO_2001_P5 :
  ∀ (A B C P Q : Point) (AB BC CA AP BQ : Line),
    formTriangle A B C AB BC CA ∧
    ∠ B:A:C = 2 / 3 * ∟ ∧
    distinctPointsOnLine A P AP ∧
    P.onLine BC ∧
    ∠ B:A:P = ∠ P:A:C ∧
    distinctPointsOnLine B Q BQ ∧
    Q.onLine CA ∧
    ∠ A:B:Q = ∠ Q:B:C ∧
    |(A─B)| + |(B─P)| = |(A─Q)| + |(Q─B)| →
    ∠ A:B:C = 8 / 9 * ∟ ∧ ∠ B:C:A = 4 / 9 * ∟ := by
  intro A B C P Q AB BC CA AP BQ h
  rcases h with
    ⟨h_form, h_angle_A, h_AP, hP_on_BC, h_bisector_AP,
      h_BQ, hQ_on_CA, h_bisector_BQ, h_len⟩

  euclid_apply rightAngle_eq_pi_div_two

  have h_tri_ABC : Triangle A B C := by
    euclid_finish

  have h_tri_BAC : Triangle B A C := by
    euclid_finish

  have h_coll_BPC : Coll B P C := by
    euclid_finish

  have h_coll_AQC : Coll A Q C := by
    euclid_finish

  have h_between_BPC : between B P C := by
    euclid_finish

  have h_between_AQC : between A Q C := by
    euclid_finish

  euclid_apply AngleBisectorTheorem A B C P
  euclid_apply AngleBisectorTheorem B A C Q
  euclid_apply triangle_angles_sum A B C

  have h_BP_ratio : |(A─C)| * |(B─P)| = |(A─B)| * |(C─P)| := by
    euclid_finish

  have h_AQ_ratio : |(B─C)| * |(A─Q)| = |(A─B)| * |(Q─C)| := by
    euclid_finish

  have h_BC_split : |(B─C)| = |(B─P)| + |(P─C)| := by
    euclid_finish

  have h_AC_split : |(A─C)| = |(A─Q)| + |(Q─C)| := by
    euclid_finish

  have h_AP_angle : ∠ B:A:P = 1 / 3 * ∟ := by
    euclid_finish

  have h_PA_angle : ∠ P:A:C = 1 / 3 * ∟ := by
    euclid_finish

  have h_CAB_angle : ∠ C:A:B = 2 / 3 * ∟ := by
    euclid_finish

  have h_BQ_split : ∠ A:B:C = ∠ A:B:Q + ∠ Q:B:C := by
    euclid_finish

  have h_BQ_double : ∠ A:B:Q + ∠ A:B:Q = ∠ A:B:C := by
    euclid_finish

  have h_ABQ_angle : ∠ A:B:Q = 4 / 9 * ∟ := by
    euclid_finish

  have h_QBC_angle : ∠ Q:B:C = 4 / 9 * ∟ := by
    euclid_finish

  have h_angle_sum : ∠ A:B:C + ∠ B:C:A = 4 / 3 * ∟ := by
    euclid_finish

  have h_ABC : ∠ A:B:C = 8 / 9 * ∟ := by
    euclid_finish

  have h_BCA : ∠ B:C:A = 4 / 9 * ∟ := by
    euclid_finish

  exact ⟨h_ABC, h_BCA⟩
