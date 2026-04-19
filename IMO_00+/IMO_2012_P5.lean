import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABC$ be a Triangle with $\angle BCA=90^{\circ}$, and let $D$ be the Foot of the altitude from $C$. Let $X$ be a point in the interior of the segment $CD$. Let $K$ be the point on the segment $AX$ such that $BK=BC$. Similarly, let $L$ be the point on the segment $BX$ such that $AL=AC$. Let $M$ be the point of intersection of $AL$ and $BK$. Show that $MK=ML$.
theorem IMO_2012_P5 :
  ∀ (A B C D X K L M : Point) (AB BC CA AL BK : Line),
    formTriangle A B C AB BC CA ∧
    ∠ B:C:A = ∟ ∧
    Foot C D AB ∧
    between C X D ∧
    between A K X ∧
    |(B─K)| = |(B─C)| ∧
    between B L X ∧
    |(A─L)| = |(A─C)| ∧
    distinctPointsOnLine A L AL ∧
    distinctPointsOnLine B K BK ∧
    M.onLine AL ∧
    M.onLine BK →
    |(M─K)| = |(M─L)| := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A C as AC_line
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points B L as BL
  euclid_apply line_from_points K L as KL

  have h_right : ∠ B:C:A = ∟ := by
    euclid_finish

  have hD_foot : Foot C D AB := by
    euclid_finish

  have hD_on_AB : D.onLine AB := by
    euclid_finish

  have hCD_perp_AB : ∠ C:D:B = ∟ := by
    euclid_finish

  have hX_between : between C X D := by
    euclid_finish

  have hK_between : between A K X := by
    euclid_finish

  have hL_between : between B L X := by
    euclid_finish

  have hBK_eq_BC : |(B─K)| = |(B─C)| := by
    euclid_finish

  have hAL_eq_AC : |(A─L)| = |(A─C)| := by
    euclid_finish

  have hK_on_AX : K.onLine AK := by
    euclid_finish

  have hL_on_BX : L.onLine BL := by
    euclid_finish

  have hM_on_AL : M.onLine AL := by
    euclid_finish

  have hM_on_BK : M.onLine BK := by
    euclid_finish

  have hA_on_AC : A.onLine AC_line := by
    euclid_finish

  have hC_on_AC : C.onLine AC_line := by
    euclid_finish

  have hB_on_BC : B.onLine BC_line := by
    euclid_finish

  have hC_on_BC : C.onLine BC_line := by
    euclid_finish

  have h_cyclic : Cyclic A B K L := by
    have hBK_eq_BC : |(B─K)| = |(B─C)| := by
      exact hBK_eq_BC
    have hAL_eq_AC : |(A─L)| = |(A─C)| := by
      exact hAL_eq_AC
    have h_right' : ∠ B:C:A = ∟ := by
      exact h_right
    have hA_on_AC' : A.onLine AC_line := by
      exact hA_on_AC
    have hC_on_AC' : C.onLine AC_line := by
      exact hC_on_AC
    euclid_finish

  have hMK_eq_ML : |(M─K)| = |(M─L)| := by
    have h1 : M.onLine AL := by
      exact hM_on_AL
    have h2 : M.onLine BK := by
      exact hM_on_BK
    have h3 : Cyclic A B K L := by
      exact h_cyclic
    have h4 : ∠ B:C:A = ∟ := by
      exact h_right
    have h5 : D.onLine AB := by
      exact hD_on_AB
    euclid_finish

  exact hMK_eq_ML
