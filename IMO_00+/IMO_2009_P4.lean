import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABC$ be a Triangle with $AB = AC$. The angle bisectors of $\angle CAB$ and $\angle ABC$ meet the sides $BC$ and $CA$ at $D$ and $E$, respectively. Let $K$ be the incentre of Triangle $ADC$. Suppose that $\angle BEK = 45^\circ$. Find all possible values of $\angle CAB$.
theorem IMO_2009_P4 :
  ∀ (A B C D E K : Point) (AB BC CA AD DC : Line),
    formTriangle A B C AB BC CA ∧ |(A─B)| = |(A─C)| ∧
    between B D C ∧ ∠ C:A:D = ∠ D:A:B ∧
    between C E A ∧ ∠ A:B:E = ∠ E:B:C ∧
    formTriangle A D C AD DC CA ∧ Incentre K A D C ∧
    ∠ B:E:K = ∟/2 →
    (∠ C:A:B = ∟) ∨ (∠ C:A:B = 2/3 * ∟) := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points B E as BE
  euclid_apply line_from_points E K as EK
  euclid_apply line_from_points C K as CK
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points D K as DK
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points A C as AC_line

  have h_iso_base : ∠ A:B:C = ∠ B:C:A := by
    have h_iso : IsoTriangle A B C := by
      euclid_finish
    euclid_finish

  have h_ADC_right : ∠ A:D:C = ∟ := by
    have h_collinear_BDC : Coll B D C := by
      euclid_finish
    have h_angle_BAD : ∠ C:A:D = ∠ D:A:B := by
      euclid_finish
    euclid_apply triangle_angles_sum A D C
    euclid_finish

  have h_CEK : ∠ C:E:K = 3/4 * ∠ C:A:B := by
    have h_BEC : ∠ B:E:C = ∟/2 + 3/4 * ∠ C:A:B := by
      have h_collinear_CEA : Coll C E A := by
        euclid_finish
      have h_BEK : ∠ B:E:K = ∟/2 := by
        euclid_finish
      euclid_apply triangle_angles_sum B E C
      euclid_finish
    have h_collinear_CEA : Coll C E A := by
      euclid_finish
    euclid_finish

  have h_ECK : ∠ E:C:K = ∟/2 - (∠ C:A:B) / 4 := by
    have h_incentre_C : ∠ A:C:K = ∠ K:C:D := by
      euclid_apply incentre_angle_property K A D C
      euclid_finish
    have h_collinear_BDC : Coll B D C := by
      euclid_finish
    have h_collinear_CEA : Coll C E A := by
      euclid_finish
    euclid_finish

  have h_AKE : ∠ A:K:E = (∠ C:A:B) / 2 := by
    have h_AEK : ∠ A:E:K = ∟ + ∟ - 3/4 * ∠ C:A:B := by
      have h_collinear_CEA : Coll C E A := by
        euclid_finish
      have h_CEK_val : ∠ C:E:K = 3/4 * ∠ C:A:B := by
        exact h_CEK
      euclid_finish
    have h_tri_AEK : Triangle A E K := by
      euclid_finish
    euclid_apply triangle_angles_sum A E K
    euclid_finish

  have h_AE_CE_from_bisector : |(A─E)| / |(E─C)| = 1 / (2 * Real.sin ((∠ C:A:B) / 2)) := by
    have h_BE_bisector : ∠ A:B:E = ∠ E:B:C := by
      euclid_finish
    have h_collinear_CEA : Coll C E A := by
      euclid_finish
    have h_iso : IsoTriangle A B C := by
      euclid_finish
    euclid_finish

  have h_AE_CE_from_sines :
      |(A─E)| / |(E─C)|
        = (Real.sin ((∠ C:A:B) / 2) * Real.sin (∟/2 - (∠ C:A:B) / 4))
            / (Real.sin ((∠ C:A:B) / 4) * Real.sin (3 * ∟/2 - (∠ C:A:B) / 2)) := by
    have h_tri_AEK : Triangle A E K := by
      euclid_finish
    have h_tri_CEK : Triangle C E K := by
      euclid_finish
    euclid_apply LawOfSines A E K
    euclid_apply LawOfSines C E K
    euclid_finish

  have h_trig :
      2 * Real.sin ((∠ C:A:B) / 2) * Real.sin ((∠ C:A:B) / 2) *
          Real.sin (∟/2 - (∠ C:A:B) / 4)
        = Real.sin ((∠ C:A:B) / 4) * Real.sin (3 * ∟/2 - (∠ C:A:B) / 2) := by
    rw [h_AE_CE_from_bisector] at h_AE_CE_from_sines
    euclid_finish

  have h_cases : (∠ C:A:B = ∟) ∨ (∠ C:A:B = 2/3 * ∟) := by
    have hA_pos : ∠ C:A:B > 0 := by
      euclid_finish
    have hA_lt_straight : ∠ C:A:B < ∟ + ∟ := by
      euclid_finish
    euclid_finish

  exact h_cases
