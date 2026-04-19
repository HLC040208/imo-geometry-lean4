import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABC$ be Triangle with incenter $I$. A point $P$ in the interior of the Triangle satisfies\[\angle PBA+\angle PCA = \angle PBC+\angle PCB.\]Show that $AP \geq AI$, and that equality holds if and only if $P=I$.
theorem IMO_2006_P1 :
  ∀ (A B C I P : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    Incentre I A B C ∧
    InsideTriangle P A B C AB BC CA ∧
    ∠ P:B:A + ∠ P:C:A = ∠ P:B:C + ∠ P:C:B →
    |(A─P)| ≥ |(A─I)| ∧ (|(A─P)| = |(A─I)| ↔ P = I) := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply circumcircle_from_points B I C as Ω
  euclid_apply line_from_points B P as BP
  euclid_apply line_from_points C P as CP
  euclid_apply line_from_points A I as AI
  euclid_apply line_from_points B I as BI
  euclid_apply line_from_points C I as CI

  have h_angle_I : ∠ B:I:C = (∠ A:B:C + ∠ A:C:B) / 2 + 2 * ∟ := by
    euclid_apply incentre_angle_property I A B C
    euclid_finish

  have hB_on_Ω : B.onCircle Ω := by
    euclid_finish

  have hI_on_Ω : I.onCircle Ω := by
    euclid_finish

  have hC_on_Ω : C.onCircle Ω := by
    euclid_finish

  have h_angle_P : ∠ B:P:C = (∠ A:B:C + ∠ A:C:B) / 2 + 2 * ∟ := by
    have h_inside : InsideTriangle P A B C AB BC CA := by
      euclid_finish
    euclid_finish

  have hP_on_Ω : P.onCircle Ω := by
    rw [h_angle_P] at h_angle_I
    euclid_finish

  have h_main : |(A─P)| ≥ |(A─I)| := by
    euclid_finish

  have h_eq_case : |(A─P)| = |(A─I)| ↔ P = I := by
    constructor
    · intro h_eq
      have hP_arc : P.onCircle Ω := by
        exact hP_on_Ω
      euclid_finish
    · intro h_PI
      rw [h_PI]

  exact ⟨h_main, h_eq_case⟩
