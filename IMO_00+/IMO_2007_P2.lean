import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Consider five points $A$, $B$, $C$, $D$ and $E$ such that $ABCD$ is a Parallelogram and $BCED$ is a Cyclic quadrilateral. Let $\ell$ be a line passing through $A$. Suppose that $\ell$ intersects the interior of the segment $DC$ at $F$ and intersects line $BC$ at $G$. Suppose also that $EF = EG = EC$. Prove that $\ell$ is the bisector of angle $DAB$.
theorem IMO_2007_P2 :
  ∀ (A B C D E F G : Point) (AB BC CD DA l CE ED DB : Line),
    Parallelogram A B C D AB BC CD DA ∧
    formQuadrilateral B C E D BC CE ED DB ∧
    Cyclic B C E D ∧
    A.onLine l ∧
    between D F C ∧ F.onLine l ∧
    G.onLine BC ∧ G.onLine l ∧
    |(E─F)| = |(E─G)| ∧ |(E─G)| = |(E─C)| →
    ∠ D:A:G = ∠ G:A:B := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A G as AG
  euclid_apply line_from_points E F as EF
  euclid_apply line_from_points E G as EG
  euclid_apply line_from_points E C as EC_line
  euclid_apply line_from_points B E as BE
  euclid_apply circle_from_points E C as ΩE

  have hE_center : E.isCentre ΩE := by
    euclid_finish

  have hC_on_ΩE : C.onCircle ΩE := by
    euclid_finish

  have hF_on_ΩE : F.onCircle ΩE := by
    have hEF_EC : |(E─F)| = |(E─C)| := by
      euclid_finish
    euclid_apply point_on_circle_if_to_rad F E ΩE
    euclid_finish

  have hG_on_ΩE : G.onCircle ΩE := by
    have hEG_EC : |(E─G)| = |(E─C)| := by
      euclid_finish
    euclid_apply point_on_circle_if_to_rad G E ΩE
    euclid_finish

  have hEF_eq_EG : |(E─F)| = |(E─G)| := by
    euclid_finish

  have hEG_eq_EC : |(E─G)| = |(E─C)| := by
    euclid_finish

  have h_collinear_DFC : Coll D F C := by
    euclid_finish

  have h_collinear_BGC : Coll B G C := by
    euclid_finish

  have hA_on_l : A.onLine l := by
    euclid_finish

  have hF_on_l : F.onLine l := by
    euclid_finish

  have hG_on_l : G.onLine l := by
    euclid_finish

  have h_parallel_angle1 : ∠ D:A:G = ∠ A:G:B := by
    euclid_finish

  have h_parallel_angle2 : ∠ G:A:B = ∠ A:G:F := by
    euclid_finish

  have h_eq_angle_FGC : ∠ G:F:C = ∠ F:C:G := by
    euclid_apply eq_sides_imp_eq_angles E F G
    euclid_finish

  have h_eq_angle_GCF : ∠ G:C:F = ∠ C:F:G := by
    euclid_apply eq_sides_imp_eq_angles E G C
    euclid_finish

  have h_bisector : ∠ D:A:G = ∠ G:A:B := by
    have h_len1 : |(E─F)| = |(E─G)| := by
      exact hEF_eq_EG
    have h_len2 : |(E─G)| = |(E─C)| := by
      exact hEG_eq_EC
    euclid_finish

  exact h_bisector
