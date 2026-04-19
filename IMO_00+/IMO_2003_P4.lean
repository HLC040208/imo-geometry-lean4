import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABCD$ be a Cyclic quadrilateral. Let $P$, $Q$, $R$ be the feet of the perpendiculars from $D$ to the lines $BC$, $CA$, $AB$, respectively. Show that $PQ=QR$ if and only if the bisectors of $\angle ABC$ and $\angle ADC$ are Concurrent with $AC$.
theorem IMO_2003_P4 :
  ∀ (A B C D P Q R X : Point) (BC CA AB CD DA : Line),
    Cyclic A B C D ∧
    formQuadrilateral A B C D AB BC CD DA ∧
    distinctPointsOnLine B C BC ∧
    distinctPointsOnLine C A CA ∧
    distinctPointsOnLine A B AB ∧
    Foot D P BC ∧
    Foot D Q CA ∧
    Foot D R AB →
    (|(P─Q)| = |(Q─R)| ↔ ∃ X : Point, X.onLine CA ∧ ∠ A:B:X = ∠ X:B:C ∧ ∠ A:D:X = ∠ X:D:C) := by
  intro A B C D P Q R X0 BC CA AB CD DA h
  rcases h with
    ⟨h_cyclic, h_form, hBC, hCA, hAB, hP_foot, hQ_foot, hR_foot⟩

  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points D P as DP
  euclid_apply line_from_points D Q as DQ
  euclid_apply line_from_points D R as DR
  euclid_apply line_from_points D B as DB

  have h_main_circle :
      ∃ Omega : Circle, A.onCircle Omega ∧ B.onCircle Omega ∧ C.onCircle Omega ∧ D.onCircle Omega := by
    exact cyclic_def A B C D h_cyclic
  rcases h_main_circle with ⟨Omega, hA_on_Omega, hB_on_Omega, hC_on_Omega, hD_on_Omega⟩

  have h_tri_ABC : Triangle A B C := by
    euclid_finish
  have h_tri_BAC : Triangle B A C := by
    euclid_finish
  have h_tri_DAB : Triangle D A B := by
    euclid_finish
  have h_tri_DCB : Triangle D C B := by
    euclid_finish
  have h_tri_DAC : Triangle D A C := by
    euclid_finish
  have h_tri_DQP : Triangle D Q P := by
    euclid_finish
  have h_tri_DQR : Triangle D Q R := by
    euclid_finish

  have hP_on_BC : P.onLine BC := by
    euclid_finish
  have hQ_on_CA : Q.onLine CA := by
    euclid_finish
  have hR_on_AB : R.onLine AB := by
    euclid_finish

  have h_coll_CPB : Coll C P B := by
    euclid_finish
  have h_coll_AQC : Coll A Q C := by
    euclid_finish
  have h_coll_ARB : Coll A R B := by
    euclid_finish

  have h_angle_DPC : ∠ D:P:C = ∟ := by
    euclid_finish
  have h_angle_DQC : ∠ D:Q:C = ∟ := by
    euclid_finish
  have h_angle_DQA : ∠ D:Q:A = ∟ := by
    euclid_finish
  have h_angle_DRA : ∠ D:R:A = ∟ := by
    euclid_finish

  have hD_neq_C : D ≠ C := by
    euclid_finish
  have hD_neq_A : D ≠ A := by
    euclid_finish

  euclid_apply exists_midpoint D C as O1
  euclid_apply circle_from_points O1 D as omega1
  have h_diam_DC : Diameter D C O1 omega1 := by
    euclid_finish
  have hP_on_omega1 : P.onCircle omega1 := by
    euclid_apply rightAngle_imp_diameter_onCircle D C P O1 omega1
    euclid_finish
  have hQ_on_omega1 : Q.onCircle omega1 := by
    euclid_apply rightAngle_imp_diameter_onCircle D C Q O1 omega1
    euclid_finish
  have hD_on_omega1 : D.onCircle omega1 := by
    euclid_finish
  have hC_on_omega1 : C.onCircle omega1 := by
    euclid_finish
  have h_cyclic_DQCP : Cyclic D Q C P := by
    exact ⟨omega1, hD_on_omega1, hQ_on_omega1, hC_on_omega1, hP_on_omega1⟩

  euclid_apply exists_midpoint D A as O2
  euclid_apply circle_from_points O2 D as omega2
  have h_diam_DA : Diameter D A O2 omega2 := by
    euclid_finish
  have hQ_on_omega2 : Q.onCircle omega2 := by
    euclid_apply rightAngle_imp_diameter_onCircle D A Q O2 omega2
    euclid_finish
  have hR_on_omega2 : R.onCircle omega2 := by
    euclid_apply rightAngle_imp_diameter_onCircle D A R O2 omega2
    euclid_finish
  have hD_on_omega2 : D.onCircle omega2 := by
    euclid_finish
  have hA_on_omega2 : A.onCircle omega2 := by
    euclid_finish
  have h_cyclic_DQAR : Cyclic D Q A R := by
    exact ⟨omega2, hD_on_omega2, hQ_on_omega2, hA_on_omega2, hR_on_omega2⟩

  have h_angle_DQP_DAB : ∠ D:Q:P = ∠ D:A:B := by
    euclid_finish
  have h_angle_QDP_ADB : ∠ Q:D:P = ∠ A:D:B := by
    euclid_finish
  have h_angle_DQR_DCB : ∠ D:Q:R = ∠ D:C:B := by
    euclid_finish
  have h_angle_QDR_CDB : ∠ Q:D:R = ∠ C:D:B := by
    euclid_finish

  have h_sim_DQP_DAB : SimilarTriangles D Q P D A B := by
    euclid_apply similar_AA D Q P D A B
    euclid_finish
  have h_sim_DQR_DCB : SimilarTriangles D Q R D C B := by
    euclid_apply similar_AA D Q R D C B
    euclid_finish

  have h_qp_rel : |(D─Q)| * |(A─B)| = |(Q─P)| * |(D─A)| := by
    euclid_finish
  have h_qr_rel : |(D─Q)| * |(B─C)| = |(Q─R)| * |(D─C)| := by
    euclid_finish

  have h_cross_iff :
      |(P─Q)| = |(Q─R)| ↔ |(A─B)| * |(D─C)| = |(B─C)| * |(D─A)| := by
    constructor
    · intro h_eq
      euclid_finish
    · intro h_cross
      euclid_finish

  constructor
  · intro h_eq
    have h_cross : |(A─B)| * |(D─C)| = |(B─C)| * |(D─A)| := by
      exact h_cross_iff.mp h_eq

    have h_exists_bisB :
        ∃ (LB : Line), B.onLine LB ∧
          (∀ (Y : Point), Y ≠ B → (Y.onLine LB ↔ ∠ A:B:Y = ∠ Y:B:C)) := by
      apply exists_angleBisector
      euclid_finish
    rcases h_exists_bisB with ⟨LB, hB_on_LB, hLB_char⟩

    have hYb_exists : ∃ Yb : Point, B ≠ Yb ∧ Yb.onLine LB := by
      exact exists_distincts_points_on_line LB B
    rcases hYb_exists with ⟨Yb, hB_neq_Yb, hYb_on_LB⟩

    have hYb_bis : ∠ A:B:Yb = ∠ Yb:B:C := by
      exact (hLB_char Yb hB_neq_Yb).mp hYb_on_LB
    have hYb_bis_left : ∠ Yb:B:A = ∠ Yb:B:C := by
      euclid_finish
    have hBYb : distinctPointsOnLine B Yb LB := by
      euclid_finish
    have hA_opp_C_LB : A.opposingSides C LB := by
      exact angleBisector_opposingSides B A C Yb LB ⟨hBYb, h_tri_BAC, hYb_bis_left⟩

    have hLB_inter_CA : LB.intersectsLine CA := by
      euclid_finish
    rcases intersection_lines LB CA hLB_inter_CA with ⟨Xb, hXb_on_LB, hXb_on_CA⟩

    have hXb_neq_B : Xb ≠ B := by
      euclid_finish
    have h_between_AXbC : between A Xb C := by
      euclid_finish
    have hXb_neq_D : Xb ≠ D := by
      euclid_finish
    have h_coll_AXbC : Coll A Xb C := by
      euclid_finish
    have h_bis_B : ∠ A:B:Xb = ∠ Xb:B:C := by
      exact (hLB_char Xb hXb_neq_B).mp hXb_on_LB

    euclid_apply AngleBisectorTheorem B A C Xb
    have h_ratio_B : |(B─C)| * |(A─Xb)| = |(B─A)| * |(C─Xb)| := by
      euclid_finish

    have h_ratio_D : |(D─C)| * |(A─Xb)| = |(D─A)| * |(C─Xb)| := by
      euclid_finish

    euclid_apply GeneralizedAngleBisectorTheorem D A C Xb
    euclid_apply triangle_angles_sum D A C
    have h_angle_split_D : ∠ C:D:Xb + ∠ Xb:D:A = ∠ C:D:A := by
      euclid_apply between_imp_angles_sum D A Xb C
      euclid_finish
    have h_sin_eq : sin (∠ Xb:D:A) = sin (∠ Xb:D:C) := by
      euclid_finish
    have h_bis_D_aux : ∠ Xb:D:A = ∠ Xb:D:C := by
      euclid_finish
    have h_bis_D : ∠ A:D:Xb = ∠ Xb:D:C := by
      euclid_finish

    exact ⟨Xb, hXb_on_CA, h_bis_B, h_bis_D⟩
  · intro h_exists
    rcases h_exists with ⟨X, hX_on_CA, h_bis_B, h_bis_D⟩

    have h_between_AXC : between A X C := by
      euclid_finish
    have h_coll_AXC : Coll A X C := by
      euclid_finish
    have h_bis_B_left : ∠ X:B:A = ∠ X:B:C := by
      euclid_finish
    have h_bis_D_left : ∠ X:D:A = ∠ X:D:C := by
      euclid_finish

    euclid_apply AngleBisectorTheorem B A C X
    euclid_apply AngleBisectorTheorem D A C X

    have h_ratio_B : |(B─C)| * |(A─X)| = |(B─A)| * |(C─X)| := by
      euclid_finish
    have h_ratio_D : |(D─C)| * |(A─X)| = |(D─A)| * |(C─X)| := by
      euclid_finish

    have h_cross : |(A─B)| * |(D─C)| = |(B─C)| * |(D─A)| := by
      euclid_finish

    exact h_cross_iff.mpr h_cross
