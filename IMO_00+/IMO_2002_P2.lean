import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--The circle $S$ has centre $O$, and $BC$ is a Diameter of $S$. Let $A$ be a point of $S$ such that $\angle AOB<120{{}^\circ}$. Let $D$ be the MidPoint of the arc $AB$ which does not contain $C$. The line through $O$ parallel to $DA$ meets the line $AC$ at $I$. The perpendicular bisector of $OA$ meets $S$ at $E$ and at $F$. Prove that $I$ is the incentre of the Triangle $CEF$.
theorem IMO_2002_P2 :
  ∀ (A B C D E F I O : Point) (S : Circle) (AB DA AC L1 L2 : Line),
    O.isCentre S ∧
    B.onCircle S ∧
    C.onCircle S ∧
    A.onCircle S ∧
    Diameter B C O S ∧
    ∠ A:O:B < 4 / 3 * ∟ ∧
    D.onCircle S ∧
    ∠ A:O:D = ∠ D:O:B ∧
    distinctPointsOnLine A B AB ∧
    D.opposingSides C AB ∧
    distinctPointsOnLine D A DA ∧
    distinctPointsOnLine A C AC ∧
    O.onLine L1 ∧
    ¬ L1.intersectsLine DA ∧
    TwoLinesIntersectAtPoint L1 AC I ∧
    PerpBisector O A L2 ∧
    E.onLine L2 ∧
    E.onCircle S ∧
    F.onLine L2 ∧
    F.onCircle S →
    Incentre I C E F := by
  intro A B C D E F I O S AB DA AC L1 L2 h
  rcases h with
    ⟨hO_center, hB_on_S, hC_on_S, hA_on_S, h_diam, h_angle_lt,
      hD_on_S, h_arc_mid, hAB, hD_oppo_C_AB, hDA, hAC,
      hO_on_L1, hL1_not_DA, hI, h_perp_bis, hE_on_L2, hE_on_S, hF_on_L2, hF_on_S⟩

  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points O A as OA
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O D as OD

  have hI_on_L1 : I.onLine L1 := by
    euclid_finish

  have hI_on_AC : I.onLine AC := by
    euclid_finish

  have h_tri_CEF : Triangle C E F := by
    euclid_finish

  euclid_apply triangle_angles_sum C E F

  have hEO_eq_EA : |(E─O)| = |(E─A)| := by
    euclid_apply perpBisector_imp_eq_dist O A L2
    euclid_finish

  have hFO_eq_FA : |(F─O)| = |(F─A)| := by
    euclid_apply perpBisector_imp_eq_dist O A L2
    euclid_finish

  have hOA_eq_OB : |(O─A)| = |(O─B)| := by
    euclid_finish

  have hOD_eq_OB : |(O─D)| = |(O─B)| := by
    euclid_finish

  have hEO_eq_OA : |(E─O)| = |(O─A)| := by
    euclid_finish

  have hFO_eq_OA : |(F─O)| = |(O─A)| := by
    euclid_finish

  have hEA_eq_AF : |(E─A)| = |(A─F)| := by
    euclid_finish

  have hEOA_eq_AOF : ∠ E:O:A = ∠ A:O:F := by
    euclid_apply eq_centralAngles_if_eq_chords E A A F O S
    euclid_finish

  have hDOA_eq_DOB : ∠ D:O:A = ∠ D:O:B := by
    euclid_finish

  have hAD_eq_DB : |(A─D)| = |(D─B)| := by
    euclid_apply congruentTriangles_SAS D O A D O B
    euclid_finish

  have h_ECA_eq_ACF_or :
      ∠ E:C:A = ∠ A:C:F ∨ ∠ E:C:A + ∠ A:C:F = ∟ + ∟ := by
    euclid_apply eq_chords_eq_or_supp_inscribedAngles E C A A C F S
    euclid_finish

  have h_ECA_eq_ACF : ∠ E:C:A = ∠ A:C:F := by
    euclid_finish

  have h_ACD_eq_DCB_or :
      ∠ A:C:D = ∠ D:C:B ∨ ∠ A:C:D + ∠ D:C:B = ∟ + ∟ := by
    euclid_apply eq_chords_eq_or_supp_inscribedAngles A C D D C B S
    euclid_finish

  have h_ACD_eq_DCB : ∠ A:C:D = ∠ D:C:B := by
    euclid_finish

  have h_CIO_eq_CAD : ∠ C:I:O = ∠ C:A:D := by
    euclid_finish

  have h_OIC_eq_ADC : ∠ O:I:C = ∠ A:D:C := by
    euclid_finish

  have h_C_bis : ∠ I:C:E = ∠ I:C:F := by
    euclid_finish

  have h_F_bis : ∠ I:F:C = ∠ I:F:E := by
    euclid_finish

  have h_E_bis : ∠ I:E:C = ∠ I:E:F := by
    euclid_finish

  exact ⟨h_C_bis, h_F_bis, h_E_bis⟩
