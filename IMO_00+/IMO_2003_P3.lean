import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Each pair of opposite sides of a convex hexagon has the following property: the distance between their midpoints is equal to $\dfrac{\sqrt{3}}{2}$ times the sum of their lengths. Prove that all the angles of the hexagon are equal.
theorem IMO_2003_P3 :
  ∀ (A B C D E F M1 M2 M3 M4 M5 M6 : Point)
    (AB BC CD DE EF FA : Line),
    distinctPointsOnLine A B AB ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine C D CD ∧
    distinctPointsOnLine D E DE ∧ distinctPointsOnLine E F EF ∧ distinctPointsOnLine F A FA ∧
    F.sameSide A DE ∧ A.sameSide B DE ∧ B.sameSide C DE ∧
    A.sameSide B EF ∧ B.sameSide C EF ∧ C.sameSide D EF ∧
    B.sameSide C FA ∧ C.sameSide D FA ∧ D.sameSide E FA ∧
    C.sameSide D AB ∧ D.sameSide E AB ∧ E.sameSide F AB ∧
    D.sameSide E BC ∧ E.sameSide F BC ∧ F.sameSide A BC ∧
    E.sameSide F CD ∧ F.sameSide A CD ∧ A.sameSide B CD ∧
    MidPoint A M1 B ∧ MidPoint D M2 E ∧ |(M1─M2)| = (√3 / 2) * (|(A─B)| + |(D─E)|) ∧
    MidPoint B M3 C ∧ MidPoint E M4 F ∧ |(M3─M4)| = (√3 / 2) * (|(B─C)| + |(E─F)|) ∧
    MidPoint C M5 D ∧ MidPoint F M6 A ∧ |(M5─M6)| = (√3 / 2) * (|(C─D)| + |(F─A)|) →
    ∠ F:A:B = ∠ A:B:C ∧
    ∠ A:B:C = ∠ B:C:D ∧
    ∠ B:C:D = ∠ C:D:E ∧
    ∠ C:D:E = ∠ D:E:F ∧
    ∠ D:E:F = ∠ E:F:A := by
  intro A B C D E F M1 M2 M3 M4 M5 M6 AB BC CD DE EF FA h
  rcases h with
    ⟨hAB, hBC, hCD, hDE, hEF, hFA,
      h_F_A_DE, h_A_B_DE, h_B_C_DE,
      h_A_B_EF, h_B_C_EF, h_C_D_EF,
      h_B_C_FA, h_C_D_FA, h_D_E_FA,
      h_C_D_AB, h_D_E_AB, h_E_F_AB,
      h_D_E_BC, h_E_F_BC, h_F_A_BC,
      h_E_F_CD, h_F_A_CD, h_A_B_CD,
      h_mid1, h_mid2, h_len1,
      h_mid3, h_mid4, h_len2,
      h_mid5, h_mid6, h_len3⟩

  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points A E as AE
  euclid_apply line_from_points M1 M2 as M12
  euclid_apply line_from_points M3 M4 as M34
  euclid_apply line_from_points M5 M6 as M56

  have h_tri_FAB : Triangle F A B := by
    euclid_finish

  have h_tri_ABC : Triangle A B C := by
    euclid_finish

  have h_tri_BCD : Triangle B C D := by
    euclid_finish

  have h_tri_CDE : Triangle C D E := by
    euclid_finish

  have h_tri_DEF : Triangle D E F := by
    euclid_finish

  have h_tri_EFA : Triangle E F A := by
    euclid_finish

  have h_sum_FAB : ∠ F:A:B + ∠ A:B:F + ∠ B:F:A = ∟ + ∟ := by
    euclid_apply triangle_angles_sum F A B
    euclid_finish

  have h_sum_ABC : ∠ A:B:C + ∠ B:C:A + ∠ C:A:B = ∟ + ∟ := by
    euclid_apply triangle_angles_sum A B C
    euclid_finish

  have h_sum_BCD : ∠ B:C:D + ∠ C:D:B + ∠ D:B:C = ∟ + ∟ := by
    euclid_apply triangle_angles_sum B C D
    euclid_finish

  have h_sum_CDE : ∠ C:D:E + ∠ D:E:C + ∠ E:C:D = ∟ + ∟ := by
    euclid_apply triangle_angles_sum C D E
    euclid_finish

  have h_sum_DEF : ∠ D:E:F + ∠ E:F:D + ∠ F:D:E = ∟ + ∟ := by
    euclid_apply triangle_angles_sum D E F
    euclid_finish

  have h_sum_EFA : ∠ E:F:A + ∠ F:A:E + ∠ A:E:F = ∟ + ∟ := by
    euclid_apply triangle_angles_sum E F A
    euclid_finish

  have h_AB_half : |(A─B)| * (1 / 2 : ℝ) = |(M1─B)| := by
    euclid_apply midpoint_half_len A B M1
    euclid_finish

  have h_DE_half : |(D─E)| * (1 / 2 : ℝ) = |(M2─E)| := by
    euclid_apply midpoint_half_len D E M2
    euclid_finish

  have h_BC_half : |(B─C)| * (1 / 2 : ℝ) = |(M3─C)| := by
    euclid_apply midpoint_half_len B C M3
    euclid_finish

  have h_EF_half : |(E─F)| * (1 / 2 : ℝ) = |(M4─F)| := by
    euclid_apply midpoint_half_len E F M4
    euclid_finish

  have h_CD_half : |(C─D)| * (1 / 2 : ℝ) = |(M5─D)| := by
    euclid_apply midpoint_half_len C D M5
    euclid_finish

  have h_FA_half : |(F─A)| * (1 / 2 : ℝ) = |(M6─A)| := by
    euclid_apply midpoint_half_len F A M6
    euclid_finish

  have h_AM1_eq_M1B : |(A─M1)| = |(M1─B)| := by
    euclid_finish

  have h_DM2_eq_M2E : |(D─M2)| = |(M2─E)| := by
    euclid_finish

  have h_BM3_eq_M3C : |(B─M3)| = |(M3─C)| := by
    euclid_finish

  have h_EM4_eq_M4F : |(E─M4)| = |(M4─F)| := by
    euclid_finish

  have h_CM5_eq_M5D : |(C─M5)| = |(M5─D)| := by
    euclid_finish

  have h_FM6_eq_M6A : |(F─M6)| = |(M6─A)| := by
    euclid_finish

  have h_len1_mid :
      |(M1─M2)| = √3 * (|(M1─B)| + |(M2─E)|) := by
    euclid_finish

  have h_len2_mid :
      |(M3─M4)| = √3 * (|(M3─C)| + |(M4─F)|) := by
    euclid_finish

  have h_len3_mid :
      |(M5─M6)| = √3 * (|(M5─D)| + |(M6─A)|) := by
    euclid_finish

  have h1 : ∠ F:A:B = ∠ A:B:C := by
    euclid_finish

  have h2 : ∠ A:B:C = ∠ B:C:D := by
    euclid_finish

  have h3 : ∠ B:C:D = ∠ C:D:E := by
    euclid_finish

  have h4 : ∠ C:D:E = ∠ D:E:F := by
    euclid_finish

  have h5 : ∠ D:E:F = ∠ E:F:A := by
    euclid_finish

  exact ⟨h1, h2, h3, h4, h5⟩
