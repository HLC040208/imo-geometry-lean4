import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $H$ be the orthocenter of an acute-angled Triangle $ABC$. The circle $\Gamma_{A}$ centered at the MidPoint of $BC$ and passing through $H$ intersects the sideline $BC$ at points $A_{1}$ and $A_{2}$. Similarly, define the points $B_{1}$, $B_{2}$, $C_{1}$ and $C_{2}$. Prove that the six points $A_{1}$, $A_{2}$, $B_{1}$, $B_{2}$, $C_{1}$ and $C_{2}$ are concyclic.
theorem IMO_2008_P1 :
  ∀ (A B C H D E F A1 A2 B1 B2 C1 C2 MBC MCA MAB : Point) (AB BC CA : Line) (ΓA ΓB ΓC : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    Orthocentre H A B C D E F AB BC CA ∧
    MidPoint B MBC C ∧
    MBC.isCentre ΓA ∧
    H.onCircle ΓA ∧
    distinctPointsOnLine A1 A2 BC ∧
    A1.onCircle ΓA ∧
    A2.onCircle ΓA ∧
    MidPoint C MCA A ∧
    MCA.isCentre ΓB ∧
    H.onCircle ΓB ∧
    distinctPointsOnLine B1 B2 CA ∧
    B1.onCircle ΓB ∧
    B2.onCircle ΓB ∧
    MidPoint A MAB B ∧
    MAB.isCentre ΓC ∧
    H.onCircle ΓC ∧
    distinctPointsOnLine C1 C2 AB ∧
    C1.onCircle ΓC ∧
    C2.onCircle ΓC
  → ∃ (Ω : Circle), A1.onCircle Ω ∧ A2.onCircle Ω ∧ B1.onCircle Ω ∧ B2.onCircle Ω ∧ C1.onCircle Ω ∧ C2.onCircle Ω := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A H as AH
  euclid_apply line_from_points B H as BH
  euclid_apply line_from_points C H as CH
  euclid_apply line_from_points A1 B1 as A1B1
  euclid_apply line_from_points B1 C1 as B1C1
  euclid_apply line_from_points C1 A1 as C1A1

  have h_foot_A : Foot A D BC := by
    euclid_finish

  have h_foot_B : Foot B E CA := by
    euclid_finish

  have h_foot_C : Foot C F AB := by
    euclid_finish

  have h_BDC : between B D C := by
    euclid_apply acuteTriangle_foot_between A B C D BC
    euclid_finish

  have h_CEA : between C E A := by
    euclid_apply acuteTriangle_foot_between B C A E CA
    euclid_finish

  have h_AFB : between A F B := by
    euclid_apply acuteTriangle_foot_between C A B F AB
    euclid_finish

  have h_AH_HD : |(A─H)| * |(H─D)| = |(B─H)| * |(H─E)| := by
    euclid_apply acuteTriangle_power_of_orthocenter A B C D E F H AB BC CA
    euclid_finish

  have h_BH_HE : |(B─H)| * |(H─E)| = |(C─H)| * |(H─F)| := by
    euclid_apply acuteTriangle_power_of_orthocenter B C A E F D H BC CA AB
    euclid_finish

  have h_CH_HF : |(C─H)| * |(H─F)| = |(A─H)| * |(H─D)| := by
    euclid_apply acuteTriangle_power_of_orthocenter C A B F D E H CA AB BC
    euclid_finish

  have hA1_eq_H : |(MBC─A1)| = |(MBC─H)| := by
    have h_center_A : MBC.isCentre ΓA := by
      euclid_finish
    have hA1_on_GA : A1.onCircle ΓA := by
      euclid_finish
    have hH_on_GA : H.onCircle ΓA := by
      euclid_finish
    euclid_finish

  have hA2_eq_H : |(MBC─A2)| = |(MBC─H)| := by
    have h_center_A : MBC.isCentre ΓA := by
      euclid_finish
    have hA2_on_GA : A2.onCircle ΓA := by
      euclid_finish
    have hH_on_GA : H.onCircle ΓA := by
      euclid_finish
    euclid_finish

  have hB1_eq_H : |(MCA─B1)| = |(MCA─H)| := by
    have h_center_B : MCA.isCentre ΓB := by
      euclid_finish
    have hB1_on_GB : B1.onCircle ΓB := by
      euclid_finish
    have hH_on_GB : H.onCircle ΓB := by
      euclid_finish
    euclid_finish

  have hB2_eq_H : |(MCA─B2)| = |(MCA─H)| := by
    have h_center_B : MCA.isCentre ΓB := by
      euclid_finish
    have hB2_on_GB : B2.onCircle ΓB := by
      euclid_finish
    have hH_on_GB : H.onCircle ΓB := by
      euclid_finish
    euclid_finish

  have hC1_eq_H : |(MAB─C1)| = |(MAB─H)| := by
    have h_center_C : MAB.isCentre ΓC := by
      euclid_finish
    have hC1_on_GC : C1.onCircle ΓC := by
      euclid_finish
    have hH_on_GC : H.onCircle ΓC := by
      euclid_finish
    euclid_finish

  have hC2_eq_H : |(MAB─C2)| = |(MAB─H)| := by
    have h_center_C : MAB.isCentre ΓC := by
      euclid_finish
    have hC2_on_GC : C2.onCircle ΓC := by
      euclid_finish
    have hH_on_GC : H.onCircle ΓC := by
      euclid_finish
    euclid_finish

  have hA1_ne_B1 : A1 ≠ B1 := by
    euclid_finish

  have hA1_ne_C1 : A1 ≠ C1 := by
    euclid_finish

  euclid_apply circumcircle_from_points A1 B1 C1 as Ω

  have hA1_on_Ω : A1.onCircle Ω := by
    euclid_finish

  have hB1_on_Ω : B1.onCircle Ω := by
    euclid_finish

  have hC1_on_Ω : C1.onCircle Ω := by
    euclid_finish

  have hA2_on_Ω : A2.onCircle Ω := by
    have h_line_A : distinctPointsOnLine A1 A2 BC := by
      euclid_finish
    have h_radius_A1 : |(MBC─A1)| = |(MBC─H)| := by
      exact hA1_eq_H
    have h_radius_A2 : |(MBC─A2)| = |(MBC─H)| := by
      exact hA2_eq_H
    euclid_finish

  have hB2_on_Ω : B2.onCircle Ω := by
    have h_line_B : distinctPointsOnLine B1 B2 CA := by
      euclid_finish
    have h_radius_B1 : |(MCA─B1)| = |(MCA─H)| := by
      exact hB1_eq_H
    have h_radius_B2 : |(MCA─B2)| = |(MCA─H)| := by
      exact hB2_eq_H
    euclid_finish

  have hC2_on_Ω : C2.onCircle Ω := by
    have h_line_C : distinctPointsOnLine C1 C2 AB := by
      euclid_finish
    have h_radius_C1 : |(MAB─C1)| = |(MAB─H)| := by
      exact hC1_eq_H
    have h_radius_C2 : |(MAB─C2)| = |(MAB─H)| := by
      exact hC2_eq_H
    euclid_finish

  use Ω
  exact ⟨hA1_on_Ω, hA2_on_Ω, hB1_on_Ω, hB2_on_Ω, hC1_on_Ω, hC2_on_Ω⟩
