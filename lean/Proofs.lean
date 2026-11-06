import Statements
set_option maxRecDepth 100000

namespace PaperProofs

section
/-- Lemma lem:validity. -/
theorem lem_validity : PaperStatements.lem_validity :=
  @Lamps.rho_rel
end

section
universe u_1 u_2 u_3
/-- Theorem thm:criterion. -/
theorem thm_criterion : PaperStatements.thm_criterion.{u_1, u_2, u_3} :=
  @Lamps.counting_criterion_final.{u_1, u_2, u_3}
end

section
universe u_1 u_2 u_3
/-- Corollary cor:cyclic. -/
theorem cor_cyclic : PaperStatements.cor_cyclic.{u_1, u_2, u_3} :=
  @Lamps.cyclic_criterion_final.{u_1, u_2, u_3}
end

section
/-- Proposition prop:upper, model. -/
theorem prop_upper : PaperStatements.prop_upper :=
  @Lamps.prop_upper
end

section
/-- Proposition prop:upper, profile. -/
theorem prop_upper_profile : PaperStatements.prop_upper_profile :=
  @Lamps.prop_upper_profile
end

section
/-- Lemma lem:exchange. -/
theorem lem_exchange : PaperStatements.lem_exchange :=
  @Lamps.exchange_sem
end

section
/-- Lemma lem:local-filling. -/
theorem lem_local_filling : PaperStatements.lem_local_filling :=
  @Lamps.localIdsFamily
end

section
/-- Theorem thm:pair-area. -/
theorem thm_pair_area : PaperStatements.thm_pair_area :=
  @Lamps.pairAreaStatement
end

section
/-- Lemma lem:imp-s3round. -/
theorem lem_imp_s3round : PaperStatements.lem_imp_s3round :=
  @Lamps.unitaryS3Round
end

section
/-- Theorem thm:imp-phase. -/
theorem thm_imp_phase : PaperStatements.thm_imp_phase :=
  @Lamps.unitaryPhaseRobust
end

section
/-- Theorem A(a). -/
theorem theorem_A_a : PaperStatements.theorem_A_a :=
  @Lamps.theoremA_a_unconditional
end

section
/-- Theorem A(b), model. -/
theorem theorem_A_b : PaperStatements.theorem_A_b :=
  @Lamps.theoremA_b
end

section
/-- Theorem A(b), profile. -/
theorem theorem_A_b_profile : PaperStatements.theorem_A_b_profile :=
  @Lamps.theoremA_b_profile
end

section
/-- Theorem A(c). -/
theorem theorem_A_c : PaperStatements.theorem_A_c :=
  @Lamps.theoremA_c_unconditional
end

section
/-- Theorem A(d), amenability. -/
theorem theorem_A_d_amenability : PaperStatements.theorem_A_d_amenability :=
  @Lamps.Γ_elementaryAmenable
end

section
/-- Theorem A(a)-(d), combined. -/
theorem theorem_A : PaperStatements.theorem_A :=
  @Lamps.theoremA
end

section
universe u_1 u_2 u_3
/-- Theorem thm:sweep, conditional. -/
theorem thm_sweep : PaperStatements.thm_sweep.{u_1, u_2, u_3} :=
  @Lamps.sweep_criterion.{u_1, u_2, u_3}
end

end PaperProofs
