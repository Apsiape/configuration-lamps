import Proofs
set_option maxRecDepth 100000

/-! Frozen exact-type checks and axiom audit of every headline. -/

-- Lemma lem:validity
#check (@Lamps.rho_rel : PaperStatements.lem_validity)
#print axioms Lamps.rho_rel
#print axioms PaperProofs.lem_validity

-- Theorem thm:criterion
#check (@Lamps.counting_criterion_final : PaperStatements.thm_criterion)
#print axioms Lamps.counting_criterion_final
#print axioms PaperProofs.thm_criterion

-- Corollary cor:cyclic
#check (@Lamps.cyclic_criterion_final : PaperStatements.cor_cyclic)
#print axioms Lamps.cyclic_criterion_final
#print axioms PaperProofs.cor_cyclic

-- Proposition prop:upper, model
#check (@Lamps.prop_upper : PaperStatements.prop_upper)
#print axioms Lamps.prop_upper
#print axioms PaperProofs.prop_upper

-- Proposition prop:upper, profile
#check (@Lamps.prop_upper_profile : PaperStatements.prop_upper_profile)
#print axioms Lamps.prop_upper_profile
#print axioms PaperProofs.prop_upper_profile

-- Lemma lem:exchange
#check (@Lamps.exchange_sem : PaperStatements.lem_exchange)
#print axioms Lamps.exchange_sem
#print axioms PaperProofs.lem_exchange

-- Lemma lem:local-filling
#check (@Lamps.localIdsFamily : PaperStatements.lem_local_filling)
#print axioms Lamps.localIdsFamily
#print axioms PaperProofs.lem_local_filling

-- Theorem thm:pair-area
#check (@Lamps.pairAreaStatement : PaperStatements.thm_pair_area)
#print axioms Lamps.pairAreaStatement
#print axioms PaperProofs.thm_pair_area

-- Lemma lem:imp-s3round
#check (@Lamps.unitaryS3Round : PaperStatements.lem_imp_s3round)
#print axioms Lamps.unitaryS3Round
#print axioms PaperProofs.lem_imp_s3round

-- Theorem thm:imp-phase
#check (@Lamps.unitaryPhaseRobust : PaperStatements.thm_imp_phase)
#print axioms Lamps.unitaryPhaseRobust
#print axioms PaperProofs.thm_imp_phase

-- Theorem A(a)
#check (@Lamps.theoremA_a_unconditional : PaperStatements.theorem_A_a)
#print axioms Lamps.theoremA_a_unconditional
#print axioms PaperProofs.theorem_A_a

-- Theorem A(b), model
#check (@Lamps.theoremA_b : PaperStatements.theorem_A_b)
#print axioms Lamps.theoremA_b
#print axioms PaperProofs.theorem_A_b

-- Theorem A(b), profile
#check (@Lamps.theoremA_b_profile : PaperStatements.theorem_A_b_profile)
#print axioms Lamps.theoremA_b_profile
#print axioms PaperProofs.theorem_A_b_profile

-- Theorem A(c)
#check (@Lamps.theoremA_c_unconditional : PaperStatements.theorem_A_c)
#print axioms Lamps.theoremA_c_unconditional
#print axioms PaperProofs.theorem_A_c

-- Theorem A(d), amenability
#check (@Lamps.Γ_elementaryAmenable : PaperStatements.theorem_A_d_amenability)
#print axioms Lamps.Γ_elementaryAmenable
#print axioms PaperProofs.theorem_A_d_amenability

-- Theorem A(a)-(d), combined
#check (@Lamps.theoremA : PaperStatements.theorem_A)
#print axioms Lamps.theoremA
#print axioms PaperProofs.theorem_A

-- Theorem thm:sweep, conditional
#check (@Lamps.sweep_criterion : PaperStatements.thm_sweep)
#print axioms Lamps.sweep_criterion
#print axioms PaperProofs.thm_sweep
