import Lamps
set_option autoImplicit false
set_option maxRecDepth 100000

namespace PaperStatements

section
/-- Lemma lem:validity. Original: `Lamps.rho_rel`. -/
def lem_validity : Prop :=
  ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))),
  @Eq.{1} (Equiv.Perm.{1} Lamps.X)
    (@DFunLike.coe.{1, 1, 1}
      (@MonoidHom.{0, 0} Lamps.F (Equiv.Perm.{1} Lamps.X)
        (@MulOneClass.toMulOne.{0} Lamps.F
          (@Monoid.toMulOneClass.{0} Lamps.F
            (@DivInvMonoid.toMonoid.{0} Lamps.F
              (@Group.toDivInvMonoid.{0} Lamps.F
                (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
        (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Lamps.X)
          (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Lamps.X)
            (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Lamps.X)
              (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))))))
      Lamps.F (fun (x : Lamps.F) => Equiv.Perm.{1} Lamps.X)
      (@MonoidHom.instFunLike.{0, 0} Lamps.F (Equiv.Perm.{1} Lamps.X)
        (@MulOneClass.toMulOne.{0} Lamps.F
          (@Monoid.toMulOneClass.{0} Lamps.F
            (@DivInvMonoid.toMonoid.{0} Lamps.F
              (@Group.toDivInvMonoid.{0} Lamps.F
                (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
        (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Lamps.X)
          (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Lamps.X)
            (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Lamps.X)
              (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))))))
      Lamps.ρΓ (Lamps.rel i))
    (@OfNat.ofNat.{0} (Equiv.Perm.{1} Lamps.X) (nat_lit 1)
      (@One.toOfNat1.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.instOne.{0} Lamps.X)))
end

section
universe u_1 u_2 u_3
/-- Theorem thm:criterion. Original: `Lamps.counting_criterion_final`. -/
def thm_criterion : Prop :=
  ∀ {G : Type u_1} [inst : Group.{u_1} G] {S : Type u_2} {ι : Type u_3} [inst_1 : DecidableEq.{u_2 + 1} S]
  [inst_2 : Fintype.{u_2} S] [inst_3 : Fintype.{u_3} ι]
  (π :
    @MonoidHom.{u_2, u_1} (FreeGroup.{u_2} S) G
      (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
        (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
          (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
            (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
      (@MulOneClass.toMulOne.{u_1} G
        (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
  (R : ι → FreeGroup.{u_2} S) (a b : S) (ia ib iab : ι)
  (hRa :
    @Eq.{u_2 + 1} (FreeGroup.{u_2} S) (R ia)
      (@HPow.hPow.{u_2, 0, u_2} (FreeGroup.{u_2} S) Nat (FreeGroup.{u_2} S)
        (@instHPow.{u_2, 0} (FreeGroup.{u_2} S) Nat
          (@NPow.toPow.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toNPow.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S))))))
        (@FreeGroup.of.{u_2} S a) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hRb :
    @Eq.{u_2 + 1} (FreeGroup.{u_2} S) (R ib)
      (@HPow.hPow.{u_2, 0, u_2} (FreeGroup.{u_2} S) Nat (FreeGroup.{u_2} S)
        (@instHPow.{u_2, 0} (FreeGroup.{u_2} S) Nat
          (@NPow.toPow.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toNPow.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S))))))
        (@FreeGroup.of.{u_2} S b) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hRab :
    @Eq.{u_2 + 1} (FreeGroup.{u_2} S) (R iab)
      (@HPow.hPow.{u_2, 0, u_2} (FreeGroup.{u_2} S) Nat (FreeGroup.{u_2} S)
        (@instHPow.{u_2, 0} (FreeGroup.{u_2} S) Nat
          (@NPow.toPow.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toNPow.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S))))))
        (@HMul.hMul.{u_2, u_2, u_2} (FreeGroup.{u_2} S) (FreeGroup.{u_2} S) (FreeGroup.{u_2} S)
          (@instHMul.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instMul.{u_2} S)) (@FreeGroup.of.{u_2} S a)
          (@FreeGroup.of.{u_2} S b))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (hR1 :
    ∀ (k : ι),
      @Eq.{u_1 + 1} G
        (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1}
          (@MonoidHom.{u_2, u_1} (FreeGroup.{u_2} S) G
            (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
              (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
                (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                  (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
            (@MulOneClass.toMulOne.{u_1} G
              (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
          (FreeGroup.{u_2} S) (fun (x : FreeGroup.{u_2} S) => G)
          (@MonoidHom.instFunLike.{u_2, u_1} (FreeGroup.{u_2} S) G
            (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
              (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
                (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                  (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
            (@MulOneClass.toMulOne.{u_1} G
              (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
          π (R k))
        (@OfNat.ofNat.{u_1} G (nat_lit 1)
          (@One.toOfNat1.{u_1} G
            (@InvOneClass.toOne.{u_1} G
              (@DivInvOneMonoid.toInvOneClass.{u_1} G
                (@DivisionMonoid.toDivInvOneMonoid.{u_1} G (@Group.toDivisionMonoid.{u_1} G inst)))))))
  (hab1 :
    @Ne.{u_1 + 1} G
      (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1}
        (@MonoidHom.{u_2, u_1} (FreeGroup.{u_2} S) G
          (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
        (FreeGroup.{u_2} S) (fun (x : FreeGroup.{u_2} S) => G)
        (@MonoidHom.instFunLike.{u_2, u_1} (FreeGroup.{u_2} S) G
          (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
        π
        (@HMul.hMul.{u_2, u_2, u_2} (FreeGroup.{u_2} S) (FreeGroup.{u_2} S) (FreeGroup.{u_2} S)
          (@instHMul.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instMul.{u_2} S)) (@FreeGroup.of.{u_2} S a)
          (@FreeGroup.of.{u_2} S b)))
      (@OfNat.ofNat.{u_1} G (nat_lit 1)
        (@One.toOfNat1.{u_1} G
          (@InvOneClass.toOne.{u_1} G
            (@DivInvOneMonoid.toInvOneClass.{u_1} G
              (@DivisionMonoid.toDivInvOneMonoid.{u_1} G (@Group.toDivisionMonoid.{u_1} G inst)))))))
  {N : Nat} (w : Fin N → FreeGroup.{u_2} S) (Λ : Nat)
  (hΛ : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Λ)
  (hw : @Lamps.TransportAreaLE.{u_2, u_3} S ι R a b N w Λ) (r : Real)
  (hr :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 10)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@Nat.cast.{0} Real Real.instNatCast N))
          (@Nat.cast.{0} Real Real.instNatCast Λ))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast (@Lamps.maxLen.{u_2, u_3} S ι inst_1 inst_3 R)))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      r),
  And
    (∀ (n : Nat),
      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
          (@Houghton.modelSizes.{u_1} G inst
            (@Lamps.criterionChunk.{u_1, u_2, u_3} G inst S ι inst_1 inst_2 inst_3 π R a b) r)
          n →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast n)))
    (∀ (m : Nat),
      @Eq.{1} ENat
          (@Houghton.profile.{u_1} G inst
            (@Lamps.criterionChunk.{u_1, u_2, u_3} G inst S ι inst_1 inst_2 inst_3 π R a b) r)
          (@Nat.cast.{0} ENat ENat.instNatCast m) →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast m)))
end

section
universe u_1 u_2 u_3
/-- Corollary cor:cyclic. Original: `Lamps.cyclic_criterion_final`. -/
def cor_cyclic : Prop :=
  ∀ {S : Type u_1} {ι : Type u_2} {G : Type u_3} [inst : Group.{u_3} G] [inst_1 : DecidableEq.{u_1 + 1} S]
  [inst_2 : Fintype.{u_1} S] [inst_3 : Fintype.{u_2} ι]
  (π :
    @MonoidHom.{u_1, u_3} (FreeGroup.{u_1} S) G
      (@MulOneClass.toMulOne.{u_1} (FreeGroup.{u_1} S)
        (@Monoid.toMulOneClass.{u_1} (FreeGroup.{u_1} S)
          (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
            (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S)))))
      (@MulOneClass.toMulOne.{u_3} G
        (@Monoid.toMulOneClass.{u_3} G (@DivInvMonoid.toMonoid.{u_3} G (@Group.toDivInvMonoid.{u_3} G inst)))))
  (R : ι → FreeGroup.{u_1} S) (a b t : S) (ia ib iab : ι)
  (hRa :
    @Eq.{u_1 + 1} (FreeGroup.{u_1} S) (R ia)
      (@HPow.hPow.{u_1, 0, u_1} (FreeGroup.{u_1} S) Nat (FreeGroup.{u_1} S)
        (@instHPow.{u_1, 0} (FreeGroup.{u_1} S) Nat
          (@NPow.toPow.{u_1} (FreeGroup.{u_1} S)
            (@Monoid.toNPow.{u_1} (FreeGroup.{u_1} S)
              (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S))))))
        (@FreeGroup.of.{u_1} S a) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hRb :
    @Eq.{u_1 + 1} (FreeGroup.{u_1} S) (R ib)
      (@HPow.hPow.{u_1, 0, u_1} (FreeGroup.{u_1} S) Nat (FreeGroup.{u_1} S)
        (@instHPow.{u_1, 0} (FreeGroup.{u_1} S) Nat
          (@NPow.toPow.{u_1} (FreeGroup.{u_1} S)
            (@Monoid.toNPow.{u_1} (FreeGroup.{u_1} S)
              (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S))))))
        (@FreeGroup.of.{u_1} S b) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hRab :
    @Eq.{u_1 + 1} (FreeGroup.{u_1} S) (R iab)
      (@HPow.hPow.{u_1, 0, u_1} (FreeGroup.{u_1} S) Nat (FreeGroup.{u_1} S)
        (@instHPow.{u_1, 0} (FreeGroup.{u_1} S) Nat
          (@NPow.toPow.{u_1} (FreeGroup.{u_1} S)
            (@Monoid.toNPow.{u_1} (FreeGroup.{u_1} S)
              (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S))))))
        (@HMul.hMul.{u_1, u_1, u_1} (FreeGroup.{u_1} S) (FreeGroup.{u_1} S) (FreeGroup.{u_1} S)
          (@instHMul.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instMul.{u_1} S)) (@FreeGroup.of.{u_1} S a)
          (@FreeGroup.of.{u_1} S b))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (hR1 :
    ∀ (k : ι),
      @Eq.{u_3 + 1} G
        (@DFunLike.coe.{max (u_1 + 1) (u_3 + 1), u_1 + 1, u_3 + 1}
          (@MonoidHom.{u_1, u_3} (FreeGroup.{u_1} S) G
            (@MulOneClass.toMulOne.{u_1} (FreeGroup.{u_1} S)
              (@Monoid.toMulOneClass.{u_1} (FreeGroup.{u_1} S)
                (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                  (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S)))))
            (@MulOneClass.toMulOne.{u_3} G
              (@Monoid.toMulOneClass.{u_3} G (@DivInvMonoid.toMonoid.{u_3} G (@Group.toDivInvMonoid.{u_3} G inst)))))
          (FreeGroup.{u_1} S) (fun (x : FreeGroup.{u_1} S) => G)
          (@MonoidHom.instFunLike.{u_1, u_3} (FreeGroup.{u_1} S) G
            (@MulOneClass.toMulOne.{u_1} (FreeGroup.{u_1} S)
              (@Monoid.toMulOneClass.{u_1} (FreeGroup.{u_1} S)
                (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                  (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S)))))
            (@MulOneClass.toMulOne.{u_3} G
              (@Monoid.toMulOneClass.{u_3} G (@DivInvMonoid.toMonoid.{u_3} G (@Group.toDivInvMonoid.{u_3} G inst)))))
          π (R k))
        (@OfNat.ofNat.{u_3} G (nat_lit 1)
          (@One.toOfNat1.{u_3} G
            (@InvOneClass.toOne.{u_3} G
              (@DivInvOneMonoid.toInvOneClass.{u_3} G
                (@DivisionMonoid.toDivInvOneMonoid.{u_3} G (@Group.toDivisionMonoid.{u_3} G inst)))))))
  (hab1 :
    @Ne.{u_3 + 1} G
      (@DFunLike.coe.{max (u_1 + 1) (u_3 + 1), u_1 + 1, u_3 + 1}
        (@MonoidHom.{u_1, u_3} (FreeGroup.{u_1} S) G
          (@MulOneClass.toMulOne.{u_1} (FreeGroup.{u_1} S)
            (@Monoid.toMulOneClass.{u_1} (FreeGroup.{u_1} S)
              (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S)))))
          (@MulOneClass.toMulOne.{u_3} G
            (@Monoid.toMulOneClass.{u_3} G (@DivInvMonoid.toMonoid.{u_3} G (@Group.toDivInvMonoid.{u_3} G inst)))))
        (FreeGroup.{u_1} S) (fun (x : FreeGroup.{u_1} S) => G)
        (@MonoidHom.instFunLike.{u_1, u_3} (FreeGroup.{u_1} S) G
          (@MulOneClass.toMulOne.{u_1} (FreeGroup.{u_1} S)
            (@Monoid.toMulOneClass.{u_1} (FreeGroup.{u_1} S)
              (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S)))))
          (@MulOneClass.toMulOne.{u_3} G
            (@Monoid.toMulOneClass.{u_3} G (@DivInvMonoid.toMonoid.{u_3} G (@Group.toDivInvMonoid.{u_3} G inst)))))
        π
        (@HMul.hMul.{u_1, u_1, u_1} (FreeGroup.{u_1} S) (FreeGroup.{u_1} S) (FreeGroup.{u_1} S)
          (@instHMul.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instMul.{u_1} S)) (@FreeGroup.of.{u_1} S a)
          (@FreeGroup.of.{u_1} S b)))
      (@OfNat.ofNat.{u_3} G (nat_lit 1)
        (@One.toOfNat1.{u_3} G
          (@InvOneClass.toOne.{u_3} G
            (@DivInvOneMonoid.toInvOneClass.{u_3} G
              (@DivisionMonoid.toDivInvOneMonoid.{u_3} G (@Group.toDivisionMonoid.{u_3} G inst)))))))
  (C p : Real)
  (hC : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C)
  (hp : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p)
  (hcyc :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
        ∀ (x : FreeGroup.{u_1} S),
          @Membership.mem.{u_1, u_1} (FreeGroup.{u_1} S) (List.{u_1} (FreeGroup.{u_1} S))
              (@List.instMembership.{u_1} (FreeGroup.{u_1} S))
              (@List.cons.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.of.{u_1} S a)
                (@List.cons.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.of.{u_1} S b) (@List.nil.{u_1} (FreeGroup.{u_1} S))))
              x →
            ∀ (y : FreeGroup.{u_1} S),
              @Membership.mem.{u_1, u_1} (FreeGroup.{u_1} S) (List.{u_1} (FreeGroup.{u_1} S))
                  (@List.instMembership.{u_1} (FreeGroup.{u_1} S))
                  (@List.cons.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.of.{u_1} S a)
                    (@List.cons.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.of.{u_1} S b)
                      (@List.nil.{u_1} (FreeGroup.{u_1} S))))
                  y →
                @Lamps.AreaLEGen.{u_1, u_2} S ι R
                  (@Lamps.commG.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S) x
                    (@HMul.hMul.{u_1, u_1, u_1} (FreeGroup.{u_1} S) (FreeGroup.{u_1} S) (FreeGroup.{u_1} S)
                      (@instHMul.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instMul.{u_1} S))
                      (@HMul.hMul.{u_1, u_1, u_1} (FreeGroup.{u_1} S) (FreeGroup.{u_1} S) (FreeGroup.{u_1} S)
                        (@instHMul.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instMul.{u_1} S))
                        (@HPow.hPow.{u_1, 0, u_1} (FreeGroup.{u_1} S) Nat (FreeGroup.{u_1} S)
                          (@instHPow.{u_1, 0} (FreeGroup.{u_1} S) Nat
                            (@NPow.toPow.{u_1} (FreeGroup.{u_1} S)
                              (@Monoid.toNPow.{u_1} (FreeGroup.{u_1} S)
                                (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                                  (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S))))))
                          (@FreeGroup.of.{u_1} S t) k)
                        y)
                      (@Inv.inv.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instInv.{u_1} S)
                        (@HPow.hPow.{u_1, 0, u_1} (FreeGroup.{u_1} S) Nat (FreeGroup.{u_1} S)
                          (@instHPow.{u_1, 0} (FreeGroup.{u_1} S) Nat
                            (@NPow.toPow.{u_1} (FreeGroup.{u_1} S)
                              (@Monoid.toNPow.{u_1} (FreeGroup.{u_1} S)
                                (@DivInvMonoid.toMonoid.{u_1} (FreeGroup.{u_1} S)
                                  (@Group.toDivInvMonoid.{u_1} (FreeGroup.{u_1} S) (@FreeGroup.instGroup.{u_1} S))))))
                          (@FreeGroup.of.{u_1} S t) k))))
                  (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast k) p))))
  (r : Real)
  (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r),
  And
    (∀ (n : Nat),
      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
          (@Houghton.modelSizes.{u_3} G inst
            (@Lamps.criterionChunk.{u_3, u_1, u_2} G inst S ι inst_1 inst_2 inst_3 π R a b) r)
          n →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) r
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@OfNat.ofNat.{0} Real (nat_lit 10)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                        C)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@Nat.cast.{0} Real Real.instNatCast (@Lamps.maxLen.{u_1, u_2} S ι inst_1 inst_3 R)))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) p
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast n)))
    (∀ (m : Nat),
      @Eq.{1} ENat
          (@Houghton.profile.{u_3} G inst
            (@Lamps.criterionChunk.{u_3, u_1, u_2} G inst S ι inst_1 inst_2 inst_3 π R a b) r)
          (@Nat.cast.{0} ENat ENat.instNatCast m) →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) r
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@OfNat.ofNat.{0} Real (nat_lit 10)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                        C)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@Nat.cast.{0} Real Real.instNatCast (@Lamps.maxLen.{u_1, u_2} S ι inst_1 inst_3 R)))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) p
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast m)))
end

section
/-- Proposition prop:upper, model. Original: `Lamps.prop_upper`. -/
def prop_upper : Prop :=
  ∀ (ℓ : Nat) (hℓ : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) ℓ)
  (E' :
    Finset.{0}
      (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
        @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
          (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
          (@SetLike.instMembership.{0, 0} (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
            (Equiv.Perm.{1} Lamps.X)
            (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
          Lamps.Γ x))
  (hE :
    ∀
      (g :
        @Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
          @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
            (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
            (@SetLike.instMembership.{0, 0} (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
            Lamps.Γ x),
      @Membership.mem.{0, 0}
          (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
            @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
              Lamps.Γ x)
          (Finset.{0}
            (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
              @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                Lamps.Γ x))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                  Lamps.Γ x))
            (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
              @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                Lamps.Γ x)
            (@Finset.instSetLike.{0}
              (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                  Lamps.Γ x)))
          E' g →
        @Exists.{1} (List.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Bool))
          fun (L : List.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Bool)) =>
          And
            (@LE.le.{0} Nat instLENat
              (@List.length.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Bool)
                L)
              ℓ)
            (@Eq.{1}
              (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                  Lamps.Γ x)
              (@DFunLike.coe.{1, 1, 1}
                (@MonoidHom.{0, 0} Lamps.F
                  (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ x)
                  (@MulOneClass.toMulOne.{0} Lamps.F
                    (@Monoid.toMulOneClass.{0} Lamps.F
                      (@DivInvMonoid.toMonoid.{0} Lamps.F
                        (@Group.toDivInvMonoid.{0} Lamps.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
                  (@MulOneClass.toMulOne.{0}
                    (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                      @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                          (Equiv.Perm.{1} Lamps.X)
                          (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                        Lamps.Γ x)
                    (@SubmonoidClass.toMulOneClass.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Lamps.X)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Lamps.X)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))))
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SubgroupClass.toSubmonoidClass.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSubgroupClass.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ)))
                Lamps.F
                (fun (x : Lamps.F) =>
                  @Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ x)
                (@MonoidHom.instFunLike.{0, 0} Lamps.F
                  (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ x)
                  (@MulOneClass.toMulOne.{0} Lamps.F
                    (@Monoid.toMulOneClass.{0} Lamps.F
                      (@DivInvMonoid.toMonoid.{0} Lamps.F
                        (@Group.toDivInvMonoid.{0} Lamps.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
                  (@MulOneClass.toMulOne.{0}
                    (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                      @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                          (Equiv.Perm.{1} Lamps.X)
                          (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                        Lamps.Γ x)
                    (@SubmonoidClass.toMulOneClass.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Lamps.X)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Lamps.X)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))))
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SubgroupClass.toSubmonoidClass.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSubgroupClass.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ)))
                Lamps.ρΓ' (@FreeGroup.mk.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) L))
              g))
  (r : Real)
  (hr : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r),
  @Exists.{1} Nat fun (n : Nat) =>
    And
      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
        (@Houghton.modelSizes.{0}
          (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
            @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
              Lamps.Γ x)
          (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ) E' r)
        n)
      (@LE.le.{0} Real Real.instLE
        (Real.logb
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@Nat.cast.{0} Real Real.instNatCast n))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 500)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 500) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 499) (instOfNatNat (nat_lit 499)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 498) (instOfNatNat (nat_lit 498)))))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@Nat.cast.{0} Real Real.instNatCast ℓ) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            r)
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              r))))
end

section
/-- Proposition prop:upper, profile. Original: `Lamps.prop_upper_profile`. -/
def prop_upper_profile : Prop :=
  ∀ (ℓ : Nat) (hℓ : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) ℓ)
  (E' :
    Finset.{0}
      (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
        @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
          (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
          (@SetLike.instMembership.{0, 0} (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
            (Equiv.Perm.{1} Lamps.X)
            (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
          Lamps.Γ x))
  (hE :
    ∀
      (g :
        @Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
          @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
            (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
            (@SetLike.instMembership.{0, 0} (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
            Lamps.Γ x),
      @Membership.mem.{0, 0}
          (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
            @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
              Lamps.Γ x)
          (Finset.{0}
            (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
              @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                Lamps.Γ x))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                  Lamps.Γ x))
            (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
              @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                Lamps.Γ x)
            (@Finset.instSetLike.{0}
              (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                  Lamps.Γ x)))
          E' g →
        @Exists.{1} (List.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Bool))
          fun (L : List.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Bool)) =>
          And
            (@LE.le.{0} Nat instLENat
              (@List.length.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) Bool)
                L)
              ℓ)
            (@Eq.{1}
              (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                  (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                  Lamps.Γ x)
              (@DFunLike.coe.{1, 1, 1}
                (@MonoidHom.{0, 0} Lamps.F
                  (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ x)
                  (@MulOneClass.toMulOne.{0} Lamps.F
                    (@Monoid.toMulOneClass.{0} Lamps.F
                      (@DivInvMonoid.toMonoid.{0} Lamps.F
                        (@Group.toDivInvMonoid.{0} Lamps.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
                  (@MulOneClass.toMulOne.{0}
                    (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                      @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                          (Equiv.Perm.{1} Lamps.X)
                          (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                        Lamps.Γ x)
                    (@SubmonoidClass.toMulOneClass.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Lamps.X)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Lamps.X)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))))
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SubgroupClass.toSubmonoidClass.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSubgroupClass.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ)))
                Lamps.F
                (fun (x : Lamps.F) =>
                  @Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ x)
                (@MonoidHom.instFunLike.{0, 0} Lamps.F
                  (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ x)
                  (@MulOneClass.toMulOne.{0} Lamps.F
                    (@Monoid.toMulOneClass.{0} Lamps.F
                      (@DivInvMonoid.toMonoid.{0} Lamps.F
                        (@Group.toDivInvMonoid.{0} Lamps.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
                  (@MulOneClass.toMulOne.{0}
                    (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                      @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                          (Equiv.Perm.{1} Lamps.X)
                          (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                        Lamps.Γ x)
                    (@SubmonoidClass.toMulOneClass.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Lamps.X)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Lamps.X)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))))
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SubgroupClass.toSubmonoidClass.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (@Subgroup.instSubgroupClass.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ)))
                Lamps.ρΓ' (@FreeGroup.mk.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) L))
              g))
  (r : Real)
  (hr : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r),
  @Exists.{1} Nat fun (n : Nat) =>
    And
      (@LE.le.{0} ENat instLEENat
        (@Houghton.profile.{0}
          (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
            @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
              Lamps.Γ x)
          (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ) E' r)
        (@Nat.cast.{0} ENat ENat.instNatCast n))
      (And
        (@LE.le.{0} Real Real.instLE
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast n))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 500)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 500) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 499) (instOfNatNat (nat_lit 499)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 498) (instOfNatNat (nat_lit 498)))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@Nat.cast.{0} Real Real.instNatCast ℓ)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              r)
            (Real.logb
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                r))))
        (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast n)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 500)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 500) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 499) (instOfNatNat (nat_lit 499)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 498) (instOfNatNat (nat_lit 498)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@Nat.cast.{0} Real Real.instNatCast ℓ)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                r)
              (Real.logb
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  r))))))
end

section
/-- Lemma lem:exchange. Original: `Lamps.exchange_sem`. -/
def lem_exchange : Prop :=
  ∀ (f : Lamps.F) (K : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Lamps.F) (k c n j : Nat)
  (hfK :
    ∀ (w : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))),
      @Eq.{1} Lamps.F
        (@DFunLike.coe.{1, 1, 1}
          (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
            (@MulOneClass.toMulOne.{0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Monoid.toMulOneClass.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@DivInvMonoid.toMonoid.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Group.toDivInvMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@MulOneClass.toMulOne.{0} Lamps.F
              (@Monoid.toMulOneClass.{0} Lamps.F
                (@DivInvMonoid.toMonoid.{0} Lamps.F
                  (@Group.toDivInvMonoid.{0} Lamps.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) => Lamps.F)
          (@MonoidHom.instFunLike.{0, 0}
            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
            (@MulOneClass.toMulOne.{0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Monoid.toMulOneClass.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@DivInvMonoid.toMonoid.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Group.toDivInvMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@MulOneClass.toMulOne.{0} Lamps.F
              (@Monoid.toMulOneClass.{0} Lamps.F
                (@DivInvMonoid.toMonoid.{0} Lamps.F
                  (@Group.toDivInvMonoid.{0} Lamps.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
          Lamps.ιpq
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
              FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@MonoidHom.instFunLike.{0, 0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (Lamps.fK k) w))
        (@DFunLike.coe.{1, 1, 1}
          (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
            (@MulOneClass.toMulOne.{0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Monoid.toMulOneClass.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@DivInvMonoid.toMonoid.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Group.toDivInvMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@MulOneClass.toMulOne.{0} Lamps.F
              (@Monoid.toMulOneClass.{0} Lamps.F
                (@DivInvMonoid.toMonoid.{0} Lamps.F
                  (@Group.toDivInvMonoid.{0} Lamps.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) => Lamps.F)
          (@MonoidHom.instFunLike.{0, 0}
            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
            (@MulOneClass.toMulOne.{0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Monoid.toMulOneClass.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@DivInvMonoid.toMonoid.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Group.toDivInvMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@MulOneClass.toMulOne.{0} Lamps.F
              (@Monoid.toMulOneClass.{0} Lamps.F
                (@DivInvMonoid.toMonoid.{0} Lamps.F
                  (@Group.toDivInvMonoid.{0} Lamps.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Lamps.F)
              (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Lamps.F
                (@MulOneClass.toMulOne.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Monoid.toMulOneClass.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@DivInvMonoid.toMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Group.toDivInvMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOneClass.toMulOne.{0} Lamps.F
                  (@Monoid.toMulOneClass.{0} Lamps.F
                    (@DivInvMonoid.toMonoid.{0} Lamps.F
                      (@Group.toDivInvMonoid.{0} Lamps.F
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Lamps.F)
            (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Lamps.F) =>
              @MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Lamps.F
                (@MulOneClass.toMulOne.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Monoid.toMulOneClass.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@DivInvMonoid.toMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Group.toDivInvMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOneClass.toMulOne.{0} Lamps.F
                  (@Monoid.toMulOneClass.{0} Lamps.F
                    (@DivInvMonoid.toMonoid.{0} Lamps.F
                      (@Group.toDivInvMonoid.{0} Lamps.F
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Lamps.F)
                (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Lamps.F
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} Lamps.F
                    (@Monoid.toMulOneClass.{0} Lamps.F
                      (@DivInvMonoid.toMonoid.{0} Lamps.F
                        (@Group.toDivInvMonoid.{0} Lamps.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Lamps.F)
              (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Lamps.F
                (@MulOneClass.toMulOne.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Monoid.toMulOneClass.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@DivInvMonoid.toMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Group.toDivInvMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOneClass.toMulOne.{0} Lamps.F
                  (@Monoid.toMulOneClass.{0} Lamps.F
                    (@DivInvMonoid.toMonoid.{0} Lamps.F
                      (@Group.toDivInvMonoid.{0} Lamps.F
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
              (@Equiv.instEquivLike.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Lamps.F)
                (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Lamps.F
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} Lamps.F
                    (@Monoid.toMulOneClass.{0} Lamps.F
                      (@DivInvMonoid.toMonoid.{0} Lamps.F
                        (@Group.toDivInvMonoid.{0} Lamps.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))))
            (@FreeGroup.lift.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Lamps.F
              (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
            K)
          w))
  (hS :
    ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
      Lamps.AreaLE (Lamps.comm f (K i)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hc :
    ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
      @LE.le.{0} Nat instLENat
        (@FreeGroup.norm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Matrix.vecCons.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@HMul.hMul.{0, 0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@instHMul.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (Lamps.ζ k) Lamps.P)
            (@Matrix.vecCons.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@HMul.hMul.{0, 0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@instHMul.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (Lamps.ζ k) Lamps.Q)
              (@Matrix.vecEmpty.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            i))
        c)
  (Z0 : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (B : Finset.{0} Houghton.Y)
  (hBpts :
    ∀ (y : Houghton.Y),
      @Membership.mem.{0, 0} Houghton.Y (Finset.{0} Houghton.Y)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Houghton.Y) Houghton.Y (@Finset.instSetLike.{0} Houghton.Y)) B y →
        @Exists.{1} Nat fun (u : Nat) =>
          And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) u)
            (And (@LE.le.{0} Nat instLENat u n) (@Eq.{1} Houghton.Y y (Lamps.pt u))))
  (hZ0supp :
    ∀ (y : Houghton.Y),
      Not
          (@Membership.mem.{0, 0} Houghton.Y (Finset.{0} Houghton.Y)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Houghton.Y) Houghton.Y (@Finset.instSetLike.{0} Houghton.Y)) B
            y) →
        @Eq.{1} Houghton.Y
          (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y (fun (x : Houghton.Y) => Houghton.Y)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y Houghton.Y
              (@Equiv.instEquivLike.{1, 1} Houghton.Y Houghton.Y))
            (@HMul.hMul.{0, 0, 0} (Equiv.Perm.{1} Houghton.Y) (Equiv.Perm.{1} Houghton.Y) (Equiv.Perm.{1} Houghton.Y)
              (@instHMul.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.instMul.{0} Houghton.Y))
              (@DFunLike.coe.{1, 1, 1}
                (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                  Equiv.Perm.{1} Houghton.Y)
                (@MonoidHom.instFunLike.{0, 0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                Lamps.ev2
                (@DFunLike.coe.{1, 1, 1}
                  (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                    FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@MonoidHom.instFunLike.{0, 0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (Lamps.fK k) Z0))
              (@Inv.inv.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.instInv.{0} Houghton.Y)
                (@DFunLike.coe.{1, 1, 1}
                  (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (Equiv.Perm.{1} Houghton.Y)
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                            (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                    Equiv.Perm.{1} Houghton.Y)
                  (@MonoidHom.instFunLike.{0, 0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (Equiv.Perm.{1} Houghton.Y)
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                            (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                  Lamps.ev2
                  (@HPow.hPow.{0, 0, 0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Nat
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@instHPow.{0, 0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Nat
                      (@NPow.toPow.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Monoid.toNPow.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@DivInvMonoid.toMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@Group.toDivInvMonoid.{0}
                              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (@FreeGroup.instGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    Lamps.P j))))
            y)
          y)
  (hZ0fix :
    ∀ (u : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) u →
        @LE.le.{0} Nat instLENat u k →
          @Eq.{1} Houghton.Y
            (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y (fun (x : Houghton.Y) => Houghton.Y)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y Houghton.Y
                (@Equiv.instEquivLike.{1, 1} Houghton.Y Houghton.Y))
              (@DFunLike.coe.{1, 1, 1}
                (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                  Equiv.Perm.{1} Houghton.Y)
                (@MonoidHom.instFunLike.{0, 0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                Lamps.ev2
                (@DFunLike.coe.{1, 1, 1}
                  (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                    FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@MonoidHom.instFunLike.{0, 0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    (@MulOneClass.toMulOne.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Monoid.toMulOneClass.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@DivInvMonoid.toMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@Group.toDivInvMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@FreeGroup.instGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (Lamps.fK k) Z0))
              (Lamps.pt u))
            (Lamps.pt u))
  (W U : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (A : Finset.{0} Houghton.Y)
  (hApts :
    ∀ (y : Houghton.Y),
      @Membership.mem.{0, 0} Houghton.Y (Finset.{0} Houghton.Y)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Houghton.Y) Houghton.Y (@Finset.instSetLike.{0} Houghton.Y)) A y →
        @Exists.{1} Nat fun (u : Nat) =>
          And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) u)
            (And (@LE.le.{0} Nat instLENat u n) (@Eq.{1} Houghton.Y y (Lamps.pt u))))
  (hW :
    ∀ (y : Houghton.Y),
      Not
          (@Membership.mem.{0, 0} Houghton.Y (Finset.{0} Houghton.Y)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Houghton.Y) Houghton.Y (@Finset.instSetLike.{0} Houghton.Y)) A
            y) →
        @Eq.{1} Houghton.Y
          (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y (fun (x : Houghton.Y) => Houghton.Y)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y Houghton.Y
              (@Equiv.instEquivLike.{1, 1} Houghton.Y Houghton.Y))
            (@DFunLike.coe.{1, 1, 1}
              (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (Equiv.Perm.{1} Houghton.Y)
                (@MulOneClass.toMulOne.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Monoid.toMulOneClass.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@DivInvMonoid.toMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Group.toDivInvMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                Equiv.Perm.{1} Houghton.Y)
              (@MonoidHom.instFunLike.{0, 0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (Equiv.Perm.{1} Houghton.Y)
                (@MulOneClass.toMulOne.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Monoid.toMulOneClass.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@DivInvMonoid.toMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Group.toDivInvMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
              Lamps.ev2 W)
            y)
          y)
  (hU :
    ∀ (y : Houghton.Y),
      Not
          (@Membership.mem.{0, 0} Houghton.Y (Finset.{0} Houghton.Y)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Houghton.Y) Houghton.Y (@Finset.instSetLike.{0} Houghton.Y)) A
            y) →
        @Eq.{1} Houghton.Y
          (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y (fun (x : Houghton.Y) => Houghton.Y)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y Houghton.Y
              (@Equiv.instEquivLike.{1, 1} Houghton.Y Houghton.Y))
            (@DFunLike.coe.{1, 1, 1}
              (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (Equiv.Perm.{1} Houghton.Y)
                (@MulOneClass.toMulOne.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Monoid.toMulOneClass.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@DivInvMonoid.toMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Group.toDivInvMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                Equiv.Perm.{1} Houghton.Y)
              (@MonoidHom.instFunLike.{0, 0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (Equiv.Perm.{1} Houghton.Y)
                (@MulOneClass.toMulOne.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Monoid.toMulOneClass.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@DivInvMonoid.toMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Group.toDivInvMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@FreeGroup.instGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
              Lamps.ev2 U)
            y)
          y)
  (hagree :
    ∀ (u : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) u →
        @LE.le.{0} Nat instLENat u k →
          @Eq.{1} Houghton.Y
            (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y (fun (x : Houghton.Y) => Houghton.Y)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y Houghton.Y
                (@Equiv.instEquivLike.{1, 1} Houghton.Y Houghton.Y))
              (@DFunLike.coe.{1, 1, 1}
                (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                  Equiv.Perm.{1} Houghton.Y)
                (@MonoidHom.instFunLike.{0, 0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                Lamps.ev2 U)
              (Lamps.pt u))
            (@DFunLike.coe.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y (fun (x : Houghton.Y) => Houghton.Y)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.Perm.{1} Houghton.Y) Houghton.Y Houghton.Y
                (@Equiv.instEquivLike.{1, 1} Houghton.Y Houghton.Y))
              (@DFunLike.coe.{1, 1, 1}
                (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
                  Equiv.Perm.{1} Houghton.Y)
                (@MonoidHom.instFunLike.{0, 0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (Equiv.Perm.{1} Houghton.Y)
                  (@MulOneClass.toMulOne.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toMulOneClass.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                  (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Equiv.Perm.permGroup.{0} Houghton.Y))))))
                Lamps.ev2
                (@HMul.hMul.{0, 0, 0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@instHMul.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                  W
                  (@HPow.hPow.{0, 0, 0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Nat
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@instHPow.{0, 0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Nat
                      (@NPow.toPow.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Monoid.toNPow.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@DivInvMonoid.toMonoid.{0}
                            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@Group.toDivInvMonoid.{0}
                              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (@FreeGroup.instGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    Lamps.P j)))
              (Lamps.pt u)))
  {D : Nat}
  (hD :
    Lamps.DehnLE
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@FreeGroup.norm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) W)
            j)
          (@FreeGroup.norm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) U))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@FreeGroup.norm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Z0)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                (@Finset.card.{0} Houghton.Y
                  (@Union.union.{0} (Finset.{0} Houghton.Y)
                    (@Finset.instUnion.{0} Houghton.Y fun (a b : Houghton.Y) =>
                      @instDecidableEqProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        Nat (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        instDecidableEqNat a b)
                    A B)))
              n))))
      D),
  Lamps.AreaLE
    (@HMul.hMul.{0, 0, 0} Lamps.F Lamps.F Lamps.F
      (@instHMul.{0} Lamps.F
        (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
      (@HMul.hMul.{0, 0, 0} Lamps.F Lamps.F Lamps.F
        (@instHMul.{0} Lamps.F
          (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
        (@HMul.hMul.{0, 0, 0} Lamps.F Lamps.F Lamps.F
          (@instHMul.{0} Lamps.F
            (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) => Lamps.F)
            (@MonoidHom.instFunLike.{0, 0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            Lamps.ιpq
            (@HMul.hMul.{0, 0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@instHMul.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              W
              (@HPow.hPow.{0, 0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Nat (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@instHPow.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Nat
                  (@NPow.toPow.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toNPow.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                Lamps.P j)))
          f)
        (@Inv.inv.{0} Lamps.F
          (@FreeGroup.instInv.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) => Lamps.F)
            (@MonoidHom.instFunLike.{0, 0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            Lamps.ιpq
            (@HMul.hMul.{0, 0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@instHMul.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              W
              (@HPow.hPow.{0, 0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Nat (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@instHPow.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  Nat
                  (@NPow.toPow.{0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Monoid.toNPow.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@DivInvMonoid.toMonoid.{0}
                        (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Group.toDivInvMonoid.{0}
                          (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                Lamps.P j)))))
      (@HMul.hMul.{0, 0, 0} Lamps.F Lamps.F Lamps.F
        (@instHMul.{0} Lamps.F
          (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
        (@HMul.hMul.{0, 0, 0} Lamps.F Lamps.F Lamps.F
          (@instHMul.{0} Lamps.F
            (@FreeGroup.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) => Lamps.F)
            (@MonoidHom.instFunLike.{0, 0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            Lamps.ιpq U)
          (@Inv.inv.{0} Lamps.F
            (@FreeGroup.instInv.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) f))
        (@Inv.inv.{0} Lamps.F
          (@FreeGroup.instInv.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0} (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (fun (x : FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) => Lamps.F)
            (@MonoidHom.instFunLike.{0, 0}
              (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) Lamps.F
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOneClass.toMulOne.{0} Lamps.F
                (@Monoid.toMulOneClass.{0} Lamps.F
                  (@DivInvMonoid.toMonoid.{0} Lamps.F
                    (@Group.toDivInvMonoid.{0} Lamps.F
                      (@FreeGroup.instGroup.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
            Lamps.ιpq U))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) D)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@FreeGroup.norm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Z0)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
            (@Finset.card.{0} Houghton.Y
              (@Union.union.{0} (Finset.{0} Houghton.Y)
                (@Finset.instUnion.{0} Houghton.Y fun (a b : Houghton.Y) =>
                  @instDecidableEqProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Nat
                    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    instDecidableEqNat a b)
                A B)))
          n)))
end

section
/-- Lemma lem:local-filling. Original: `Lamps.localIdsFamily`. -/
def lem_local_filling : Prop :=
  Lamps.LocalIdsFamily (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
  (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700)))
end

section
/-- Theorem thm:pair-area. Original: `Lamps.pairAreaStatement`. -/
def thm_pair_area : Prop :=
  Lamps.PairAreaStatement
end

section
/-- Lemma lem:imp-s3round. Original: `Lamps.unitaryS3Round`. -/
def lem_imp_s3round : Prop :=
  Lamps.UnitaryS3Round
end

section
/-- Theorem thm:imp-phase. Original: `Lamps.unitaryPhaseRobust`. -/
def thm_imp_phase : Prop :=
  Lamps.UnitaryPhaseRobust
end

section
/-- Theorem A(a). Original: `Lamps.theoremA_a_unconditional`. -/
def theorem_A_a : Prop :=
  @Exists.{1} Real fun (c : Real) =>
  And (@GT.gt.{0} Real Real.instLT c (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (∀ (r : Real),
      @GE.ge.{0} Real Real.instLE r
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
        ∀ (m : Nat),
          @Eq.{1} ENat
              (@Houghton.profile.{0}
                (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                  @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                    Lamps.Γ x)
                (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ) Lamps.E r)
              (@Nat.cast.{0} ENat ENat.instNatCast m) →
            @LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c r)
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (Real.logb
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    r)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Lamps.pH)))
              (Real.logb
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@Nat.cast.{0} Real Real.instNatCast m)))
end

section
/-- Theorem A(b), model. Original: `Lamps.theoremA_b`. -/
def theorem_A_b : Prop :=
  ∀ (r : Real)
  (hr :
    @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      r),
  @Exists.{1} Nat fun (n : Nat) =>
    And
      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
        (@Houghton.modelSizes.{0}
          (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
            @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
              Lamps.Γ x)
          (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ) Lamps.E r)
        n)
      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast n)
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 500)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 500) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 499) (instOfNatNat (nat_lit 499)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 498) (instOfNatNat (nat_lit 498)))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 24)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              r)
            (Real.logb
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                r)))))
end

section
/-- Theorem A(b), profile. Original: `Lamps.theoremA_b_profile`. -/
def theorem_A_b_profile : Prop :=
  ∀ (r : Real)
  (hr :
    @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      r),
  @Exists.{1} Nat fun (n : Nat) =>
    And
      (@LE.le.{0} ENat instLEENat
        (@Houghton.profile.{0}
          (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
            @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)) (Equiv.Perm.{1} Lamps.X)
                (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
              Lamps.Γ x)
          (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ) Lamps.E r)
        (@Nat.cast.{0} ENat ENat.instNatCast n))
      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast n)
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 500)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 500) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 499) (instOfNatNat (nat_lit 499)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 498) (instOfNatNat (nat_lit 498)))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 24)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              r)
            (Real.logb
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                r)))))
end

section
/-- Theorem A(c). Original: `Lamps.theoremA_c_unconditional`. -/
def theorem_A_c : Prop :=
  ∀ (Δ : Real)
  (hΔ0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Δ)
  (hΔ1 : @LE.le.{0} Real Real.instLE Δ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Exists.{1} Real fun (cΔ : Real) =>
    And (@GT.gt.{0} Real Real.instLT cΔ (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@Exists.{1} Real fun (eΔ : Real) =>
        And (@GT.gt.{0} Real Real.instLT eΔ (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (∀ (e : Real),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) e →
              @LE.le.{0} Real Real.instLE e eΔ →
                ∀ {Ω : Type} [inst : Fintype.{0} Ω] [inst_1 : DecidableEq.{1} Ω]
                  (φ :
                    @MonoidHom.{0, 0} Lamps.F
                      (@Subtype.{1} (Matrix.{0, 0, 0} Ω Ω Complex) fun (x : Matrix.{0, 0, 0} Ω Ω Complex) =>
                        @Membership.mem.{0, 0} (Matrix.{0, 0, 0} Ω Ω Complex)
                          (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                            (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                (@Matrix.semiring.{0, 0} Ω Complex
                                  (@CommSemiring.toSemiring.{0} Complex
                                    (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                  inst inst_1))))
                          (@SetLike.instMembership.{0, 0}
                            (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                  (@Matrix.semiring.{0, 0} Ω Complex
                                    (@CommSemiring.toSemiring.{0} Complex
                                      (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                    inst inst_1))))
                            (Matrix.{0, 0, 0} Ω Ω Complex)
                            (@Submonoid.instSetLike.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                  (@Matrix.semiring.{0, 0} Ω Complex
                                    (@CommSemiring.toSemiring.{0} Complex
                                      (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                    inst inst_1)))))
                          (@Matrix.unitaryGroup.{0, 0} Ω inst_1 inst Complex Complex.commRing Complex.instStarRing) x)
                      (@MulOneClass.toMulOne.{0} Lamps.F
                        (@Monoid.toMulOneClass.{0} Lamps.F
                          (@DivInvMonoid.toMonoid.{0} Lamps.F
                            (@Group.toDivInvMonoid.{0} Lamps.F
                              (@FreeGroup.instGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
                      (@MulOneClass.toMulOne.{0}
                        (@Subtype.{1} (Matrix.{0, 0, 0} Ω Ω Complex) fun (x : Matrix.{0, 0, 0} Ω Ω Complex) =>
                          @Membership.mem.{0, 0} (Matrix.{0, 0, 0} Ω Ω Complex)
                            (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                  (@Matrix.semiring.{0, 0} Ω Complex
                                    (@CommSemiring.toSemiring.{0} Complex
                                      (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                    inst inst_1))))
                            (@SetLike.instMembership.{0, 0}
                              (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                  (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                    (@Matrix.semiring.{0, 0} Ω Complex
                                      (@CommSemiring.toSemiring.{0} Complex
                                        (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                      inst inst_1))))
                              (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@Submonoid.instSetLike.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                  (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                    (@Matrix.semiring.{0, 0} Ω Complex
                                      (@CommSemiring.toSemiring.{0} Complex
                                        (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                      inst inst_1)))))
                            (@Matrix.unitaryGroup.{0, 0} Ω inst_1 inst Complex Complex.commRing Complex.instStarRing) x)
                        (@Submonoid.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                          (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                            (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@Matrix.semiring.{0, 0} Ω Complex
                                (@CommSemiring.toSemiring.{0} Complex
                                  (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                inst inst_1)))
                          (@Matrix.unitaryGroup.{0, 0} Ω inst_1 inst Complex Complex.commRing Complex.instStarRing)))),
                  (∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))),
                      @LE.le.{0} Real Real.instLE
                        (@Lamps.ud Ω inst
                          (@Lamps.phiM.{0} Ω inst inst_1
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) φ (Lamps.rel k))
                          (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} Ω Ω Complex) (nat_lit 1)
                            (@One.toOfNat1.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@Matrix.one.{0, 0} Ω Complex inst_1 Complex.instZero Complex.instOne))))
                        e) →
                    @LE.le.{0} Real Real.instLE Δ
                        (@Lamps.ud Ω inst
                          (@Lamps.phiM.{0} Ω inst inst_1
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) φ
                            (@HMul.hMul.{0, 0, 0} Lamps.F Lamps.F Lamps.F
                              (@instHMul.{0} Lamps.F
                                (@FreeGroup.instMul.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
                              Lamps.a Lamps.b))
                          (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} Ω Ω Complex) (nat_lit 1)
                            (@One.toOfNat1.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                              (@Matrix.one.{0, 0} Ω Complex inst_1 Complex.instZero Complex.instOne)))) →
                      @LE.le.{0} Real Real.instLE
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) cΔ
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) e)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (Real.logb
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) e))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                Lamps.pH))))
                        (Real.logb
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{0} Ω inst)))))
end

section
/-- Theorem A(d), amenability. Original: `Lamps.Γ_elementaryAmenable`. -/
def theorem_A_d_amenability : Prop :=
  @Lamps.ElementaryAmenable.{0}
  (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
      (@SetLike.instMembership.{0, 0} (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
        (Equiv.Perm.{1} Lamps.X)
        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
      Lamps.Γ x)
  (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ)
end

section
/-- Theorem A(a)-(d), combined. Original: `Lamps.theoremA`. -/
def theorem_A : Prop :=
  And
  (@Exists.{1} Real fun (c : Real) =>
    And (@GT.gt.{0} Real Real.instLT c (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (∀ (r : Real),
        @GE.ge.{0} Real Real.instLE r
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
          ∀ (m : Nat),
            @Eq.{1} ENat
                (@Houghton.profile.{0}
                  (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                    @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                        (Equiv.Perm.{1} Lamps.X)
                        (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                      Lamps.Γ x)
                  (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ) Lamps.E
                  r)
                (@Nat.cast.{0} ENat ENat.instNatCast m) →
              @LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c r)
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (Real.logb
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      r)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      Lamps.pH)))
                (Real.logb
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@Nat.cast.{0} Real Real.instNatCast m))))
  (And
    (∀ (r : Real),
      @LE.le.{0} Real Real.instLE
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          r →
        @Exists.{1} Nat fun (n : Nat) =>
          And
            (@LE.le.{0} ENat instLEENat
              (@Houghton.profile.{0}
                (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
                  @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
                    (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
                      (Equiv.Perm.{1} Lamps.X)
                      (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
                    Lamps.Γ x)
                (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ) Lamps.E r)
              (@Nat.cast.{0} ENat ENat.instNatCast n))
            (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast n)
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 500)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 500) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 499) (instOfNatNat (nat_lit 499)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 498) (instOfNatNat (nat_lit 498)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@OfNat.ofNat.{0} Real (nat_lit 24)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    r)
                  (Real.logb
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      r))))))
    (And
      (∀ (Δ : Real),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Δ →
          @LE.le.{0} Real Real.instLE Δ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @Exists.{1} Real fun (cΔ : Real) =>
              And
                (@GT.gt.{0} Real Real.instLT cΔ
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                (@Exists.{1} Real fun (eΔ : Real) =>
                  And
                    (@GT.gt.{0} Real Real.instLT eΔ
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                    (∀ (e : Real),
                      @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) e →
                        @LE.le.{0} Real Real.instLE e eΔ →
                          ∀ {Ω : Type} [inst : Fintype.{0} Ω] [inst_1 : DecidableEq.{1} Ω]
                            (φ :
                              @MonoidHom.{0, 0} Lamps.F
                                (@Subtype.{1} (Matrix.{0, 0, 0} Ω Ω Complex) fun (x : Matrix.{0, 0, 0} Ω Ω Complex) =>
                                  @Membership.mem.{0, 0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                    (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                      (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                          (@Matrix.semiring.{0, 0} Ω Complex
                                            (@CommSemiring.toSemiring.{0} Complex
                                              (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                            inst inst_1))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                          (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                            (@Matrix.semiring.{0, 0} Ω Complex
                                              (@CommSemiring.toSemiring.{0} Complex
                                                (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                              inst inst_1))))
                                      (Matrix.{0, 0, 0} Ω Ω Complex)
                                      (@Submonoid.instSetLike.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                          (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                            (@Matrix.semiring.{0, 0} Ω Complex
                                              (@CommSemiring.toSemiring.{0} Complex
                                                (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                              inst inst_1)))))
                                    (@Matrix.unitaryGroup.{0, 0} Ω inst_1 inst Complex Complex.commRing
                                      Complex.instStarRing)
                                    x)
                                (@MulOneClass.toMulOne.{0} Lamps.F
                                  (@Monoid.toMulOneClass.{0} Lamps.F
                                    (@DivInvMonoid.toMonoid.{0} Lamps.F
                                      (@Group.toDivInvMonoid.{0} Lamps.F
                                        (@FreeGroup.instGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))
                                (@MulOneClass.toMulOne.{0}
                                  (@Subtype.{1} (Matrix.{0, 0, 0} Ω Ω Complex) fun (x : Matrix.{0, 0, 0} Ω Ω Complex) =>
                                    @Membership.mem.{0, 0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                      (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                          (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                            (@Matrix.semiring.{0, 0} Ω Complex
                                              (@CommSemiring.toSemiring.{0} Complex
                                                (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                              inst inst_1))))
                                      (@SetLike.instMembership.{0, 0}
                                        (@Submonoid.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                          (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                            (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                              (@Matrix.semiring.{0, 0} Ω Complex
                                                (@CommSemiring.toSemiring.{0} Complex
                                                  (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                                inst inst_1))))
                                        (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@Submonoid.instSetLike.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                          (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                            (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                              (@Matrix.semiring.{0, 0} Ω Complex
                                                (@CommSemiring.toSemiring.{0} Complex
                                                  (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                                inst inst_1)))))
                                      (@Matrix.unitaryGroup.{0, 0} Ω inst_1 inst Complex Complex.commRing
                                        Complex.instStarRing)
                                      x)
                                  (@Submonoid.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                    (@MulZeroOneClass.toMulOneClass.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                      (@instMulZeroOneClassOfSemiring.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@Matrix.semiring.{0, 0} Ω Complex
                                          (@CommSemiring.toSemiring.{0} Complex
                                            (@CommRing.toCommSemiring.{0} Complex Complex.commRing))
                                          inst inst_1)))
                                    (@Matrix.unitaryGroup.{0, 0} Ω inst_1 inst Complex Complex.commRing
                                      Complex.instStarRing)))),
                            (∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))),
                                @LE.le.{0} Real Real.instLE
                                  (@Lamps.ud Ω inst
                                    (@Lamps.phiM.{0} Ω inst inst_1
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) φ
                                      (Lamps.rel k))
                                    (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} Ω Ω Complex) (nat_lit 1)
                                      (@One.toOfNat1.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@Matrix.one.{0, 0} Ω Complex inst_1 Complex.instZero Complex.instOne))))
                                  e) →
                              @LE.le.{0} Real Real.instLE Δ
                                  (@Lamps.ud Ω inst
                                    (@Lamps.phiM.{0} Ω inst inst_1
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) φ
                                      (@HMul.hMul.{0, 0, 0} Lamps.F Lamps.F Lamps.F
                                        (@instHMul.{0} Lamps.F
                                          (@FreeGroup.instMul.{0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
                                        Lamps.a Lamps.b))
                                    (@OfNat.ofNat.{0} (Matrix.{0, 0, 0} Ω Ω Complex) (nat_lit 1)
                                      (@One.toOfNat1.{0} (Matrix.{0, 0, 0} Ω Ω Complex)
                                        (@Matrix.one.{0, 0} Ω Complex inst_1 Complex.instZero Complex.instOne)))) →
                                @LE.le.{0} Real Real.instLE
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) cΔ
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat
                                          (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) e)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                    (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                                      (Real.logb
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) e))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                          Lamps.pH))))
                                  (Real.logb
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                    (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{0} Ω inst))))))
      (@Lamps.ElementaryAmenable.{0}
        (@Subtype.{1} (Equiv.Perm.{1} Lamps.X) fun (x : Equiv.Perm.{1} Lamps.X) =>
          @Membership.mem.{0, 0} (Equiv.Perm.{1} Lamps.X)
            (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
            (@SetLike.instMembership.{0, 0} (@Subgroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X))
              (Equiv.Perm.{1} Lamps.X)
              (@Subgroup.instSetLike.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X)))
            Lamps.Γ x)
        (@Subgroup.toGroup.{0} (Equiv.Perm.{1} Lamps.X) (@Equiv.Perm.permGroup.{0} Lamps.X) Lamps.Γ))))
end

section
universe u_1 u_2 u_3
/-- Theorem thm:sweep, conditional. Original: `Lamps.sweep_criterion`. -/
def thm_sweep : Prop :=
  ∀ {G : Type u_1} [inst : Group.{u_1} G] {S : Type u_2} {ι : Type u_3} [inst_1 : DecidableEq.{u_2 + 1} S]
  [inst_2 : Fintype.{u_2} S] [inst_3 : Fintype.{u_3} ι] (hS : Lamps.PermSweepBound)
  (π :
    @MonoidHom.{u_2, u_1} (FreeGroup.{u_2} S) G
      (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
        (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
          (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
            (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
      (@MulOneClass.toMulOne.{u_1} G
        (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
  (R : ι → FreeGroup.{u_2} S) (a b : S) (ia ib iab : ι)
  (hRa :
    @Eq.{u_2 + 1} (FreeGroup.{u_2} S) (R ia)
      (@HPow.hPow.{u_2, 0, u_2} (FreeGroup.{u_2} S) Nat (FreeGroup.{u_2} S)
        (@instHPow.{u_2, 0} (FreeGroup.{u_2} S) Nat
          (@NPow.toPow.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toNPow.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S))))))
        (@FreeGroup.of.{u_2} S a) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hRb :
    @Eq.{u_2 + 1} (FreeGroup.{u_2} S) (R ib)
      (@HPow.hPow.{u_2, 0, u_2} (FreeGroup.{u_2} S) Nat (FreeGroup.{u_2} S)
        (@instHPow.{u_2, 0} (FreeGroup.{u_2} S) Nat
          (@NPow.toPow.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toNPow.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S))))))
        (@FreeGroup.of.{u_2} S b) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hRab :
    @Eq.{u_2 + 1} (FreeGroup.{u_2} S) (R iab)
      (@HPow.hPow.{u_2, 0, u_2} (FreeGroup.{u_2} S) Nat (FreeGroup.{u_2} S)
        (@instHPow.{u_2, 0} (FreeGroup.{u_2} S) Nat
          (@NPow.toPow.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toNPow.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S))))))
        (@HMul.hMul.{u_2, u_2, u_2} (FreeGroup.{u_2} S) (FreeGroup.{u_2} S) (FreeGroup.{u_2} S)
          (@instHMul.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instMul.{u_2} S)) (@FreeGroup.of.{u_2} S a)
          (@FreeGroup.of.{u_2} S b))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (hR1 :
    ∀ (k : ι),
      @Eq.{u_1 + 1} G
        (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1}
          (@MonoidHom.{u_2, u_1} (FreeGroup.{u_2} S) G
            (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
              (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
                (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                  (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
            (@MulOneClass.toMulOne.{u_1} G
              (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
          (FreeGroup.{u_2} S) (fun (x : FreeGroup.{u_2} S) => G)
          (@MonoidHom.instFunLike.{u_2, u_1} (FreeGroup.{u_2} S) G
            (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
              (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
                (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                  (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
            (@MulOneClass.toMulOne.{u_1} G
              (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
          π (R k))
        (@OfNat.ofNat.{u_1} G (nat_lit 1)
          (@One.toOfNat1.{u_1} G
            (@InvOneClass.toOne.{u_1} G
              (@DivInvOneMonoid.toInvOneClass.{u_1} G
                (@DivisionMonoid.toDivInvOneMonoid.{u_1} G (@Group.toDivisionMonoid.{u_1} G inst)))))))
  (hab1 :
    @Ne.{u_1 + 1} G
      (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1}
        (@MonoidHom.{u_2, u_1} (FreeGroup.{u_2} S) G
          (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
        (FreeGroup.{u_2} S) (fun (x : FreeGroup.{u_2} S) => G)
        (@MonoidHom.instFunLike.{u_2, u_1} (FreeGroup.{u_2} S) G
          (@MulOneClass.toMulOne.{u_2} (FreeGroup.{u_2} S)
            (@Monoid.toMulOneClass.{u_2} (FreeGroup.{u_2} S)
              (@DivInvMonoid.toMonoid.{u_2} (FreeGroup.{u_2} S)
                (@Group.toDivInvMonoid.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instGroup.{u_2} S)))))
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
        π
        (@HMul.hMul.{u_2, u_2, u_2} (FreeGroup.{u_2} S) (FreeGroup.{u_2} S) (FreeGroup.{u_2} S)
          (@instHMul.{u_2} (FreeGroup.{u_2} S) (@FreeGroup.instMul.{u_2} S)) (@FreeGroup.of.{u_2} S a)
          (@FreeGroup.of.{u_2} S b)))
      (@OfNat.ofNat.{u_1} G (nat_lit 1)
        (@One.toOfNat1.{u_1} G
          (@InvOneClass.toOne.{u_1} G
            (@DivInvOneMonoid.toInvOneClass.{u_1} G
              (@DivisionMonoid.toDivInvOneMonoid.{u_1} G (@Group.toDivisionMonoid.{u_1} G inst)))))))
  {N : Nat} (hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (w : Fin N → FreeGroup.{u_2} S) (Λ : Nat) (hw : @Lamps.SweepAreaLE.{u_2, u_3} S ι R a b N w Λ) (r : Real)
  (hr :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast Λ)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 40)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 40) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 39) (instOfNatNat (nat_lit 39)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))))))
            (@Nat.cast.{0} Real Real.instNatCast N)))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast (@Lamps.maxLen.{u_2, u_3} S ι inst_1 inst_3 R)))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) r
        (@OfNat.ofNat.{0} Real (nat_lit 20000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 20000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19999) (instOfNatNat (nat_lit 19999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 19998) (instOfNatNat (nat_lit 19998))))))))),
  And
    (∀ (n : Nat),
      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
          (@Houghton.modelSizes.{u_1} G inst
            (@Lamps.criterionChunk.{u_1, u_2, u_3} G inst S ι inst_1 inst_2 inst_3 π R a b) r)
          n →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast n)))
    (∀ (m : Nat),
      @Eq.{1} ENat
          (@Houghton.profile.{u_1} G inst
            (@Lamps.criterionChunk.{u_1, u_2, u_3} G inst S ι inst_1 inst_2 inst_3 π R a b) r)
          (@Nat.cast.{0} ENat ENat.instNatCast m) →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (Real.logb
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast m)))
end

end PaperStatements
