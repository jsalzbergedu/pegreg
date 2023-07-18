Require Import List.
Import ListNotations.

Section PegReg.
  Context (Σ : Type).
  Context (eq_dec : Σ -> Σ -> bool).
  Context (eq_dec_correct : forall σ1 σ2, (eq_dec σ1 σ2 = true <-> σ1 = σ2) /\ (eq_dec σ1 σ2 = false <-> σ1 <> σ2)).

  Inductive PEG : Type :=
  | Char (c : Σ)
  | Concat (p1 : PEG) (p2 : PEG)
  | PossesiveStar (p1 : PEG)
  | OrderedChoice (p1 : PEG) (p2 : PEG).

  Inductive PegMatch : PEG -> list Σ -> option (list Σ * list Σ) -> Prop :=
  | CharS : forall c : Σ, forall t : list Σ, PegMatch (Char c) (c :: t) (Some ([c], t))
  | CharFail : forall c1 c2 : Σ, forall t : list Σ, (eq_dec c1 c2) = false -> PegMatch (Char c1) (c2 :: t) None
  | CatS : forall p1 p2 : PEG, forall l0 l1 l2 l3 l4 : list Σ, PegMatch p1 l0 (Some (l1, l2)) ->
                                                     PegMatch p2 l2 (Some (l3,  l4)) ->
                                                     PegMatch (Concat p1 p2) l0 (Some ((l1 ++ l3), l4))
  | CatFail1 : forall p1 p2 : PEG, forall l : list Σ, PegMatch p1 l None -> PegMatch (Concat p1 p2) l None
  | CatFail2 : forall p1 p2 : PEG, forall l0 l1 l2 : list Σ, PegMatch p1 l0 (Some (l1, l2)) -> PegMatch p2 l2 None -> PegMatch (Concat p1 p2) l0 None
  | ChoiceL : forall p1 p2 : PEG, forall l0 l1 l2 : list Σ, PegMatch p1 l0 (Some (l1, l2)) ->
                                                  PegMatch (OrderedChoice p1 p2) l0 (Some (l1, l2))
  | ChoiceR : forall p1 p2 : PEG, forall l0 l1 l2 : list Σ, PegMatch p1 l0 None -> PegMatch p2 l0 (Some (l1, l2)) -> PegMatch (OrderedChoice p1 p2) l0 (Some (l1, l2))
  | ChoiceFail : forall p1 p2 : PEG, forall l0 : list Σ, PegMatch p1 l0 None -> PegMatch p2 l0 None -> PegMatch (OrderedChoice p1 p2) l0 None
  | StarEnd : forall p1 : PEG, forall l : list Σ, PegMatch p1 l None -> PegMatch (PossesiveStar p1) l (Some ([], l))
  | StarRec : forall p1 : PEG, forall l0 l1 l2 l3 l4 : list Σ, PegMatch p1 l0 (Some (l1, l2)) -> PegMatch (PossesiveStar p1) l2 (Some (l3, l4)) -> PegMatch (PossesiveStar p1) l0 (Some (l1 ++ l3, l4)).

  Definition DoesNotMatch (P : PEG) (l : list Σ) := (forall l1 l2, PegMatch P l (Some (l1, l2)) -> False).

  Definition PPartial (p : PEG) := forall l o, PegMatch p l o -> forall o', PegMatch p l o' -> o = o'.

  Lemma PPartialStar : forall p l o, PegMatch p l o -> forall p', p = PossesiveStar p' -> PPartial p' -> forall o', PegMatch p l o' -> o = o'.
    intros p l o m.
    induction m; try discriminate.
    {
      intros p' Heq HPartial o' m'.
      inversion Heq. subst p'.
      destruct o' eqn:eqo.
      {
        inversion m'. { reflexivity. } { subst. assert (Some (l1, l2) = None) by eauto. discriminate. }
      }
      {
        inversion m'.
      }
    }
    {
      intros p' Heqp Hpartial o' m'.
      inversion Heqp.
      subst p'.
      destruct o' eqn:eqo.
      {
        inversion m'.
        {
          subst.
          assert (None = Some (l1, l2)) by eauto.
          discriminate.
        }
        {
          subst.
          assert (Some (l6, l7) = Some (l1, l2)) by eauto.
          inversion H.
          subst.
          assert (Some (l3, l4) = Some (l8, l9)). { eapply IHm2. exact Heqp. exact Hpartial. exact H3. }
          now inversion H0.
        }
      }
      {
        inversion m'.
      }
    }
  Qed.

  Lemma PegPartialFunctionStrong: forall p, PPartial p.
    intros p.
    induction p.
    {
      intros l o m1 o' m2.
      destruct o; destruct o'; try reflexivity.
      {
        inversion m1. inversion m2.
        subst.
        now inversion H2.
      }
      {
        inversion m1. inversion m2.
        subst. inversion H4. subst. now apply eq_dec_correct in H3.
      }
      {
        inversion m1. inversion m2.
        subst. inversion H2. subst. now apply eq_dec_correct in H0.
      }
    }
    {
      intros l o m1 o' m2.
      destruct o; destruct o'; try reflexivity.
      {
        inversion m1. inversion m2.
        subst.
        assert (Some (l1, l2) = Some (l6, l7)) by eauto.
        inversion H.
        subst l7. subst l6.
        assert (Some (l3, l4) = Some (l8, l9)) by eauto.
        inversion H0. subst l9. subst l8.
        reflexivity.
      }
      {
        inversion m2.
        { inversion m1. subst. assert (Some (l2, l3) = None) by eauto. discriminate. }
        { inversion m1. subst. assert (Some (l1, l2) = Some (l4, l5)) by eauto. inversion H. subst. assert (Some (l6, l7) = None) by eauto. discriminate. }
      }
      {
        inversion m1.
        { inversion m2. subst. assert (Some (l2, l3) = None) by eauto. discriminate. }
        { inversion m2. subst. assert (Some (l1, l2) = Some (l4, l5)) by eauto. inversion H. subst. assert (Some (l6, l7) = None) by eauto. discriminate. }
      }
    }
    {
      intros l o m1 o' m2.
      eauto using PPartialStar.
    }
    {
      intros l o m1 o' m2.
      destruct o; destruct o'; try reflexivity.
      {
        inversion m1.
        {
          inversion m2.
          {
            eauto.
          }
          {
            assert (Some (l1, l2) = None) by eauto.
            discriminate.
          }
        }
        {
          inversion m2.
          {
            assert (None = Some (l4, l5)) by eauto.
            discriminate.
          }
          {
            eauto.
          }
        }
      }
      {
        inversion m2.
        subst.
        inversion m1; subst; assert (Some (l1, l2) = None) by eauto; discriminate.
      }
      {
        inversion m1.
        subst.
        inversion m2; subst; assert (Some (l1, l2) = None) by eauto; discriminate.
      }
    }
  Qed.

  Theorem PegPartial : forall p l o, PegMatch p l o -> forall o', PegMatch p l o' -> o = o'.
    intros p.
    assert (PPartial p) by eauto using PegPartialFunctionStrong.
    eauto using PegPartialFunctionStrong.
  Qed.

  Axiom lem_peg : forall (P : PEG) (l1 : list Σ), DoesNotMatch P l1 \/
                                               exists (l2 l3 : list Σ), (PegMatch P l1 (Some (l2, l3))).

  (* Equivalent to the last one by pegpartial, however I don't feel like proving that.
     I'm guessing either lempeg is probably provable without lem itself. *)
  Axiom lem_peg' : forall (P : PEG) (l : list Σ) (o : option (list Σ * list Σ)),
      PegMatch P l o \/ ~PegMatch P l o.

  Inductive REG : Type :=
  | REmp
  | RAny
  | RChar (c : Σ)
  | RConcat (r1 : REG) (r2 : REG)
  | RUnion (r1 : REG) (r2 : REG)
  | RStar (r : REG)
  | RIntersection (r1 : REG) (r2 : REG)
  | RNeg (r1 : REG).

  Inductive RegMatch : REG -> list Σ -> bool -> Prop :=
  | REmpS : RegMatch REmp [] true
  | REmpF : forall c, forall t : list Σ, RegMatch REmp (c :: t) false
  | RAnyS : forall c : Σ, RegMatch (RAny) [c] true
  | RCharS : forall c : Σ, RegMatch (RChar c) [c] true
  | RCharFEmp : forall c : Σ, RegMatch (RChar c) [] false
  | RCharF1 : forall c1 c2 : Σ, forall t, (eq_dec c1 c2) = false -> RegMatch (RChar c1) (c2 :: t) false
  | RCharF2 : forall c c1 c2, forall t, RegMatch (RChar c) (c1 :: c2 :: t) false
  | RConcatS : forall l1 l2 : list Σ, forall r1 r2 : REG, RegMatch r1 l1 true -> RegMatch r2 l2 true -> RegMatch (RConcat r1 r2) (l1 ++ l2) true
  | RConcatF r1 r2 : forall l : list Σ,
      (forall l1' l1'', l1' ++ l1'' = l -> (RegMatch r1 l1' false) \/ (RegMatch r1 l1' true /\ RegMatch r2 l1'' false)) ->
                                            RegMatch (RConcat r1 r2) l false
  | RUnionSL : forall l1 : list Σ, forall r1 r2 : REG, RegMatch r1 l1 true -> RegMatch (RUnion r1 r2) l1 true
  | RUnionSR : forall l1 : list Σ, forall r1 r2 : REG, RegMatch r2 l1 true -> RegMatch (RUnion r1 r2) l1 true
  | RUnionF r1 r2 : forall l1 : list Σ, RegMatch r1 l1 false -> RegMatch r2 l1 false -> RegMatch (RUnion r1 r2) l1 false
  | RStarS r1 : forall l, (exists l', List.concat l' = l /\ Forall (fun l => RegMatch r1 l true) l') -> RegMatch (RStar r1) l true
  | RStarF r1 : forall l, (forall l', List.concat l' = l -> (exists e, In e l' /\ RegMatch r1 e false)) -> RegMatch (RStar r1) l false
  | RIntersectionS : forall l : list Σ, forall r1 r2 : REG, RegMatch r1 l true -> RegMatch r2 l true -> RegMatch (RIntersection r1 r2) l true
  | RIntersectionFL r1 r2 : forall l : list Σ, RegMatch r1 l false -> RegMatch (RIntersection r1 r2) l false
  | RIntersectionFR r1 r2 : forall l : list Σ, RegMatch r2 l false -> RegMatch (RIntersection r1 r2) l false
  | RNegS : forall l : list Σ, forall r : REG, RegMatch r l true -> RegMatch (RNeg r) l false
  | RNegF : forall l : list Σ, forall r : REG, RegMatch r l false -> RegMatch (RNeg r) l true.
  (* I do have some doubts that RNegS is the same as the automata defn.*)

  (* Remove the parts of r corresponding to ordered/possesive choices of p,
     then concatenate p with r. *)
  Fixpoint PEGREG_old (p : PEG) (r : REG) : REG :=
    match p with
    | Char c => RConcat (RChar c) r
    | Concat p1 p2 => PEGREG_old p1 (PEGREG_old p2 r)
    | OrderedChoice p1 p2 =>
        let reg_p1_r := PEGREG_old p1 r in
        let reg_p2_r := PEGREG_old p2 r in
        let reg_p1 := PEGREG_old p1 REmp in
        RUnion reg_p1_r (RIntersection reg_p2_r (RNeg (RConcat reg_p1 (RStar RAny))))
    | PossesiveStar p1 =>
        let reg_p1 := (PEGREG_old p1 REmp) in
        RConcat (RStar reg_p1) (RIntersection r (RNeg (RConcat reg_p1 (RStar RAny))))
    end.
  Fixpoint PEGREG (p : PEG) (r : REG) : REG :=
    match p with
    | Char c => RConcat (RChar c) r
    | Concat p1 p2 => PEGREG p1 (PEGREG p2 r)
    | OrderedChoice p1 p2 =>
        let reg_p1_r := PEGREG p1 r in
        let reg_p2_r := PEGREG p2 r in
        let reg_p1 := PEGREG p1 REmp in
        RUnion reg_p1_r (RIntersection reg_p2_r (RNeg reg_p1))
    | PossesiveStar p1 =>
        let reg_p1 := (PEGREG p1 REmp) in
        RConcat (RStar reg_p1) (RIntersection r (RNeg reg_p1))
    end.


  Definition some_implies_match (P : PEG) (r__remainder : REG) (r__out : REG) :=
    forall l1 l2 l3 prf suf, PegMatch P l1 (Some (l2, l3)) -> prf ++ suf = l3 -> RegMatch r__remainder prf true -> RegMatch r__out (l2 ++ prf) true.

  Definition none_implies_nomatch (P : PEG) (r__remainder : REG) (r__out : REG) :=
    forall l1, (forall prf suf, l1 = prf ++ suf -> DoesNotMatch P prf) -> RegMatch r__out l1 false.

  Definition blame_remainder (P : PEG) (r__remainder : REG) (r__out : REG) :=
    forall l1 l2, PegMatch P (l1 ++ l2) (Some (l1, l2)) ->
                        RegMatch r__remainder l2 false -> RegMatch r__out (l1 ++ l2) false.

  Inductive NonEmpty : PEG -> Prop :=
  | NonEmptyChar : forall c, NonEmpty (Char c)
  | NonEmptyConcat : forall p1 p2, NonEmpty p1 -> NonEmpty p2 -> (NonEmpty (Concat p1 p2))
  | NonEmptyConcatL : forall p1 p2, NonEmpty p1 -> NonEmpty p2 -> (NonEmpty (Concat (PossesiveStar p1) p2))
  | NonEmptyConcatR : forall p1 p2, NonEmpty p1 -> NonEmpty p2 -> (NonEmpty (Concat p1 (PossesiveStar p2)))
  | NonEmptyOrderedChoice : forall p1 p2, NonEmpty p1 -> NonEmpty p2 -> NonEmpty (OrderedChoice p1 p2).
  (* Okay, this characterizes nonempty now, I think.
   * Now, I'm not sure it is the case that you can recast any PEG P, where
   * PegMatch P [] ~> false, as NonEmpty.
   * Also, does this deal with the ** case?
   * not PEGMatch P**x s ->
   * not RegMatch P** x s?
   * Yes, by disallowing **. p1 must be nonempty.
   * If we do this, then do we get doesnotmatch monotonicity? Cut off chars, and you match less?
   * I can't yet see why not
   *)


  Definition LR (P : PEG) (r__remainder : REG) (r__out : REG) : Prop :=
    some_implies_match P r__remainder r__out /\ none_implies_nomatch P r__remainder r__out /\
      blame_remainder P r__remainder r__out.

  Definition WeakenFail (P : PEG) (l1 l2 : list Σ) :=
    PegMatch P l1 None -> PegMatch P (l1 ++ l2) None.

  Definition WeakenMatch (P : PEG) (l1 l2 l3 : list Σ) :=
    PegMatch P (l1 ++ l2) (Some (l1, l2)) ->
    PegMatch P (l1 ++ l2 ++ l3) (Some (l1, l2 ++ l3)).

  Definition BlameConcatenee (P : PEG) (l1 l2 l3: list Σ) :=
    forall P', PegMatch P l1 (Some (l2, l3)) -> PegMatch (Concat P P') l1 None ->
          PegMatch P' l3 None.

  Definition WeakenStar (P : PEG) (l1 l2 l3 : list Σ) :=
    PegMatch (PossesiveStar P) (l1 ++ l2) (Some (l1, l2)) ->
    PegMatch (PossesiveStar P) (l1 ++ l2 ++ l3) (Some (l1, l2 ++ l3)).

  Lemma list_split : forall p : PEG, forall l1 l2 l3 : list Σ, PegMatch p l1 (Some (l2, l3)) -> l1 = l2 ++ l3.
    intros P l1 l2 l3 m.
    remember (Some (l2, l3)) as output.
    generalize dependent l3.
    generalize dependent l2.
    remember l1 as input.
    generalize dependent l1.
    induction m; try discriminate; try eauto.
    {
      intros l1 H1 l2 l3 H2.
      inversion H2.
      reflexivity.
    }
    {
      intros l5 H1 l6 l7 H2.
      inversion H2.
      subst l7.
      subst l6.
      clear H2.
      subst l5.
      rename l0 into input.
      rename l2 into remainder.
      assert (remainder = l3 ++ l4).
      {
        eauto.
      }
      rewrite <- app_assoc.
      subst remainder.
      eauto.
    }
    {
      intros l1 H1 l2 l3 H2.
      inversion H2. subst l3. subst l2.
      reflexivity.
    }
    {
      intros l6 H1 l7 l8 H2.
      subst l6.
      inversion H2.
      subst l8.
      subst l7.
      clear H2.
      assert (l2 = l3 ++ l4).
      {
        eauto.
      }
      rewrite <- app_assoc.
      subst l2.
      eauto.
    }
  Qed.

  Lemma StarWeakenBaseStrong1 : forall p l o,
      PegMatch p l o ->
      forall l1 l2 l3 c,
        p = (PossesiveStar (Char c)) -> l = l1 ++ l2 -> o = (Some (l1, l2)) ->
        PegMatch p (l1 ++ l2 ++ l3) (Some (l1, l2 ++ l3)).
    intros p l o m.
    induction m; try discriminate.
    {
      intros l1 l2 l3 c Heq1 Heq2 H.
      inversion H. inversion Heq2. inversion Heq1. subst.
      constructor.
      simpl in m.
      inversion m.
      subst.
      now constructor.
    }
    {
      intros l6 l7 l8 c Heq1 Heq2 H.
      inversion H.
      inversion Heq1.
      inversion Heq2.
      subst.
      rewrite <- app_assoc.
      rewrite <- app_assoc in m1.
      inversion m1.
      subst.
      eapply StarRec.
      {
        constructor.
      }
      {
        eapply IHm2.
        reflexivity.
        apply list_split in m2.
        assumption.
        reflexivity.
      }
    }
  Qed.

  Lemma StarWeakenBase1 : forall l1 l2 l3 c,
      PegMatch (PossesiveStar (Char c)) (l1 ++ l2) (Some (l1, l2)) ->
      PegMatch (PossesiveStar (Char c)) (l1 ++ l2 ++ l3) (Some (l1, l2 ++ l3)).
    eauto using StarWeakenBaseStrong1.
  Qed.

  Lemma ConcatDistrEquivalentFail : forall P1 P2 P3, forall l,
      PegMatch (Concat (Concat P1 P2) P3) l None <->
        PegMatch (Concat P1 (Concat P2 P3)) l None.
    intros P1 P2 P3 l.
    split.
    {
      intros H.
      inversion H.
      {
        subst.
        inversion H3.
        {
          now eapply CatFail1.
        }
        {
          subst.
          eapply CatFail2; try exact H2.
          now eapply CatFail1.
        }
      }
      {
        subst.
        inversion H2.
        subst.
        eapply CatFail2.
        {
          exact H6.
        }
        {
          eapply CatFail2.
          {
            exact H8.
          }
          {
            exact H4.
          }
        }
      }
    }
    {
      intros H.
      inversion H.
      {
        subst.
        eapply CatFail1.
        now eapply CatFail1.
      }
      {
        subst.
        inversion H4.
        subst.
        {
          eapply CatFail1.
          now eapply CatFail2; try exact H2.
        }
        {
          subst.
          eapply CatFail2.
          {
            eapply CatS. { exact H2. } { exact H3. }
          }
          {
            exact H6.
          }
        }
      }
    }
  Qed.

  Lemma StarWeakenConcatStrong :
    forall p l o, PegMatch p l o ->
             forall P1 P2 l1 l2 l3 l4, p = (PossesiveStar (Concat P1 P2)) -> l = l1 -> o = (Some (l2, l3)) ->
                                  (forall l4 l5 l6, WeakenMatch (Concat P1 P2) l4 l5 l6 /\ WeakenFail (Concat P1 P2) l4 l5) -> PegMatch p (l1 ++ l4) (Some (l2, l3 ++ l4)).
    intros p l o m.
    induction m; try discriminate.
    {
      intros P1 P2 l1 l2 l3 l4 Heq1 Heq2 Heq3 HWeaken.
      inversion Heq1.
      inversion Heq2.
      inversion Heq3.
      subst.
      apply StarEnd.
      assert (WeakenFail (Concat P1 P2) l3 l4) by (apply HWeaken; exact []).
      unfold WeakenFail in H0.
      now apply H0.
    }
    {
      intros P1 P2 l6 l7 l8 l9 Heq1 Heq2 Heq3 HWeaken.
      inversion Heq1.
      inversion Heq2.
      inversion Heq3.
      subst.
      apply list_split in m1 as HLS.
      subst l6.
      assert (PegMatch (Concat P1 P2) (l1 ++ l2 ++ l9) (Some (l1, l2 ++ l9))).
      {
        assert (WeakenMatch (Concat P1 P2) l1 l2 l9) by (apply HWeaken; exact []).
        unfold WeakenMatch in H0.
        now apply H0.
      }
      assert (PegMatch (PossesiveStar (Concat P1 P2)) (l2 ++ l9) (Some (l3, l8 ++ l9))) by (eapply IHm2; eauto).
      rewrite <- app_assoc.
      econstructor. { exact H0. } { exact H1.}
    }
  Qed.

  Lemma StarWeakenConcat : forall P1 P2 l1 l2 l3, (forall l4 l5 l6, WeakenMatch (Concat P1 P2) l4 l5 l6 /\ WeakenFail (Concat P1 P2) l4 l5) -> WeakenStar (Concat P1 P2) l1 l2 l3.
    intros P1 P2 l1 l2 l3 H1 H2.
    remember (PossesiveStar (Concat P1 P2)).
    remember (l1 ++ l2).
    rewrite app_assoc.
    remember (Some (l1, l2)).
    eapply StarWeakenConcatStrong; eauto.
  Qed.

  Lemma MatchDeterministic :
    forall p l o, PegMatch p l o -> forall o', PegMatch p l o' -> o' = o.
    intros p l o m.
    induction m.
    {
      intros o' H.
      inversion H.
      {
        subst.
        reflexivity.
      }
      {
        subst.
        now apply eq_dec_correct in H4.
      }
    }
    {
      intros o' H'.
      inversion H'.
      {
        subst.
        apply eq_dec_correct in H.
        contradiction.
      }
      {
        reflexivity.
      }
    }
    {
      intros o' H2.
      inversion H2.
      {
        subst.
        assert (Some (l6, l7) = Some (l1, l2)).
        {
          now apply IHm1.
        }
        assert (Some (l8, l9) = Some (l3, l4)).
        {
          apply IHm2.
          inversion H.
          subst.
          assumption.
        }
        inversion H.
        inversion H0.
        subst.
        reflexivity.
      }
      {
        subst.
        assert (None = Some (l1, l2)).
        {
          now apply IHm1.
        }
        inversion H.
      }
      {
        subst.
        assert (Some (l6, l7) = Some (l1, l2)); eauto.
        inversion H.
        subst.
        assert (None = (Some (l3, l4))); eauto using IHm2.
        inversion H0.
      }
    }
    {
      intros o H1.
      inversion H1; try eauto.
      subst.
      assert (Some (l1, l2) = None); eauto.
      inversion H.
    }
    {
      intros o H1.
      inversion H1; try eauto.
      subst.
      assert (Some (l4, l5) = Some (l1, l2)); eauto.
      inversion H.
      subst.
      assert (Some (l6, l7) = None); eauto.
      inversion H0.
    }
    {
      intros o H1.
      inversion H1.
      {
        subst.
        eapply IHm.
        exact H4.
      }
      {
        subst.
        assert (None = (Some (l1, l2))) by (apply IHm; assumption).
        inversion H.
      }
      {
        subst.
        assert (None = (Some (l1, l2))) by (apply IHm; assumption).
        inversion H.
      }
    }
    {
      intros o H1.
      inversion H1; try eauto.
      subst.
      assert (Some (l4, l5) = None); eauto.
      inversion H.
    }
    {
      intros o H1.
      inversion H1.
      {
        subst.
        now eapply IHm1.
      }
      {
        subst.
        now eapply IHm2.
      }
      {
        reflexivity.
      }
    }
    {
      intros o' H.
      inversion H.
      {
        subst.
        reflexivity.
      }
      {
        subst.
        assert (Some (l1, l2) = None) by eauto.
        inversion H0.
      }
    }
    {
      intros o H.
      inversion H; subst.
      {
        now assert (None = Some (l1, l2)) by eauto.
      }
      {
        assert (Some (l6, l7) = Some (l1, l2)) by eauto.
        inversion H0.
        subst.
        assert (Some (l8, l9) = Some (l3, l4)) by eauto.
        now inversion H3.
      }
    }
  Qed.

  Lemma StarStarNeverStrong : forall p l o, PegMatch p l o -> forall p', p = (PossesiveStar (PossesiveStar p')) -> False.
    intros P l o H.
    induction H; try discriminate.
    {
      intros p' Heq.
      inversion Heq.
      subst.
      inversion H.
    }
    {
      intros p' Heq.
      inversion Heq.
      subst.
      eapply IHPegMatch2.
      reflexivity.
    }
  Qed.

  Lemma StarStarNever : forall p l o, PegMatch (PossesiveStar (PossesiveStar p)) l o -> False.
    eauto using StarStarNeverStrong.
  Qed.

  Lemma StarWeakenOrderedChoiceStrong :
    forall p l o, PegMatch p l o ->
             forall P1 P2 l1 l2 l3 l4, p = (PossesiveStar (OrderedChoice P1 P2)) -> l = l1 -> o = (Some (l2, l3)) ->
                                  (forall l4 l5 l6, WeakenMatch (OrderedChoice P1 P2) l4 l5 l6 /\ WeakenFail (OrderedChoice P1 P2) l4 l5) -> PegMatch p (l1 ++ l4) (Some (l2, l3 ++ l4)).
    intros p l o m.
    induction m; try discriminate.
    {
      intros P1 P2 l1 l2 l3 l4 Heq1 Heq2 Heq3 HWeaken.
      inversion Heq1.
      inversion Heq2.
      inversion Heq3.
      subst.
      apply StarEnd.
      assert (WeakenFail (OrderedChoice P1 P2) l3 l4) by (apply HWeaken; exact []).
      unfold WeakenFail in H0.
      now apply H0.
    }
    {
      intros P1 P2 l5 l6 l7 l8 Heq1 Heq2 Heq3 HWeaken.
      inversion Heq1.
      inversion Heq2.
      inversion Heq3.
      subst.
      apply list_split in m1 as HLS.
      subst l5.
      assert (PegMatch (OrderedChoice P1 P2) (l1 ++ l2 ++ l8) (Some (l1, l2 ++ l8))).
      {
        assert (WeakenMatch (OrderedChoice P1 P2) l1 l2 l8) by (apply HWeaken; exact []).
        unfold WeakenMatch in H0.
        now apply H0.
      }
      assert (PegMatch (PossesiveStar (OrderedChoice P1 P2)) (l2 ++ l8) (Some (l3, l7 ++ l8))) by (eapply IHm2; eauto).
      rewrite <- app_assoc.
      econstructor. { exact H0. } { exact H1.}
    }
  Qed.

  Lemma StarWeakenOrderedChoice : forall P1 P2 l1 l2 l3, (forall l4 l5 l6, WeakenMatch (OrderedChoice P1 P2) l4 l5 l6 /\ WeakenFail (OrderedChoice P1 P2) l4 l5) -> WeakenStar (OrderedChoice P1 P2) l1 l2 l3.
    intros P1 P2 l1 l2 l3 H1 H2.
    remember (PossesiveStar (OrderedChoice P1 P2)).
    remember (l1 ++ l2).
    rewrite app_assoc.
    remember (Some (l1, l2)).
    eapply StarWeakenOrderedChoiceStrong; eauto.
  Qed.

  Lemma MatchWeakenStrong : forall P l1 l2 l3, WeakenMatch P l1 l2 l3 /\ WeakenFail P l1 l2 /\ BlameConcatenee P l1 l2 l3 /\ ((forall l4 l5 l6, WeakenMatch P l4 l5 l6 /\ WeakenFail P l4 l5) -> WeakenStar P l1 l2 l3).
      intros P.
      induction P.
      {
        intros l1 l2 l3.
        repeat split.
        (* { *)
        (*   intros H. *)
        (*   inversion H. *)
        (*   subst. *)
        (*   constructor. *)
        (* } *)
        {
          intros H.
          inversion H.
          subst.
          apply CharS.
        }
        {
          intros H.
          inversion H.
          {
            subst.
            now constructor.
          }
        }
        {
          unfold BlameConcatenee.
          intros P' H1 H2.
          inversion H1.
          subst.
          inversion H2.
          {
            subst.
            inversion H4.
            subst.
            apply eq_dec_correct in H3.
            contradiction.
          }
          {
            subst.
            inversion H3.
            now subst.
          }
        }
        {
          intros H.
          unfold WeakenStar.
          apply StarWeakenBase1.
        }
      }
      {
        intros l1 l2 l3.
        repeat split.
        {
          intros H.
          inversion H.
          subst.
          apply list_split in H6 as HLS.
          rewrite HLS in H6.
          assert (WeakenMatch P2 l6 l2 l3) by apply IHP2.
          unfold WeakenMatch in H0.
          apply H0 in H6.
          rewrite <- app_assoc in H4.
          rewrite app_assoc in H4.
          apply list_split in H4 as HLS1.
          rewrite HLS1 in H4.
          assert (WeakenMatch P1 l4 l5 l3) by apply IHP1.
          unfold WeakenMatch in H1.
          apply H1 in H4.
          rewrite HLS in H4.
          rewrite <- app_assoc in H4.
          rewrite <- app_assoc.
          eapply CatS.
          exact H4.
          exact H6.
        }
        {
          unfold WeakenFail.
          intros H.
          inversion H.
          {
            subst.
            assert (WeakenFail P1 l1 l2) by (apply IHP1; exact []).
            unfold WeakenFail in H0.
            eapply CatFail1.
            now apply H0.
          }
          {
            subst.
            assert (BlameConcatenee P1 l1 l4 l5) by (apply IHP1).
            unfold BlameConcatenee in H0.
            apply list_split in H2 as HLS. subst l1.
            assert (WeakenMatch P1 l4 l5 l2) by apply IHP1.
            unfold WeakenMatch in H1.
            apply H1 in H2.
            assert (WeakenFail P2 l5 l2) by (apply IHP2; exact []).
            unfold WeakenFail in H3.
            assert (PegMatch P2 (l5 ++ l2) None) by auto.
            eapply CatFail2.
            rewrite <- app_assoc.
            exact H2.
            exact H5.
          }
        }
        {
          unfold BlameConcatenee.
          intros P' H1 H2.
          inversion H1.
          subst.
          apply ConcatDistrEquivalentFail in H2 as HFail.
          apply list_split in H1 as HLS.
          assert (BlameConcatenee P1 l1 l4 l5) by apply IHP1.
          unfold BlameConcatenee in H.
          assert (PegMatch (Concat P2 P') l5 None) by eauto.
          assert (BlameConcatenee P2 l5 l6 l3) by apply IHP2.
          unfold BlameConcatenee in H3.
          now apply H3.
        }
        {
          apply StarWeakenConcat.
        }
      }
      {
        intros l1 l2 l3.
        repeat split.
        {
          unfold WeakenMatch.
          intros H.
          assert (WeakenStar P l1 l2 l3).
          {
            apply IHP.
            split.
            apply IHP.
            apply IHP.
            exact [].
          }
          eauto.
        }
        {
          intros H.
          inversion H.
        }
        {
          unfold BlameConcatenee.
          intros P' H1 H2.
          inversion H2.
          {
            subst.
            assert (Some (l2, l3) = None); eauto using MatchDeterministic.
            discriminate.
          }
          {
            subst.
            assert (Some (l2, l3) = Some (l4, l5)); eauto using MatchDeterministic.
            inversion H.
            assumption.
          }
        }
        {
          intros H1 H2.
          apply StarStarNever in H2.
          contradiction.
        }
      }
      {
        intros l1 l2 l3.
        repeat split.
        {
          intros H.
          inversion H.
          {
            subst.
            assert (WeakenMatch P1 l1 l2 l3) by apply IHP1.
            eauto using PegMatch.
          }
          {
            subst.
            assert (WeakenMatch P2 l1 l2 l3) by apply IHP2.
            assert (WeakenFail P1 (l1 ++ l2) l3) by (apply IHP1; exact []).
            unfold WeakenMatch in H0.
            unfold WeakenFail in H1.
            assert (PegMatch P1 ((l1 ++ l2) ++ l3) None) by eauto.
            rewrite <- app_assoc in H2.
            eapply ChoiceR; eauto.
          }
        }
        {
          intros H.
          inversion H.
          {
            subst.
            assert (WeakenFail P1 l1 l2) by (apply IHP1; exact []).
            assert (WeakenFail P2 l1 l2) by (apply IHP2; exact []).
            unfold WeakenFail in H0.
            unfold WeakenFail in H1.
            constructor. { now apply H0. } { now apply H1. }
          }
        }
        {
          intros P H1 H2.
          inversion H2.
          {
            subst.
            assert (None = (Some (l2, l3))); eauto using MatchDeterministic.
            discriminate.
          }
          {
            subst.
            assert (Some (l2, l3) = Some (l4, l5)); eauto using MatchDeterministic.
            now inversion H.
          }
        }
        {
          intros H1 H2.
          apply StarWeakenOrderedChoice.
          {
            intros l4 l5 l6. split. apply H1. apply H1. exact [].
          }
          {
            exact H2.
          }
        }
      }
  Qed.

  Lemma MatchWeaken' : forall P l1 l2 l3, WeakenMatch P l1 l2 l3 /\ WeakenFail P l1 l2 /\ BlameConcatenee P l1 l2 l3.
    intros P l1 l2 l3.
    repeat split.
    {
      eapply MatchWeakenStrong.
    }
    {
      eapply MatchWeakenStrong. exact [].
    }
    {
      eapply MatchWeakenStrong.
    }
  Qed.

  Lemma MatchWeaken : forall P l1 l2 l3, WeakenMatch P l1 l2 l3 /\ WeakenFail P l1 l2.
    intros P l1 l2 l3.
    repeat split; try eapply MatchWeaken'.
    exact [].
  Qed.

  Lemma none_monotonicity : forall P l l', PegMatch P l None -> PegMatch P (l ++ l') None.
    intros P.
    induction P.
    {
      intros.
      destruct l.
      {
        inversion H.
      }
      {
        inversion H.
        subst.
        eauto using PegMatch.
      }
    }
    {
      intros.
      inversion H; subst.
      {
        eauto using PegMatch.
      }
      {
        eapply CatFail2 with (l1 := l1) (l2 := l2 ++ l').
        assert (PegMatch P1 (l ++ l') (Some (l1, l2 ++ l'))).
        {
          assert (WeakenMatch P1 l1 l2 l') by eapply MatchWeaken.
          unfold WeakenMatch in H0.
          apply list_split in H2 as HLS.
          subst.
          rewrite <- app_assoc.
          eapply H0.
          assumption.
        }
        {
          eassumption.
        }
        eauto.
      }
    }
    {
      intros.
      inversion H.
    }
    {
      intros; inversion H; subst.
      constructor; eauto.
    }
  Qed.

  Definition StrengthenFail (P : PEG) (l1 l2 : list Σ) :=  DoesNotMatch P (l1 ++ l2) -> DoesNotMatch P l1.

  Theorem MatchStrengthen : forall P l1 l2, StrengthenFail P l1 l2.
    intros p l1 l2.
    hnf. intros H'.
    hnf. hnf in H'.
    assert (forall o, PegMatch p l1 o \/ ~ (PegMatch p l1 o)).
    {
      intros o.
      eapply lem_peg'.
    }
    assert (PegMatch p l1 None \/ ~ PegMatch p l1 None) by eauto.
    inversion H0.
    {
      intros l0 l3 H''.
      assert (Some (l0, l3) = None) by eauto using PegPartial.
      discriminate.
    }
    {
      intros l1' l2' H''.
      apply H' with (l1 := l1') (l2 := l2' ++ l2).
      eapply list_split in H'' as HLS1.
      assert (PegMatch p (l1' ++ l2') (Some (l1', l2'))) by (rewrite <- HLS1; assumption).
      assert (WeakenMatch p l1' l2' l2). { eapply MatchWeaken. }
      hnf in H3.
      rewrite app_assoc in H3.
      repeat rewrite <- HLS1 in H3.
      now eapply H3.
    }
  Qed.

  Lemma RRStarWeakRStar : forall R l, RegMatch ((RConcat R) (RStar R)) l true ->
                                 RegMatch (RStar R) l true.
    intros.
    inversion H. subst.
    inversion H4. subst.
    inversion H1. inversion H0.
    constructor.
    exists (l1 :: x).
    split.
    {
      subst.
      simpl.
      reflexivity.
    }
    {
      constructor.
      eassumption.
      eassumption.
    }
  Qed.

  Lemma CatRRStarWeakCatRStar :
    forall R1 R2 l, RegMatch (RConcat ((RConcat R1) (RStar R1)) R2) l true ->
               RegMatch (RConcat (RStar R1) R2) l true.
    intros.
    inversion H.
    subst.
    eapply RRStarWeakRStar in H2.
    eauto using RegMatch.
  Qed.

  Lemma RCatAssoc : forall R1 R2 R3 l, RegMatch (RConcat R1 (RConcat R2 R3)) l true <->
                                  RegMatch (RConcat (RConcat R1 R2) R3) l true.
    intros.
    split.
    {
      intros.
      inversion H. subst. inversion H4. subst.
      rewrite app_assoc.
      eauto using RegMatch.
    }
    {
      intros.
      inversion H. subst. inversion H2. subst.
      rewrite <- app_assoc.
      eauto using RegMatch.
    }
  Qed.


  (* Alright, a next task would be: try to clarify what is meant by
     induction on the match object. *)
  (* Another thing to try: memorize all of the pieces, and try to see
     if they will hold.*)
  Lemma star_some_implies_match :
    forall P l1 o (m : PegMatch P l1 o),
    forall l2 l3, o = Some (l2, l3) ->
    forall P', P = PossesiveStar P' ->
    (forall r, LR P' r (PEGREG P' r)) ->
    forall prf suf, prf ++ suf = l3 ->
    (forall r, RegMatch r prf true ->
    RegMatch (PEGREG P r) (l2 ++ prf) true).
    intros P l1 o m.
    induction m.
    all: try discriminate.
    {
      intros.
      inversion H. inversion H0. subst.
      simpl.
      replace prf with ([] ++ prf) by eauto.
      eapply RConcatS. { constructor. exists []. split. eauto. eauto. }
      constructor. assumption.
      constructor.
      assert (StrengthenFail P' prf suf) by eapply MatchStrengthen.
      assert (DoesNotMatch P' prf).
      {
        eapply H2.
        unfold DoesNotMatch. intros.
        assert (None = Some (l1, l2)).
        {
          eapply PegPartial. eassumption. eassumption.
        }
        inversion H5.
      }
      assert (forall r, none_implies_nomatch P' r (PEGREG P' r)) by apply H1.
      unfold none_implies_nomatch in H5.
      unfold LR in H1.
      unfold StrengthenFail in H2.
      eapply H5 with (l1 := prf).
      intros.
      subst.
      assert (StrengthenFail P' prf0 suf0) by eapply MatchStrengthen.
      eapply H6.
      eassumption.
    }
    {
      intros.
      inversion H. inversion H0. subst.
      simpl.
      rewrite <- app_assoc.
      eapply CatRRStarWeakCatRStar.
      eapply RCatAssoc.
      constructor.
      {
        assert (forall r, some_implies_match P' r (PEGREG P' r)) by eapply H1.
        unfold some_implies_match in H2.
        replace l1 with (l1 ++ []) by (rewrite app_nil_r; reflexivity).
        eapply H2 with (prf := []) (l1 := l0 )(suf := l2) (l3 := l2).
        { eassumption. }
        { reflexivity. }
        { constructor. }
      }
      {
        eapply IHm2.
        {
          reflexivity.
        }
        {
          reflexivity.
        }
        {
          assumption.
        }
        {
          reflexivity.
        }
        {
          assumption.
        }
      }
    }
  Qed.

  Lemma heregoes : forall P r__remainder, LR P r__remainder (PEGREG P r__remainder).
    intros P.
    induction P.
    {
      intros r.
      repeat split.
      {
        unfold some_implies_match.
        intros.
        inversion H.
        subst.
        constructor.
        { constructor. }
        { assumption. }
      }
      {
        unfold none_implies_nomatch.
        intros.
        unfold DoesNotMatch in H.
        destruct l1.
        {
          unfold PEGREG.
          constructor.
          intros.
          destruct l1'.
          2: { inversion H0. }
          destruct l1''.
          2: { inversion H0. }
          left.
          constructor.
        }
        destruct (eq_dec c σ) eqn:eqeqdec.
        {
          apply eq_dec_correct in eqeqdec.
          subst.
          exfalso.
          eapply H with (prf := [σ]) (suf := l1).
          { simpl. reflexivity. }
          { econstructor. }
        }
        {
          constructor.
          intros.
          destruct l1'.
          {
            left.
            constructor.
          }
          {
            inversion H0. subst.
            left.
            constructor.
            assumption.
          }
        }
      }
      {
        unfold blame_remainder.
        intros.
        inversion H.
        subst.
        constructor.
        intros.
        destruct l1'.
        {
          left.
          constructor.
        }
        {
          inversion H1. subst.
          destruct l1'.
          {
            right. split. constructor. eauto.
          }
          {
            left. eauto using RegMatch.
          }
        }
      }
    }
    {
      intros r.
      simpl.
      assert (LR P2 r (PEGREG P2 r)). eauto.
      assert (LR P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))). eauto.
      unfold LR.
      repeat split.
      {
        assert (some_implies_match P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) by eapply H0.
        unfold some_implies_match in H1.
        assert (some_implies_match P2 r (PEGREG P2 r)) by eapply H.
        unfold some_implies_match in H2.
        unfold some_implies_match.
        intros. subst.
        inversion H3. subst.
        eapply list_split in H11 as HSplit.
        rewrite <- app_assoc.
        eapply H1.
        eassumption.
        symmetry. rewrite <- app_assoc. eassumption.
        eapply H2.
        eassumption.
        reflexivity.
        eassumption.
      }
      {
        assert (none_implies_nomatch P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) by eapply H0.
        assert (blame_remainder P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) as HBlame by eapply H0.
        unfold none_implies_nomatch in H1.
        assert (none_implies_nomatch P2 r (PEGREG P2 r)) by eapply H.
        unfold none_implies_nomatch in H2.
        unfold none_implies_nomatch.
        intros.
        unfold DoesNotMatch in H3.
        assert (DoesNotMatch P1 l1 \/ exists l2 l3, PegMatch P1 l1 (Some (l2, l3))) by eapply lem_peg.
        inversion H4.
        {
          eapply H1.
          intros.
          subst.
          assert (StrengthenFail P1 prf suf). { eapply MatchStrengthen. }
          eauto.
        }
        {
          inversion H5. inversion H6.
          assert (DoesNotMatch P2 x0 \/ exists l2 l3, PegMatch P2 x0 (Some (l2, l3))) by eapply lem_peg.
          inversion H8.
          {
            assert (RegMatch (PEGREG P2 r) x0 false).
            {
              replace (x0) with (x0 ++ []) by eauto using app_nil_r.
              eapply H2.
              intros. rewrite app_nil_r in H10. subst.
              assert (StrengthenFail P2 prf suf) by eapply MatchStrengthen.
              eauto.
            }
            unfold blame_remainder in HBlame.
            eapply list_split in H7 as HSplit. subst l1.
            eapply HBlame.
            eapply H7.
            eassumption.
          }
          {
            inversion H9.
            inversion H10.
            exfalso. eapply H3 with (prf := l1) (suf := []).
            rewrite app_nil_r. reflexivity.
            eauto using PegMatch.
          }
        }
      }
      {
        assert (blame_remainder P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) by eapply H0.
        assert (blame_remainder P2 r (PEGREG P2 r)) by eapply H.
        unfold blame_remainder.
        intros.
        inversion H3. subst.
        rewrite <- app_assoc in H9.
        rewrite <- app_assoc.
        apply list_split in H11 as HLS. subst l4.
        assert (RegMatch (PEGREG P2 r) (l5 ++ l2) false).
        {
          eapply H2.
          eapply H11.
          eassumption.
        }
        eauto.
      }
    }
    {
      intros r.
      repeat split.
      {
        unfold some_implies_match.
        intros.
        eapply star_some_implies_match; eauto.
      }
      {
        unfold none_implies_nomatch.
        intros.
        unfold DoesNotMatch in H.
      }
    }
