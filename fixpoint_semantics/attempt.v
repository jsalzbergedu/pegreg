Require Import List.
Import ListNotations.

From mathcomp Require Import fintype.
Require Import Basics.
Require Import Lia.

Axiom lem : forall P : Prop, P \/ ~P.

Lemma dn : forall P, ~ ~ P -> P.
  intros P H.
  unfold not in H.
  assert (P \/ ~P) by apply lem.
  inversion H0. { assumption. } { exfalso. apply H. apply H1. } Qed.


Section PegReg.
  Context (Σ : finType).
  Context (eq_dec : Σ -> Σ -> bool).
  Context (eq_dec_correct : forall σ1 σ2, (eq_dec σ1 σ2 = true <-> σ1 = σ2) /\ (eq_dec σ1 σ2 = false <-> σ1 <> σ2)).

  Inductive PEG : Type :=
  | Char (c : Σ)
  | Concat (p1 : PEG) (p2 : PEG)
  | PossesiveStar (p1 : PEG)
  | OrderedChoice (p1 : PEG) (p2 : PEG).

  Inductive SyntacticOrder : PEG -> PEG -> Prop :=
  | ConcatL : forall p1 p2 : PEG, SyntacticOrder p1 (Concat p1 p2)
  | ConcatR : forall p1 p2 : PEG, SyntacticOrder p2 (Concat p1 p2)
  | PossesiveStarLt : forall p1 : PEG, SyntacticOrder p1 (PossesiveStar p1)
  | OrderedChoiceL : forall p1 p2 : PEG, SyntacticOrder p1 (OrderedChoice p1 p2)
  | OrderedChoiceR : forall p1 p2 : PEG, SyntacticOrder p2 (OrderedChoice p1 p2).

  Lemma char_smallest : forall c, forall p, SyntacticOrder p (Char c) -> False.
    intros c p H.
    remember (Char c).
    remember p.
    induction H; discriminate.
  Qed.

  Lemma wf_syntactic_order : well_founded SyntacticOrder.
    unfold well_founded.
    intros a.
    induction a.
    {
      constructor.
      intros y H.
      exfalso.
      eapply char_smallest.
      exact H.
    }
    {
      constructor.
      intros y.
      intros H.
      inversion H; subst; assumption.
    }
    {
      constructor.
      intros y H.
      inversion H.
      subst.
      assumption.
    }
    {
      constructor.
      intros y H.
      inversion H; subst; assumption.
    }
  Qed.

  Inductive RecursiveSyntacticOrder : PEG -> PEG -> Prop :=
  | SyntacticOrderLt : forall p1 p2, SyntacticOrder p1 p2 -> RecursiveSyntacticOrder p1 p2
  | Trans : forall p1 p2 p3, RecursiveSyntacticOrder p1 p2 -> RecursiveSyntacticOrder p2 p3 -> RecursiveSyntacticOrder p1 p3.


  Lemma char_smallest_rec : forall c, forall p, RecursiveSyntacticOrder p (Char c) -> False.
    intros c p H.
    remember (Char c).
    induction H.
    {
      subst.
      apply char_smallest in H.
      assumption.
    }
    {
      subst.
      eauto.
    }
  Qed.

  Check (well_founded_ind (wf_syntactic_order) (fun o =>
                                                  forall e, RecursiveSyntacticOrder o e ->
                                                  Acc RecursiveSyntacticOrder o)).
  Lemma wf_recursive_syntactic_order : well_founded RecursiveSyntacticOrder.
    constructor.
    induction a.
    {
      intros y H.
      now apply char_smallest_rec in H.
    }
    {
      intros y H.
      remember (Concat a1 a2).
      induction H.
      {
        subst.
        inversion H; subst; constructor; intros y HSmaller. { now apply IHa1. } { now apply IHa2. }
      }
      {
        subst.
        assert (Acc RecursiveSyntacticOrder p2) by eauto.
        inversion H1.
        now apply H2.
      }
    }
    {
      intros y H.
      remember (PossesiveStar a).
      induction H.
      {
        subst.
        inversion H.
        subst.
        constructor.
        intros y HSmaller.
        now apply IHa.
      }
      {
        subst.
        assert (Acc RecursiveSyntacticOrder p2) by eauto.
        inversion H1.
        now apply H2.
      }
    }
    {
      intros y H.
      remember (OrderedChoice a1 a2).
      induction H.
      {
        subst.
        inversion H; subst; constructor; intros y HSmaller. { now apply IHa1. } { now apply IHa2. }
      }
      {
        subst.
        assert (Acc RecursiveSyntacticOrder p2) by eauto.
        inversion H1.
        now apply H2.
      }
    }
    Qed.

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

  Lemma app_nil : forall T, forall l1 l2 : list T, l1 ++ l2 = [] -> (l1 = [] /\ l2 = []).
    intros T l1.
    induction l1.
    {
      eauto.
    }
    {
      intros l2 H.
      inversion H.
    }
  Qed.

  Lemma some_eq : forall T, forall t1 t2 : T, t1 = t2 -> Some t1 = Some t2.
    - intros T t1 t2 H.
      rewrite H.
      reflexivity.
  Qed.

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

  Lemma ConcatDistrEquivalentMatch : forall P1 P2 P3, forall l1 l2 l3,
      PegMatch (Concat (Concat P1 P2) P3) l1 (Some (l2, l3)) <->
      PegMatch (Concat P1 (Concat P2 P3)) l1 (Some (l2, l3)).
    intros P1 P2 P3 l1 l2 l3.
    split.
    {
      intros H.
      inversion H.
      subst.
      inversion H4.
      subst.
      rewrite <- app_assoc.
      eapply CatS.
      {
        exact H5.
      }
      {
        eapply CatS. { exact H8. } { exact H6. }
      }
    }
    {
      intros H.
      inversion H.
      subst.
      inversion H6.
      subst.
      rewrite app_assoc.
      eapply CatS.
      {
        eapply CatS.
        {
          exact H4.
        }
        {
          exact H5.
        }
      }
      {
        exact H8.
      }
    }
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

  Lemma PStarWeakerPPStar : forall P l1 l2 l3, PegMatch (PossesiveStar P) l1 (Some (l2, l3)) ->
                                          l2 = [] \/ PegMatch (Concat P (PossesiveStar P)) l1 (Some (l2, l3)).
    intros P l1 l2 l3 H.
    inversion H.
    {
      left.
      reflexivity.
    }
    {
      right.
      subst.
      eapply CatS.
      {
        exact H4.
      }
      {
        exact H5.
      }
    }
  Qed.

  Lemma StarImpliesRemainderFailStrong : forall p, forall l1 o,
      PegMatch p l1 o ->
      forall P l2 l3,
      p = PossesiveStar P ->
      o = Some (l2, l3) ->
      PegMatch P l3 None.
    intros P l1 o H.
    induction H; try discriminate.
    {
      intros P l1 l2 HPeq HOeq.
      inversion HPeq.
      inversion HOeq.
      subst.
      assumption.
    }
    {
      intros P l6 l7 HPeq HOeq.
      inversion HPeq.
      inversion HOeq.
      subst.
      now eapply IHPegMatch2.
    }
    Qed.

    Lemma StarImpliesRemainderFail :
      forall P l1 l2 l3, PegMatch (PossesiveStar P) l1 (Some (l2, l3)) ->
                    PegMatch P l3 None.
      intros P l1 l2 l3 H.
      eauto using StarImpliesRemainderFailStrong.
      Qed.

    Definition WeakenMatch (P : PEG) (l1 l2 l3 : list Σ) :=
      PegMatch P (l1 ++ l2) (Some (l1, l2)) ->
      PegMatch P (l1 ++ l2 ++ l3) (Some (l1, l2 ++ l3)).

    Definition WeakenFail (P : PEG) (l1 l2 : list Σ) :=
      PegMatch P l1 None -> PegMatch P (l1 ++ l2) None.

    Definition StarWillFailPrefixes (p : PEG) := forall l o, PegMatch (PossesiveStar p) l o ->
                                                        forall l1 l2, o = Some (l1, l2) -> forall l3 l4, l3 ++ l4 = l2 -> (l3 = [] \/ PegMatch p l3 None).

    Definition BlameConcatenee (P : PEG) (l1 l2 l3: list Σ) :=
      forall P', PegMatch P l1 (Some (l2, l3)) -> PegMatch (Concat P P') l1 None ->
            PegMatch P' l3 None.

    Definition WeakenStar (P : PEG) (l1 l2 l3 : list Σ) :=
      PegMatch (PossesiveStar P) (l1 ++ l2) (Some (l1, l2)) ->
        PegMatch (PossesiveStar P) (l1 ++ l2 ++ l3) (Some (l1, l2 ++ l3)).

    Lemma catnil : forall T, forall l1 l2 : list T, [] = l1 ++ l2 -> l1 = [].
      intros T l1.
      induction l1; try eauto.
      intros l2 H.
      inversion H.
    Qed.


    Fixpoint foldl {T O} (l : list T) (f : T -> O -> O) (z : O) : O :=
      match l with
      | [] => z
      | h :: t => f h (foldl t f z)
      end.


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

    Lemma taileq : forall {T}, forall l1 l2 l3 : list T, l1 ++ l2 = l1 ++ l3 -> l2 = l3.
      intros T l1.
      induction l1; try eauto.
      intros l2 l3 H.
      simpl in H.
      inversion H.
      now apply IHl1.
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
        (* { *)
        (*   intros H. *)
        (*   inversion H. *)
        (*   subst. *)
        (*   eapply CatS. *)
        (*   { *)
        (*     rewrite <- app_assoc. *)
        (*     apply IHP1 with (l3 := l3). *)
        (*     replace (l4 ++ (l6 ++ l2) ++ l3) with ((l4 ++ l6) ++ l2 ++ l3). *)
        (*     2: { *)
        (*       rewrite <- app_assoc. *)
        (*       symmetry. *)
        (*       now rewrite <- app_assoc. *)
        (*     } *)
        (*     assert (l5 = (l6 ++ l2) ++ l3) by (apply list_split in H6; rewrite <- app_assoc; assumption). *)
        (*     rewrite H0 in H4. *)
        (*     assumption. *)
        (*   } *)
        (*   { *)
        (*     apply IHP2 with (l3 := l3). *)
        (*     apply list_split in H6 as HLS. *)
        (*     now rewrite HLS in H6. *)
        (*   } *)
        (* } *)
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

    Definition StrengthenFail (P : PEG) (l1 l2 : list Σ) :=  DoesNotMatch P (l1 ++ l2) -> DoesNotMatch P l1.

    Lemma splitcases : forall T, forall (l1 l2 l3 l4 : list T), l1 ++ l2 = l3 ++ l4 ->
                                                      ((exists restl3, (l1 ++ restl3) = l3 /\ restl3 ++ l4 = l2) \/ (exists begl4, l3 ++ begl4 = l1 /\ begl4 ++ l2 = l4)).
      intros T l1.
      induction l1.
      {
        intros l2 l3 l4 H.
        simpl in H.
        simpl.
        left.
        exists l3; split; symmetry; auto.
      }
      {
        intros l2 l3 l4 H.
        destruct l3.
        {
          destruct l4. { simpl in H. inversion H. }
          simpl in H.
          inversion H.
          assert (l1 ++ l2 = [] ++ l4) by auto.
          assert ((exists restl3 : list T, l1 ++ restl3 = [] /\ restl3 ++ l4 = l2) \/ (exists begl4 : list T, [] ++ begl4 = l1 /\ begl4 ++ l2 = l4)) by auto.
          inversion H3.
          {
            inversion H4.
            inversion H5.
            subst.
            right.
            exists (t :: l1). split. { reflexivity. } { simpl. reflexivity. }
          }
          {
            inversion H4.
            inversion H5.
            right.
            subst.
            simpl.
            exists (t :: x); auto.
          }
        }
        {
          simpl in H.
          inversion H.
          subst.
          assert ((exists restl3 : list T, l1 ++ restl3 = l3 /\ restl3 ++ l4 = l2) \/ (exists begl4 : list T, l3 ++ begl4 = l1 /\ begl4 ++ l2 = l4)) by auto.
          inversion H0.
          {
            inversion H1.
            inversion H3.
            subst.
            left.
            exists x; auto.
          }
          {
            inversion H1.
            inversion H3.
            subst.
            right.
            exists x; auto.
          }
        }
      }
    Qed.

    Theorem MatchStrengthen : forall P l1 l2, StrengthenFail P l1 l2.
      intros p l1 l2.
      hnf. intros H'.
      hnf. hnf in H'.
      assert (forall o, PegMatch p l1 o \/ ~ (PegMatch p l1 o)).
      {
        intros o.
        eapply lem.
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

  Lemma allmatch_eq : forall p : PEG, forall l1 l2 : list Σ, PegMatch p l1 (Some (l2, [])) -> l1 = l2.
    - intros p l1 l2 m.
      apply list_split in m.
      now rewrite <- app_nil_r.
      Qed.

  Inductive REG : Type :=
  | REmp
  | RChar (c : Σ)
  | RConcat (r1 : REG) (r2 : REG)
  | RUnion (r1 : REG) (r2 : REG)
  | RStar (r : REG)
  | RIntersection (r1 : REG) (r2 : REG)
  | RNeg (r1 : REG).

  Inductive RegMatch : REG -> list Σ -> bool -> Prop :=
  | REmpS : RegMatch REmp [] true
  | REmpF : forall c, forall t : list Σ, RegMatch REmp (c :: t) false
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

  Definition RDeterministic (r : REG) := forall l b, RegMatch r l b -> forall b', RegMatch r l b' -> b = b'.

  Definition RStarDeterministic (r : REG) := forall l b, RegMatch (RStar r) l b -> forall b', RegMatch (RStar r) l b' -> b = b'.

  Lemma ConcatFactor : forall {T}, forall l (l1 : list T) a, concat (a :: l) = l1 -> l1 = a ++ (concat l).
    intros T l.
    induction l.
    {
      intros l1 a H.
      inversion H.
      simpl.
      reflexivity.
    }
    {
      intros l1 a1 H.
      simpl in H.
      simpl.
      now symmetry.
    }
  Qed.

  Lemma InImpliesAll : forall T, forall l : list T, forall x (P : T -> Prop), In x l -> Forall P l -> P x.
    intros T l.
    induction l.
    {
      intros x P H1 H2.
      inversion H1.
    }
    {
      intros x P H1 H2.
      inversion H1.
      {
        subst x.
        now inversion H2.
      }
      {
        inversion H2.
        subst.
        eapply IHl; eauto.
      }
    }
    Qed.

  Lemma REmpStarImpossibleCaseStrong : RDeterministic REmp ->
                                       forall l, ((exists l', concat l' = l /\ Forall (fun l : list Σ => RegMatch REmp l true) l') /\ (forall l', concat l' = l -> exists e : list Σ, In e l' /\ RegMatch REmp e false)) -> False.
    intros RDet l.
    destruct l.
    {
      intros HImp.
      inversion HImp.
      assert (exists e : list Σ, In e [] /\ RegMatch REmp e false) by eauto.
      inversion H1.
      inversion H2.
      inversion H3.
    }
    {
      intros HImp.
      inversion HImp.
      inversion H.
      inversion H1.
      assert (exists e : list Σ, In e x /\ RegMatch REmp e false) by eauto.
      inversion H4.
      inversion H5.
      inversion H7.
      subst x0.
      inversion H5.
      assert (RegMatch REmp (c :: t) true). { eapply InImpliesAll with (x := (c :: t)). exact H8. exact H3. }
      eauto.
    }
    Qed.

  Lemma RCharStarImpossibleCaseStrong : forall c, RDeterministic (RChar c) ->
                                       forall l, ((exists l', concat l' = l /\ Forall (fun l : list Σ => RegMatch (RChar c) l true) l') /\ (forall l', concat l' = l -> exists e : list Σ, In e l' /\ RegMatch (RChar c) e false)) -> False.
    intros c RDet l.
    destruct l.
    {
      intros HImp.
      inversion HImp.
      assert (exists e : list Σ, In e [] /\ RegMatch (RChar c) e false) by eauto.
      inversion H1.
      inversion H2.
      inversion H3.
    }
    {
      intros HImp.
      inversion HImp.
      inversion H.
      inversion H1.
      assert (exists e, In e x /\ RegMatch (RChar c) e false); eauto.
      inversion H4.
      inversion H5.
      assert (RegMatch (RChar c) x0 true). { eapply InImpliesAll with (x := x0). exact H6. exact H3. }
      eauto.
    }
    Qed.

  Lemma RConcatImpossibleCaseStrong : forall r1 r2, RDeterministic (RConcat r1 r2) ->
                                               forall l, ((exists l', concat l' = l /\ Forall (fun l : list Σ => RegMatch (RConcat r1 r2) l true) l') /\ (forall l', concat l' = l -> exists e : list Σ, In e l' /\ RegMatch (RConcat r1 r2) e false)) -> False.
    intros r1 r2 RDet l.
    destruct l.
    {
      intros HImp.
      inversion HImp.
      assert (exists e : list Σ, In e [] /\ RegMatch (RConcat r1 r2) e false) by eauto.
      inversion H1.
      inversion H2.
      inversion H3.
    }
    {
      intros HImp.
      inversion HImp.
      inversion H.
      inversion H1.
      assert (exists e, In e x /\ RegMatch (RConcat r1 r2) e false); eauto.
      inversion H4.
      inversion H5.
      assert (RegMatch (RConcat r1 r2) x0 true). { eapply InImpliesAll with (x := x0). exact H6. exact H3. }
      eauto.
    }
    Qed.

  Lemma RUnionImpossibleCaseStrong : forall r1 r2, RDeterministic (RUnion r1 r2) ->
                                               forall l, ((exists l', concat l' = l /\ Forall (fun l : list Σ => RegMatch (RUnion r1 r2) l true) l') /\ (forall l', concat l' = l -> exists e : list Σ, In e l' /\ RegMatch (RUnion r1 r2) e false)) -> False.
    intros r1 r2 RDet l.
    destruct l.
    {
      intros HImp.
      inversion HImp.
      assert (exists e : list Σ, In e [] /\ RegMatch (RUnion r1 r2) e false) by eauto.
      inversion H1.
      inversion H2.
      inversion H3.
    }
    {
      intros HImp.
      inversion HImp.
      inversion H.
      inversion H1.
      assert (exists e, In e x /\ RegMatch (RUnion r1 r2) e false); eauto.
      inversion H4.
      inversion H5.
      assert (RegMatch (RUnion r1 r2) x0 true). { eapply InImpliesAll with (x := x0). exact H6. exact H3. }
      eauto.
    }
    Qed.

  Lemma RIntersectionImpossibleCaseStrong : forall r1 r2, RDeterministic (RIntersection r1 r2) ->
                                               forall l, ((exists l', concat l' = l /\ Forall (fun l : list Σ => RegMatch (RIntersection r1 r2) l true) l') /\ (forall l', concat l' = l -> exists e : list Σ, In e l' /\ RegMatch (RIntersection r1 r2) e false)) -> False.
    intros r1 r2 RDet l.
    destruct l.
    {
      intros HImp.
      inversion HImp.
      assert (exists e : list Σ, In e [] /\ RegMatch (RIntersection r1 r2) e false) by eauto.
      inversion H1.
      inversion H2.
      inversion H3.
    }
    {
      intros HImp.
      inversion HImp.
      inversion H.
      inversion H1.
      assert (exists e, In e x /\ RegMatch (RIntersection r1 r2) e false); eauto.
      inversion H4.
      inversion H5.
      assert (RegMatch (RIntersection r1 r2) x0 true). { eapply InImpliesAll with (x := x0). exact H6. exact H3. }
      eauto.
    }
    Qed.

  Lemma RStarImpossibleCaseStrong : forall r1, RDeterministic (RStar r1) ->
                                               forall l, ((exists l', concat l' = l /\ Forall (fun l : list Σ => RegMatch (RStar r1) l true) l') /\ (forall l', concat l' = l -> exists e : list Σ, In e l' /\ RegMatch (RStar r1) e false)) -> False.
    intros r1 RDet l.
    destruct l.
    {
      intros HImp.
      inversion HImp.
      assert (exists e : list Σ, In e [] /\ RegMatch (RStar r1) e false) by eauto.
      inversion H1.
      inversion H2.
      inversion H3.
    }
    {
      intros HImp.
      inversion HImp.
      inversion H.
      inversion H1.
      assert (exists e, In e x /\ RegMatch (RStar r1) e false); eauto.
      inversion H4.
      inversion H5.
      assert (RegMatch (RStar r1) x0 true). { eapply InImpliesAll with (x := x0). exact H6. exact H3. }
      eauto.
    }
    Qed.

  Lemma RNegImpossibleCaseStrong : forall r1, RDeterministic (RNeg r1) ->
                                               forall l, ((exists l', concat l' = l /\ Forall (fun l : list Σ => RegMatch (RNeg r1) l true) l') /\ (forall l', concat l' = l -> exists e : list Σ, In e l' /\ RegMatch (RNeg r1) e false)) -> False.
    intros r1 RDet l.
    destruct l.
    {
      intros HImp.
      inversion HImp.
      assert (exists e : list Σ, In e [] /\ RegMatch (RNeg r1) e false) by eauto.
      inversion H1.
      inversion H2.
      inversion H3.
    }
    {
      intros HImp.
      inversion HImp.
      inversion H.
      inversion H1.
      assert (exists e, In e x /\ RegMatch (RNeg r1) e false); eauto.
      inversion H4.
      inversion H5.
      assert (RegMatch (RNeg r1) x0 true). { eapply InImpliesAll with (x := x0). exact H6. exact H3. }
      eauto.
    }
    Qed.

  Lemma RNegImpossibleCase : forall r1, RDeterministic (RNeg r1) -> forall l, RegMatch (RStar (RNeg r1)) l true -> RegMatch (RStar (RNeg r1)) l false -> False.
    intros r1 HDet l HTrue HFalse.
    eapply RNegImpossibleCaseStrong.
    {
      exact HDet.
    }
    {
      inversion HTrue.
      inversion HFalse.
      repeat split; eauto.
    }
    Qed.

  Lemma RStarStarImpossibleCase : forall r1, RDeterministic (RStar r1) -> forall l, RegMatch (RStar (RStar r1)) l true -> RegMatch (RStar (RStar r1)) l false -> False.
    intros r1 HDet l HTrue HFalse.
    eapply RStarImpossibleCaseStrong.
    {
      exact HDet.
    }
    {
      inversion HTrue.
      inversion HFalse.
      repeat split; eauto.
    }
    Qed.

  Lemma RConcatStarImpossibleCase : forall r1 r2, RDeterministic (RConcat r1 r2) -> forall l, RegMatch (RStar (RConcat r1 r2)) l true -> RegMatch (RStar (RConcat r1 r2)) l false -> False.
    intros r1 r2 HDet l HTrue HFalse.
    eapply RConcatImpossibleCaseStrong.
    {
      exact HDet.
    }
    {
      inversion HTrue.
      inversion HFalse.
      repeat split; eauto.
    }
    Qed.

  Lemma RIntersectionStarImpossibleCase : forall r1 r2, RDeterministic (RIntersection r1 r2) -> forall l, RegMatch (RStar (RIntersection r1 r2)) l true -> RegMatch (RStar (RIntersection r1 r2)) l false -> False.
    intros r1 r2 HDet l HTrue HFalse.
    eapply RIntersectionImpossibleCaseStrong.
    {
      exact HDet.
    }
    {
      inversion HTrue.
      inversion HFalse.
      repeat split; eauto.
    }
    Qed.

  Lemma RUnionStarImpossibleCase : forall r1 r2, RDeterministic (RUnion r1 r2) -> forall l, RegMatch (RStar (RUnion r1 r2)) l true -> RegMatch (RStar (RUnion r1 r2)) l false -> False.
    intros r1 r2 HDet l HTrue HFalse.
    eapply RUnionImpossibleCaseStrong.
    {
      exact HDet.
    }
    {
      inversion HTrue.
      inversion HFalse.
      repeat split; eauto.
    }
    Qed.

  Lemma RCharStarImpossibleCase : forall c, RDeterministic (RChar c) -> forall l, RegMatch (RStar (RChar c)) l true -> RegMatch (RStar (RChar c)) l false -> False.
    intros c HDet l HTrue HFalse.
    eapply RCharStarImpossibleCaseStrong.
    {
      exact HDet.
    }
    {
      inversion HTrue.
      inversion HFalse.
      repeat split; eauto.
    }
    Qed.

  (* By an online source *)
  Lemma length_nil: forall A:Type, forall l:list A,
      l = nil <-> length l = 0.
  Proof.
    split; intros H.
    rewrite H; simpl; auto.
    destruct l. auto.
    contradict H; simpl.
    apply sym_not_eq; apply O_S.
  Qed.

  Lemma LOrder : forall {T}, forall l1 l2 l3 : list T, l1 ++ l2 = l3 -> length l1 <= length l3.
    intros T l1.
    induction l1.
    {
      intros l2 l3 H.
      simpl.
      lia.
    }
    {
      intros l2 l3 H.
      simpl in H.
      destruct l3.
      {
        inversion H.
      }
      {
        inversion H.
        simpl.
        apply le_n_S.
        rewrite H2.
        eapply IHl1.
        exact H2.
      }
    }
    Qed.

  Lemma Reg_Det : forall r, RDeterministic r /\ (RDeterministic r -> RStarDeterministic r).
    intros r.
    induction r.
    {
      repeat split.
      {
        intros l b H b' H'.
        inversion H. { inversion H'. { reflexivity. } { subst. inversion H3. }} { subst. inversion H'. reflexivity.  }
      }
      {
        intros Hdet.
        intros l b Hs b' H'.
        destruct b; destruct b'; try reflexivity.
        {
          inversion Hs.
          subst.
          inversion H'.
          subst.
          exfalso.
          eapply REmpStarImpossibleCaseStrong; repeat split; eauto.
        }
        {
          inversion Hs. inversion H'. subst. exfalso. eapply REmpStarImpossibleCaseStrong; repeat split; eauto.
        }
      }
    }
    {
      repeat split.
      {
        intros l b H b' H'.
        inversion H.
        { inversion H'. { reflexivity. } { subst. inversion H3. } { subst. inversion H5. subst. apply eq_dec_correct in H4. contradiction.  } { subst. inversion H3. } }
        { subst. inversion H'. { reflexivity. } }
        { subst. inversion H'. { subst. apply eq_dec_correct in H1. contradiction. } { reflexivity. } { reflexivity. } }
        { subst. inversion H'. { reflexivity. } { reflexivity. } }
      }
      {
        intros HDet l b Hs1 b' Hs2.
        destruct b; destruct b'; try reflexivity; try (exfalso; eapply RCharStarImpossibleCase; eauto).
      }
    }
    {
      repeat split.
      {
        intros l b H b' H'.
        inversion IHr1.
        inversion IHr2.
        destruct b; destruct b'; try reflexivity; inversion H; inversion H'; subst; assert (RegMatch r1 l1 false \/ RegMatch r1 l1 true /\ RegMatch r2 l2 false) by eauto; inversion H4; try eauto; inversion H5; eauto.
      }
      {
        intros H.
        intros l b HMatch1 b' HMatch2.
        inversion IHr1.
        inversion IHr2.
        destruct b; destruct b'; try reflexivity; exfalso; eauto using RConcatStarImpossibleCase.
      }
    }
    {
      repeat split.
      {
        intros l b H b' H'.
        inversion IHr1.
        inversion IHr2.
        destruct b; destruct b'; try reflexivity; inversion H; inversion H'; eauto.
      }
      {
        intros RUnion.
        inversion IHr1. inversion IHr2.
        intros l b HMatch b' HMatch'.
        destruct b; destruct b'; try reflexivity; exfalso; eauto using RUnionStarImpossibleCase.
      }
    }
    {
      repeat split.
      {
        intros l b H b' H'.
        inversion IHr.
        assert (RStarDeterministic r) by eauto.
        eauto.
      }
      {
        intros H.
        inversion IHr.
        intros l b HMatch1 b' HMatch2.
        destruct b; destruct b'; try reflexivity; exfalso; eauto using RStarStarImpossibleCase.
      }
    }
    {
      repeat split.
      {
        intros l b H b' H'.
        inversion IHr1.
        inversion IHr2.
        destruct b; destruct b'; try reflexivity; inversion H; inversion H'; subst; assert (true = false) by eauto; discriminate.
      }
      {
        intros H.
        inversion IHr1.
        inversion IHr2.
        intros l b HMatch1 b' HMatch2.
        destruct b; destruct b'; try reflexivity; exfalso; eauto using RIntersectionStarImpossibleCase.
      }
    }
    {
      repeat split.
      {
        intros l b H b' H'.
        inversion IHr.
        destruct b; destruct b'; try reflexivity; inversion H; inversion H'; subst; assert (true = false) by eauto; discriminate.
      }
      {
        intros H.
        inversion IHr.
        intros l b HMatch1 b' HMatch2.
        destruct b; destruct b'; try reflexivity; exfalso; eauto using RNegImpossibleCase.
      }
    }
  Qed.

  Theorem reg_det : forall r, RDeterministic r.
    intros r.
    assert (forall r0, RDeterministic r0 /\ (RDeterministic r0 -> RStarDeterministic r0)) by eapply Reg_Det.
    assert (RDeterministic r /\ (RDeterministic r -> RStarDeterministic r)) by eauto.
    now inversion H0.
  Qed.

  Definition RTotal (r : REG) := forall l, RegMatch r l true \/ RegMatch r l false.

  Lemma SplitEmpty : forall {T}, forall l1 l2 : list T, l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
    intros T l1.
    induction l1.
    {
      intros l2 H.
      simpl in H.
      rewrite H.
      split; reflexivity.
    }
    {
      intros l2 H.
      simpl in H.
      inversion H.
    }
  Qed.

  Lemma RegCatEquivalence : forall r1 r2 r3 l b, RTotal r1 -> RTotal r2 -> RTotal (RConcat r1 r2) -> RTotal r3 -> RegMatch (RConcat r1 (RConcat r2 r3)) l b -> RegMatch (RConcat (RConcat r1 r2) r3) l b.
    intros r1 r2 r3 l b HT1 HTCat HT2 HT3 H.
    destruct b eqn:Eqb.
    {
      inversion H.
      subst.
      inversion H4.
      subst.
      replace (l1 ++ l0 ++ l3) with ((l1 ++ l0) ++ l3) by eauto using app_assoc.
      constructor. { constructor; assumption. } assumption.
    }
    {
      constructor.
      intros left1 right1 Heql1.
      assert (RegMatch (RConcat r1 r2) left1 true \/ RegMatch (RConcat r1 r2) left1 false) by eauto.
      inversion H0; try (left; assumption).
      inversion H1.
      subst.
      rename l1 into left2. rename l2 into right2.
      rewrite <- app_assoc in H.
      inversion H.
      subst.
      assert (RegMatch r1 left2 false \/ RegMatch r1 left2 true /\ RegMatch (RConcat r2 r3) (right2 ++ right1) false) by eauto.
      inversion H2.
      {
        assert (RDeterministic r1) by eauto using reg_det.
        assert (false = true) by eauto.
        discriminate.
      }
      {
        inversion H3.
        right. split; try assumption.
        inversion H8.
        subst.
        assert (RegMatch r2 right2 false \/ RegMatch r2 right2 true /\ RegMatch r3 right1 false) by eauto.
        inversion H9; try (inversion H10; assumption).
        assert (RDeterministic r2) by eauto using reg_det.
        assert (false = true) by eauto.
        discriminate.
      }
    }
  Qed.

  Lemma UnionConcatEquivalence : forall r1 r2 , RTotal r1 -> RTotal r2 -> RTotal (RUnion r1 r2) -> forall r0, RTotal r0 -> forall l b, RegMatch (RUnion (RConcat r1 r0) (RConcat r2 r0)) l b -> RegMatch (RConcat (RUnion r1 r2) r0) l b.
    intros r1 r2 HRT1 HRT2 HRT3 r0 HRT0 l b H.
    destruct b.
    {
      inversion H.
      {
        subst.
        inversion H3.
        subst.
        constructor. { eapply RUnionSL. assumption. } { assumption. }
      }
      {
        subst.
        inversion H3.
        subst.
        constructor. { eapply RUnionSR. assumption. } { assumption. }
      }
    }
    {
      inversion H.
      subst.
      inversion H2.
      subst.
      inversion H4.
      subst.
      constructor.
      intros left1 right1 Hlr1.
      assert (RegMatch (RUnion r1 r2) left1 true \/ RegMatch (RUnion r1 r2) left1 false) by eauto.
      inversion H0; try (left; assumption).
      right.
      split; try assumption.
      subst l.
      inversion H1.
      {
        subst.
        assert (RegMatch r1 left1 false \/ RegMatch r1 left1 true /\ RegMatch r0 right1 false) by eauto.
        inversion H3; try (inversion H7; assumption).
        assert (RDeterministic r1) by eauto using reg_det.
        assert (false = true) by eauto.
        discriminate.
      }
      {
        subst.
        assert (RegMatch r2 left1 false \/ RegMatch r2 left1 true /\ RegMatch r0 right1 false) by eauto.
        inversion H3; try (inversion H7; assumption).
        assert (RDeterministic r2) by eauto using reg_det.
        assert (false = true) by eauto.
        discriminate.
      }
    }
    Qed.

  Lemma RegStarBase : RTotal REmp -> forall l' l, List.concat l' = l -> (l = [] \/ exists x, In x l' /\ RegMatch REmp x false).
    intros HRT l'.
    induction l'.
    {
      intros l H.
      simpl in H.
      rewrite <- H.
      left. reflexivity.
    }
    {
      intros l H1.
      assert ((concat l') = [] \/ exists x : list Σ, In x l' /\ RegMatch REmp x false) by eauto.
      destruct a.
      {
        inversion H.
        {
          left.
          subst.
          simpl.
          assumption.
        }
        {
          right.
          inversion H0.
          inversion H2.
          exists x.
          split. { simpl. now right. } { assumption. }
        }
      }
      {
        right.
        exists (s :: a).
        split. { simpl. left. reflexivity. } { constructor. }
      }
    }
  Qed.

  Lemma RegCharStarBase1 : forall c, RTotal (RChar c) -> forall l' l c2 , eq_dec c c2 = false -> List.concat l' = (c2 :: l) -> (l = [] \/ exists x, In x l' /\ RegMatch (RChar c) x false).
    intros c HRT l'.
    induction l'.
    {
      intros l c2 H1 H2.
      simpl in H2.
      inversion H2.
    }
    {
      intros l c2 H1 H2.
      destruct a.
      {
        simpl in H2.
        simpl.
        right.
        exists []. split. {left. reflexivity.} { constructor. }
      }
      {
        destruct a.
        2: { right. exists (s :: s0 :: a). split. { simpl. left. reflexivity. } { eapply RCharF2. } }
        simpl in H2.
        inversion H2.
        right.
        exists [c2]. split. { simpl. left. reflexivity. } { constructor. assumption. }
      }
    }
  Qed.

  Lemma RegCharStarBase2 : forall c, RTotal (RChar c) -> forall l' l, RegMatch (RStar (RChar c)) l false -> List.concat l' = (c :: l) -> (exists x, In x l' /\ RegMatch (RChar c) x false).
    intros c HRT l'.
    induction l'.
    {
      intros l' l H.
      inversion H.
    }
    {
      intros l H H0.
      inversion H.
      subst.
      destruct a.
      {
        simpl in H0.
        exists []; repeat split; eauto using RegMatch. simpl. left. reflexivity.
      }
      {
        destruct a.
        2: { exists (s :: s0 :: a). split. { simpl. left. reflexivity. } { eapply RCharF2. } }
        simpl in H0.
        inversion H0.
        subst.
        assert (exists e : list Σ, In e l' /\ RegMatch (RChar c) e false) by eauto.
        inversion H1.
        inversion H3.
        exists x. split. { now right. } { assumption. }
      }
    }
  Qed.


  Lemma RRStarWeakRStar : forall r l b, RegMatch (RConcat (RUnion r REmp) (RStar r)) l b -> RegMatch (RStar r) l b.
    intros r l b.
    destruct b.
    {
      intros H.
      inversion H.
      subst.
      inversion H4.
      subst.
      constructor.
      inversion H1.
      inversion H0.
      inversion H2.
      {
        subst.
        exists (l1 :: x).
        split. { simpl. reflexivity. } { now constructor. }
      }
      {
        subst.
        inversion H9.
        subst l1.
        simpl.
        exists x. split; eauto.
      }
    }
    {
      intros H.
      inversion H.
      subst.
      constructor.
      intros ls Hconcat.
      destruct ls.
      {
        simpl in Hconcat.
        subst l.
        assert (RegMatch (RUnion r REmp) [] false \/ RegMatch (RUnion r REmp) [] true /\ RegMatch (RStar r) [] false) by eauto.
        inversion H0.
        {
          assert (RegMatch (RUnion r REmp) [] true) by eauto using RegMatch.
          assert (RDeterministic (RUnion r REmp)) by eauto using reg_det.
          assert (false = true) by eauto.
          discriminate.
        }
        {
          inversion H1.
          assert (RegMatch (RStar r) [] true) by (constructor; exists []; eauto).
          assert (RDeterministic (RStar r)) by eauto using reg_det.
          assert (false = true) by eauto.
          discriminate.
        }
      }
      simpl in Hconcat.
      assert (RegMatch (RUnion r REmp) l0 false \/ RegMatch (RUnion r REmp) l0 true /\ RegMatch (RStar r) (concat ls) false) by eauto.
      inversion H0.
      {
        inversion H1.
        subst.
        exists l0; split; try eauto; try (constructor; reflexivity).
      }
      {
        inversion H1.
        inversion H4.
        subst.
        assert (exists e : list Σ, In e ls /\ RegMatch r e false) by eauto.
        inversion H5.
        inversion H7.
        exists x. split. { simpl. now right. } { assumption. }
      }
    }
  Qed.


  (* H' : concat l' = [a] *)
  (* ============================ *)
  (* exists e : list Σ, In e l' /\ RegMatch (RChar c) e false *)
  Lemma LMembMakesFalse : forall l' c t, RegMatch (RStar (RChar c)) t true -> forall a, eq_dec c a = false -> concat l' = (a :: t) ->
        exists e : list Σ, In e l' /\ RegMatch (RChar c) e false.
    intros l'.
    induction l'.
    {
      intros a t HMatch a0 Heq Hconcat.
      simpl in Hconcat.
      inversion Hconcat.
    }
    {
      intros c t HMatch a0 Heq Hconcat.
      simpl in Hconcat.
      destruct a.
      {
        exists []; split. { left. reflexivity. } { constructor. }
      }
      {
        destruct a.
        2: { exists (s :: s0 :: a). split. { left. reflexivity. } { eapply RCharF2. } }
        inversion Hconcat.
        exists [a0].
        split. { left. reflexivity. } { now constructor. }
      }
    }
  Qed.

  Inductive Splits {T} : list T -> list T -> Type :=
  | SplitsBase l1 : Splits [] l1
  | SplitsRec l1 : forall h t, Splits l1 (h :: t) -> Splits (l1 ++ [h]) t.

  Fixpoint ListOfSplits {T} {l1 l2} (s : Splits l1 l2) : list T :=
    match s with
     | SplitsBase l1 => l1
     | SplitsRec l1 _ _ m => l1 ++ ListOfSplits m
    end.

  (*
  IHr1 : RTotal r1 /\ (RTotal r1 -> forall r2 : REG, RTotal r2 -> RTotal (RConcat r1 r2)) /\ (RTotal r1 -> forall r3 : REG, RTotal r3 -> RTotal (RUnion r1 r3)) /\ (RTotal r1 -> RTotal (RStar r1))
  IHr2 : RTotal r2 /\ (RTotal r2 -> forall r3 : REG, RTotal r3 -> RTotal (RConcat r2 r3)) /\ (RTotal r2 -> forall r3 : REG, RTotal r3 -> RTotal (RUnion r2 r3)) /\ (RTotal r2 -> RTotal (RStar r2))
  ============================
  RTotal (RConcat r1 r2) -> RTotal (RStar (RConcat r1 r2))
   *)

  (* Lemma RegTotalStrong : forall r, RTotal r /\ (RTotal r -> forall r2, RTotal r2 -> RTotal (RConcat r r2)) /\ (RTotal r -> forall r3, RTotal r3 -> RTotal (RUnion r r3)) /\ (RTotal r -> RTotal (RStar r)). *)
  (*   intros r. *)
  (*   induction r. *)
  (*   { *)
  (*     repeat split. *)
  (*     { *)
  (*       intros l. *)
  (*       destruct l. *)
  (*       { *)
  (*         left. *)
  (*         constructor. *)
  (*       } *)
  (*       { *)
  (*         right. *)
  (*         constructor. *)
  (*       } *)
  (*     } *)
  (*     { *)
  (*       intros HTotalEmp r2 HTotalr2 l. *)
  (*       unfold RTotal in HTotalr2. *)
  (*       assert (RegMatch r2 l true \/ RegMatch r2 l false) by eauto. *)
  (*       inversion H. *)
  (*       { *)
  (*         left. *)
  (*         replace l with ([] ++ l) by reflexivity. *)
  (*         constructor; try constructor; try assumption. *)
  (*       } *)
  (*       { *)
  (*         right. *)
  (*         apply RConcatF. *)
  (*         intros l1 l1'' Heq. *)
  (*         destruct l1. *)
  (*         { *)
  (*           right; repeat split. *)
  (*           { *)
  (*             constructor. *)
  (*           } *)
  (*           { *)
  (*             simpl in Heq. *)
  (*             now subst l1''. *)
  (*           } *)
  (*         } *)
  (*         { *)
  (*           left. *)
  (*           constructor. *)
  (*         } *)
  (*       } *)
  (*     } *)
  (*     { *)
  (*       intros HRT1 r0 HRT0 l. *)
  (*       destruct l. *)
  (*       { *)
  (*         left. *)
  (*         eapply RUnionSL. *)
  (*         constructor. *)
  (*       } *)
  (*       { *)
  (*         assert (RegMatch r0 (s :: l) true \/ RegMatch r0 (s :: l) false) by eauto. *)
  (*         inversion H. *)
  (*         { *)
  (*           left. *)
  (*           now eapply RUnionSR. *)
  (*         } *)
  (*         { *)
  (*           right. *)
  (*           apply RUnionF; try assumption; try constructor. *)
  (*         } *)
  (*       } *)
  (*     } *)
  (*     { *)
  (*       intros HRT l. *)
  (*       destruct l eqn:Eql. *)
  (*       { *)
  (*         left. constructor. *)
  (*         exists []. repeat split; eauto. *)
  (*       } *)
  (*       { *)
  (*         right. *)
  (*         constructor. *)
  (*         intros l' H. *)
  (*         assert ((s :: l0) = [] \/ (exists x : list Σ, In x l' /\ RegMatch REmp x false)) by eauto using RegStarBase. *)
  (*         inversion H0. { inversion H1. } { assumption. } *)
  (*       } *)
  (*     } *)
  (*   } *)
  (*   { *)
  (*     repeat split. *)
  (*     { *)
  (*       intros l. *)
  (*       destruct l. *)
  (*       { *)
  (*         right. now constructor. *)
  (*       } *)
  (*       { *)
  (*         destruct l. *)
  (*         { *)
  (*           destruct (eq_dec c s) eqn:Eqd. *)
  (*           { *)
  (*             apply eq_dec_correct in Eqd. *)
  (*             rewrite Eqd. *)
  (*             left. *)
  (*             constructor. *)
  (*           } *)
  (*           { *)
  (*             right. *)
  (*             now constructor. *)
  (*           } *)
  (*         } *)
  (*         { *)
  (*           right. *)
  (*           eapply RCharF2. *)
  (*         } *)
  (*       } *)
  (*     } *)
  (*     { *)
  (*       intros HTotal1 r2 HTotal2 l. *)
  (*       destruct l. *)
  (*       { *)
  (*         right. *)
  (*         constructor. *)
  (*         intros l1' l1'' Hsplit. *)
  (*         eapply SplitEmpty in Hsplit. *)
  (*         inversion Hsplit. *)
  (*         subst. *)
  (*         left. *)
  (*         constructor. *)
  (*       } *)
  (*       { *)
  (*         destruct (eq_dec c s) eqn:Eqd. *)
  (*         { *)
  (*           apply eq_dec_correct in Eqd. *)
  (*           subst s. *)
  (*           unfold RTotal in HTotal2. *)
  (*           assert (RegMatch r2 l true \/ RegMatch r2 l false) by eauto. *)
  (*           inversion H. *)
  (*           { *)
  (*             left. *)
  (*             replace (c :: l) with ([c] ++ l) by eauto. *)
  (*             eapply RConcatS; try constructor; try assumption. *)
  (*           } *)
  (*           { *)
  (*             right. *)
  (*             constructor. *)
  (*             intros l1' l1'' Hsplit. *)
  (*             destruct l1'. { left. constructor. } *)
  (*             destruct l1'. { right. inversion Hsplit. subst. split; try constructor; try assumption. } *)
  (*             left. eapply RCharF2. *)
  (*           } *)
  (*         } *)
  (*         { *)
  (*           right. *)
  (*           constructor. *)
  (*           intros l1' l1'' H. *)
  (*           destruct l1'. { left. constructor. } *)
  (*           destruct l1'. { left. constructor. now inversion H. } *)
  (*           left. eapply RCharF2. *)
  (*         } *)
  (*       } *)
  (*     } *)
  (*     { *)
  (*       intros HT1 r3 HT0 l. *)
  (*       assert (RegMatch r3 l true \/ RegMatch r3 l false) by eauto. *)
  (*       inversion H; try (left; eapply RUnionSR; assumption). *)
  (*       destruct l; try destruct l; eauto using RegMatch. *)
  (*       destruct (eq_dec c s) eqn:Eqd. *)
  (*       { apply eq_dec_correct in Eqd. rewrite Eqd. left. eapply RUnionSL. constructor. } *)
  (*       { right. constructor. constructor. assumption. assumption. } *)
  (*     } *)
  (*     { *)
  (*       intros HRT l. *)
  (*       induction l. *)
  (*       { *)
  (*         left. *)
  (*         constructor. *)
  (*         exists []. split; eauto. *)
  (*       } *)
  (*       { *)
  (*         destruct (eq_dec c a) eqn:Eqd. *)
  (*         { *)
  (*           apply eq_dec_correct in Eqd. *)
  (*           subst a. *)
  (*           inversion IHl. *)
  (*           { *)
  (*             inversion H. *)
  (*             subst. *)
  (*             inversion H1. *)
  (*             inversion H0. *)
  (*             subst l. *)
  (*             left. *)
  (*             constructor. *)
  (*             exists ([c] :: x); split. *)
  (*             { simpl. reflexivity. } { constructor; eauto using RegMatch. } *)
  (*           } *)
  (*           { *)
  (*             inversion H. *)
  (*             subst l0. *)
  (*             right. *)
  (*             constructor. *)
  (*             intros l' H'. *)
  (*             eauto using RegCharStarBase2. *)
  (*           } *)
  (*         } *)
  (*         { *)
  (*           inversion IHl. *)
  (*           { *)
  (*             right. *)
  (*             constructor. *)
  (*             intros l' H'. *)
  (*             eauto using LMembMakesFalse. *)
  (*           } *)
  (*           { *)
  (*             right. *)
  (*             constructor. *)
  (*             intros l' H'. *)
  (*             destruct l'. *)
  (*             { *)
  (*               simpl in H'. *)
  (*               inversion H'. *)
  (*             } *)
  (*             { *)
  (*               destruct l0. *)
  (*               { *)
  (*                 exists []. split. left. reflexivity. constructor. *)
  (*               } *)
  (*               { *)
  (*                 destruct l0. *)
  (*                 { *)
  (*                   simpl in H'. *)
  (*                   inversion H'. *)
  (*                   exists [a]. split. left. reflexivity. constructor. assumption. *)
  (*                 } *)
  (*                 { *)
  (*                   exists (s :: s0 :: l0). split. left. reflexivity. eapply RCharF2. *)
  (*                 } *)
  (*               } *)
  (*             } *)
  (*           } *)
  (*         } *)
  (*       } *)
  (*     } *)
  (*   } *)
  (*   { *)
  (*     repeat split. *)
  (*     { *)
  (*       inversion IHr1. *)
  (*       inversion IHr2. *)
  (*       inversion H0. *)
  (*       inversion H2. *)
  (*       eauto. *)
  (*     } *)
  (*     { *)
  (*       intros HTotal1 r0 HTotal0 l. *)
  (*       inversion IHr1. inversion IHr2. *)
  (*       assert (RegMatch (RConcat r1 (RConcat r2 r0)) l true \/ RegMatch (RConcat r1 (RConcat r2 r0)) l false). *)
  (*       { *)
  (*         eapply H0; try assumption. *)
  (*         eapply H2; try assumption. *)
  (*       } *)
  (*       inversion H3. *)
  (*       { *)
  (*         apply RegCatEquivalence in H4; try assumption. *)
  (*         left; assumption. *)
  (*       } *)
  (*       { *)
  (*         apply RegCatEquivalence in H4; try assumption. *)
  (*         right; assumption. *)
  (*       } *)
  (*     } *)
  (*     { *)
  (*       intros H r3 H0 l. *)
  (*       assert (RegMatch (RConcat r1 r2) l true \/ RegMatch (RConcat r1 r2) l false) by eauto. *)
  (*       assert (RegMatch r3 l true \/ RegMatch r3 l false) by eauto. *)
  (*       inversion H1; inversion H2. *)
  (*       { left. eapply RUnionSL. assumption. } *)
  (*       { left. eapply RUnionSL. assumption. } *)
  (*       { left. eapply RUnionSR. assumption. } *)
  (*       { right. eapply RUnionF. assumption. assumption. } *)
  (*     } *)
  (*     { *)

  (*       intros H. *)
  (*     } *)
  (*   } *)
  (*   { *)
  (*     inversion IHr1. *)
  (*     inversion IHr2. *)
  (*     repeat split. *)
  (*     { *)
  (*       intros l. *)
  (*       unfold RTotal in H. *)
  (*       unfold RTotal in H1. *)
  (*       assert (RegMatch r1 l true \/ RegMatch r1 l false) by eauto. *)
  (*       assert (RegMatch r2 l true \/ RegMatch r2 l false) by eauto. *)
  (*       inversion H3; inversion H4. *)
  (*       1: left. 2: left. 3: left. 4: { right; constructor; assumption. } all: constructor; assumption. *)
  (*     } *)
  (*     { *)
  (*       intros HT1 r0 HT0 l. *)
  (*       inversion IHr1. *)
  (*       inversion H4. *)
  (*       inversion IHr2. *)
  (*       inversion H8. *)
  (*       assert (RegMatch (RUnion (RConcat r1 r0) (RConcat r2 r0)) l true \/ RegMatch (RUnion (RConcat r1 r0) (RConcat r2 r0)) l false). *)
  (*       { *)
  (*         assert (RegMatch (RConcat r1 r0) l true \/ RegMatch (RConcat r1 r0) l false). *)
  (*         { *)
  (*           now eapply H5. *)
  (*         } *)
  (*         assert (RegMatch (RConcat r2 r0) l true \/ RegMatch (RConcat r2 r0) l false). *)
  (*         { *)
  (*           now apply H9. *)
  (*         } *)
  (*         inversion H11. { left. now eapply RUnionSL. } { inversion H12. { left. now eapply RUnionSR. } { right. now constructor. }} *)
  (*       } *)
  (*       inversion H11. *)
  (*       { *)
  (*         left. *)
  (*         eapply UnionConcatEquivalence in H12; eauto. *)
  (*       } *)
  (*       { *)
  (*         right. *)
  (*         eapply UnionConcatEquivalence in H12; eauto. *)
  (*       } *)
  (*     } *)
  (*     { *)
  (*       intros HT1 r3 HT3 l. *)
  (*       assert (RegMatch (RUnion r1 r2) l true \/ RegMatch (RUnion r1 r2) l false) by eauto. *)
  (*       inversion H3. { left. now apply RUnionSL. } *)
  (*       inversion H4. *)
  (*       subst. *)
  (*       assert (RegMatch r3 l true \/ RegMatch r3 l false) by eauto. *)
  (*       inversion H5. { left. now apply RUnionSR. } *)
  (*       right. *)
  (*       constructor; try constructor; assumption. *)
  (*     } *)
  (*   } *)
  (*   { *)
  (*     repeat split. *)
  (*     { *)
  (*       intros l. *)
  (*       inversion IHr. *)
  (*       inversion H0. *)
        
  (*     } *)
  (*   } *)

  (* Context (tot : forall r, RTotal r). *)

  Definition RSetMinus (r1 : REG) (r2 : REG) := RIntersection r1 (RNeg r2).

  (* First version, of which I am more confident of the semantics. *)
  Fixpoint PEGREG__old (p : PEG) (r : REG) : REG :=
    match p with
    | Char c => RConcat (RChar c) r
    | Concat p1 p2 => PEGREG__old p1 (PEGREG__old p2 r)
    | OrderedChoice p1 p2 => let p1r := PEGREG__old p1 r in
                            let p2r := PEGREG__old p2 r in
                            RUnion p1r (RSetMinus p2r (RIntersection p1r p2r))
    | PossesiveStar p1 => let p1r := RStar (PEGREG__old p1 REmp) in
                         RConcat p1r (RSetMinus r (RIntersection p1r r))
    end.

  (* Second version, more inductive. *)

  (* Remove the parts of r corresponding to ordered/possesive choices of p,
     then concatenate p with r. *)
  Fixpoint PEGREG (p : PEG) (r : REG) : REG :=
    match p with
    | Char c => RConcat (RChar c) r
    | Concat p1 p2 => PEGREG p1 (PEGREG p2 r)
    | OrderedChoice p1 p2 =>
        let p1r := PEGREG p1 r in
        let p2r := PEGREG p2 r in
        let p2r' := RSetMinus p2r (RIntersection p1r p2r) in
        RUnion p1r p2r
    | PossesiveStar p1 =>
        let p1r := RStar (PEGREG p1 REmp) in
        let p2r := (RSetMinus r (RIntersection p1r r)) in
        RConcat p1r p2r
    end.

  Lemma concat_char_nomatch_emp : forall c1, forall r, RegMatch (RConcat (RChar c1) r) [] false.
    intros c1 r.
    constructor.
    intros l1' l1'' H.
    destruct l1'.
    {
      left. constructor.
    }
    {
      destruct l1''.
      {
        simpl in H.
        inversion H.
      }
      {
        simpl in H.
        inversion H.
      }
    }
    Qed.

  Lemma two_one_length_one_one_length_impossible : forall T, forall l1 l2 : list T, forall c1 c2 c3 : T,
      (c1 :: l1) ++ (c2 :: l2) = [c3] -> False.
    intros T l1.
    induction l1.
    {
      intros l2 c1 c2 c3 H.
      simpl in H.
      inversion H.
    }
    {
      intros l2 c1 c2 c3 H.
      inversion H.
    }
  Qed.

  Lemma two_char_nomatch_one : forall c1 c2 c3, forall r, RegMatch (RConcat (RChar c1) (RConcat (RChar c2) r)) [c3] false.
    intros c1 c2 c3 r.
    destruct (eq_dec c1 c3) eqn:Heq_dec; apply eq_dec_correct in Heq_dec.
    {
      subst c3.
      constructor.
      intros l1' l1'' H.
      destruct l1'.
      {
        left.
        constructor.
      }
      {
        destruct l1''.
        {
          inversion H.
          rewrite app_nil_r in H2.
          rewrite H2.
          right.
          split.
          {
            constructor.
          }
          {
            apply concat_char_nomatch_emp.
          }
        }
        {
          simpl in H.
          inversion H.
          subst.
          simpl in H2.
          destruct l1'; discriminate.
        }
      }
    }
    {
      constructor.
      intros l1' l1'' H.
      destruct l1'.
      {
        simpl in H.
        subst.
        left.
        constructor.
      }
      {
        destruct l1''.
        {
          simpl in H.
          inversion H.
          subst.
          left.
          eapply RCharF1. { eapply eq_dec_correct. exact Heq_dec. }
        }
        {
          apply two_one_length_one_one_length_impossible in H.
          contradiction.
        }
      }
    }
  Qed.

  Lemma lop : forall t r c,
      RegMatch r t false -> RegMatch (RConcat (RChar c) r) (c :: t) false.
    intros t.
    induction t.
    {
      intros r c H.
      constructor.
      intros l1' l1'' H'.
      destruct l1'.
      {
        simpl in H'.
        rewrite H'.
        left.
        constructor.
      }
      {
        destruct l1''.
        {
          simpl in H'.
          inversion H'.
          rewrite app_nil_r in H2.
          subst.
          right; split; simpl; eauto using RegMatch.
        }
        {
          now apply two_one_length_one_one_length_impossible in H'.
        }
      }
    }
    {
      intros r c H.
      constructor.
      intros l1' l1'' H'.
      destruct l1'.
      {
        left.
        constructor.
      }
      {
        destruct l1''.
        {
          simpl in H'.
          inversion H'.
          rewrite app_nil_r in H2.
          subst.
          left.
          eapply RCharF2.
        }
        {
          destruct l1'.
          {
            inversion H'.
            subst.
            right; split; eauto using RegMatch.
          }
          {
            left.
            eapply RCharF2.
          }
        }
      }
    }
  Qed.

  Definition splits_imply_concat_inclusion : forall {T}, forall (P : list T -> Prop), forall l, (forall l1 l2 : list T, l1 ++ l2 = l -> P l1) -> (l = [] \/ forall l3, concat l3 = l -> exists l1', In l1' l3 /\ P l1').
    intros T P l H.
    destruct l eqn:eql.
    {
      left.
      reflexivity.
    }
    {
      right.
      intros l3.
      rewrite <- eql in * |- *.
      intros HConc.
      destruct l3.
      {
        simpl in HConc.
        subst.
        discriminate.
      }
      {
        simpl in HConc.
        assert (P l1) by eauto.
        exists l1. split; eauto. left. reflexivity.
      }
    }
  Qed.

  Definition some_implies_match (P : PEG) (r__remainder : REG) (r__out : REG) :=
    forall l1 l2 l3 prf suf, PegMatch P l1 (Some (l2, l3)) -> prf ++ suf = l3 -> RegMatch r__remainder prf true -> RegMatch r__out (l2 ++ prf) true.

  Definition blame_remainder (P : PEG) (r__remainder : REG) (r__out : REG) :=
    forall l1 l2 l3 prf suf, PegMatch P l1 (Some (l2, l3)) -> prf ++ suf = l3 ->
                        RegMatch r__remainder prf false -> RegMatch r__out (l2 ++ prf) false.

  (*
   * some_implies_match and blame_remainder together characterize the
   * "action/influence" of rremainder on rout
   *)

  Definition none_implies_nomatch (P : PEG) (r__remainder : REG) (r__out : REG) :=
    forall l1, DoesNotMatch P l1 -> RegMatch r__out l1 false.

  (* An by earlier lemma, therefore none -> nomatch any of the prefixes. *)


  Definition LR (P : PEG) (r__remainder : REG) (r__out : REG) : Prop :=
    some_implies_match P r__remainder r__out /\
      none_implies_nomatch P r__remainder r__out /\
      blame_remainder P r__remainder r__out.

  Lemma NoPegEmp' : forall p l o, PegMatch p l o -> l <> [].
    intros p l o m.
    induction m; try discriminate; try assumption.
  Qed.

  Lemma NoPegEmp : forall p o, PegMatch p [] o -> False.
    intros p o m.
    assert ([] <> []) by eauto using NoPegEmp'.
    contradiction.
  Qed.

  Lemma PegMatchChunkFormStrong : forall p l o, PegMatch p l o -> forall l1 l2, o = Some (l1, l2) -> forall p', p = PossesiveStar p' ->
                                                                                         exists ls, (concat ls = l1 /\ forall prf a suf, prf ++ (a :: suf) = ls -> PegMatch p' ((concat (a :: suf)) ++ l2) (Some (a, (concat suf) ++ l2))).
    intros p l o m.
    induction m; try discriminate.
    {
      intros l1 l2 Heqo p' Heqp'.
      inversion Heqo. inversion Heqp'. simpl.
      exists [].
      split.
      { simpl. reflexivity. }
      {
        intros prf a suf HConc.
        symmetry in HConc.
        eapply catnil in HConc as HNil.
        subst prf. simpl in HConc.
        discriminate.
      }
    }
    {
      intros l5 l6 Heqo p' Heqp'.
      inversion Heqo. inversion Heqp'. simpl.
      subst.
      assert (exists ls : list (list Σ),
           concat ls = l3 /\
           (forall prf a suf,
               prf ++ (a :: suf) = ls -> PegMatch p' ((concat (a :: suf)) ++ l6) (Some (a, concat (suf) ++ l6)))).
      {
        eapply IHm2; reflexivity.
      }
      inversion H.
      inversion H0.
      eapply list_split in m1 as HLS1.
      eapply list_split in m2 as HLS2.
      subst l2.
      symmetry in H1.
      subst.
      exists (l1 :: x); split.
      {
        simpl. reflexivity.
      }
      {
        intros prf a suf HConc.
        destruct prf eqn:heqprf.
        {
          simpl in HConc.
          inversion HConc.
          subst.
          rewrite <- app_assoc.
          eauto.
        }
        {
          simpl in HConc.
          inversion HConc.
          subst.
          inversion H0.
          replace (a ++ concat suf) with (concat (a :: suf)) by reflexivity.
          eapply H3 with (prf := l0).
          reflexivity.
        }
      }
    }
  Qed.

  Lemma PegMatchChunkForm : forall p l1 l2 l3, PegMatch (PossesiveStar p) l1 (Some (l2, l3)) ->
                                          exists ls, (concat ls = l2 /\ forall prf a suf, prf ++ (a :: suf) = ls -> PegMatch p ((concat (a :: suf)) ++ l3) (Some (a, (concat suf) ++ l3))).
    eauto using PegMatchChunkFormStrong.
  Qed.

  Lemma PegMatchInversion : forall ls p l3,
      (forall prf a suf, prf ++ (a :: suf) = ls -> PegMatch p ((concat (a :: suf)) ++ l3) (Some (a, (concat suf) ++ l3))) -> PegMatch p l3 None -> PegMatch (PossesiveStar p) ((concat ls) ++ l3) (Some ((concat ls), l3)).
    intros ls.
    induction ls; try eauto using PegMatch.
    intros p l3 HSuf HTail.
    assert (
        (forall (prf : list (list Σ)) (a : list Σ) (suf : list (list Σ)),
          prf ++ a :: suf = ls -> PegMatch p (concat (a :: suf) ++ l3) (Some (a, concat suf ++ l3)))
      ).
    {
      intros prf a0 suf HApp.
      apply HSuf with (prf := a :: prf). rewrite <- HApp. reflexivity.
    }
    assert (PegMatch (PossesiveStar p) (concat ls ++ l3) (Some (concat ls, l3))) by (eapply IHls; assumption).
    simpl. rewrite <- app_assoc. econstructor.
    {
      simpl in HSuf.
      rewrite app_assoc.
      eapply HSuf with (prf := []). simpl. reflexivity.
    }
    exact H0.
  Qed.

  Lemma PegregStarBase : forall p, (forall r__remainder, LR p r__remainder (PEGREG p r__remainder)) ->
                              forall l1 l3, PegMatch (PossesiveStar p) l1 (Some ([], l3)) ->
                                       forall r, RegMatch r l3 true ->
                                            RegMatch (PEGREG (PossesiveStar p) r) l1 true.
    intros p HLR l1 l3 m r HMatch.
    destruct l1 eqn:eqnl1; try (exfalso; eapply NoPegEmp; eassumption).
    simpl.
    apply list_split in m as HLS. simpl in HLS. subst l3.
    replace (s :: l) with ([] ++ (s :: l)) by reflexivity.
    eapply RConcatS; try (constructor; exists []; auto).
    constructor; try assumption.
    constructor.
    constructor.
    apply StarImpliesRemainderFail in m as HRemainderFail.
    assert (forall prf suf, prf ++ suf = (s :: l) -> DoesNotMatch p prf).
    {
      intros prf suf HConc.
      rewrite <- HConc in HRemainderFail.
      assert (DoesNotMatch p (prf ++ suf)).
      { intros l1' l2' H'. assert (Some (l1', l2') = None) by eauto using PegPartial. discriminate. }
      eapply MatchStrengthen. exact H.
    }
    assert ((s :: l) = [] \/ forall l', concat l' = (s :: l) -> exists e, In e l' /\ DoesNotMatch p e).
    {
      eapply splits_imply_concat_inclusion.
      exact H.
    }
    inversion H0. { discriminate. }
    constructor.
    intros l' HConc.
    assert (exists e : list Σ, In e l' /\ DoesNotMatch p e) by (eapply H1; assumption).
    inversion H2.
    inversion H3.
    assert (none_implies_nomatch p REmp (PEGREG p REmp)) by apply HLR.
    unfold none_implies_nomatch in H6.
    assert (RegMatch (PEGREG p REmp) x false). { eapply H6. exact H5. }
    exists x; split; assumption.
  Qed.


  Lemma SomeImpliesMatchStarChunkForm :
    forall ls p l3,
      (forall prf a suf, prf ++ (a :: suf) = ls -> PegMatch p ((concat (a :: suf)) ++ l3) (Some (a, (concat suf) ++ l3))) ->
      forall l1, PegMatch (PossesiveStar p) l1 (Some (concat ls, l3)) ->
               (forall r__remainder, LR p r__remainder (PEGREG p r__remainder)) ->
                    (Forall (fun l => RegMatch (PEGREG p REmp) l true) ls).
    intros ls.
    induction ls. { constructor. }
    {
      intros.
      assert
         (forall (prf : list (list Σ)) (a : list Σ) (suf : list (list Σ)),
             prf ++ a :: suf = ls -> PegMatch p (concat (a :: suf) ++ l3) (Some (a, concat suf ++ l3))).
      {
        intros prf a0 suf HSuf.
        eapply H with (prf := a :: prf). now rewrite <- HSuf.
      }
      constructor.
      {
        assert (PegMatch p (concat (a :: ls) ++ l3) (Some (a, (concat ls) ++ l3))).
        { eapply H with (prf := []). simpl. reflexivity. }
        assert (some_implies_match p REmp (PEGREG p REmp)) by eapply H1.
        replace a with (a ++ []) by eauto using app_nil_r.
        unfold some_implies_match in H4.
        apply H4 with (l1 := (concat (a :: ls) ++ l3)) (l2 := a) (l3 := concat ls ++ l3)
                      (prf := []) (suf := concat ls ++ l3); eauto using RegMatch.
      }
      {
        apply IHls with (l3 := l3) (l1 := (concat ls) ++ l3); try assumption.
        {
          apply StarImpliesRemainderFail in H0 as HRemainderFail.
          eapply PegMatchInversion; try assumption.
        }
      }
    }
    Qed.


  Lemma dnm_none : forall p l, PegMatch p l None -> DoesNotMatch p l.
    intros p l H ? ? H'.
    assert (None = Some (_, _)) by eauto using PegPartial.
    discriminate.
  Qed.


  Lemma SomeImpliesMatchStarStrong :
    forall p l o, PegMatch p l o ->
             forall p', p = PossesiveStar p' ->
             (forall r__remainder, LR p' r__remainder (PEGREG p' r__remainder)) ->
             forall l2 prf suf : list Σ, o = (Some (l2, prf ++ suf)) -> forall r, RegMatch r prf true ->
                                                               RegMatch (PEGREG p r) (l2 ++ prf) true.
    intros p l o m p' Heqp HLR l2 prf suf Heqo r HMatch.
    inversion Heqp. inversion Heqo. subst.
    simpl.
    apply list_split in m as HLS. subst l.
    apply PegMatchChunkForm in m as HChunkform.
    constructor.
    {
      constructor.
      inversion HChunkform.
      inversion H1.
      eapply SomeImpliesMatchStarChunkForm in H3.
      2: { rewrite H2. exact m. }
      2: { exact HLR. }
      exists x; split; eauto.
    }
    {
      constructor; try assumption.
      constructor.
      constructor.
      constructor.
      intros l' HConcat.
      apply StarImpliesRemainderFail in m as HFail.
      assert (StrengthenFail p' prf suf) by eapply MatchStrengthen.
      assert (DoesNotMatch p' prf) by (eapply H1; eapply dnm_none; assumption).
      assert (forall l' l'', l' ++ l'' = prf -> DoesNotMatch p' l').
      {
        intros l'0 l'' HApp.
        assert (StrengthenFail p' l'0 l'') by eapply MatchStrengthen.
        eapply H3. now rewrite HApp.
      }
      assert (forall l' l'', l' ++ l'' = prf -> RegMatch (PEGREG p' REmp) l' false).
      {
        intros l'0 l'' HApp.
        assert (DoesNotMatch p' l'0) by eauto.
        assert (none_implies_nomatch p' REmp (PEGREG p' REmp)) by apply HLR.
        now apply H5.
      }
      assert (prf = [] \/ (forall ell, concat ell = prf -> exists e : list Σ, In e ell /\ RegMatch (PEGREG p' REmp) e false)) by (eapply splits_imply_concat_inclusion; auto).
      inversion H5.
      {
        rewrite H6 in HConcat.a
      }
      {
        eapply H5.
        assert (exists e : list Σ, In e l' /\ RegMatch (PEGREG p' REmp) e false) by (eapply H5; auto).
        inversion H6.
        inversion H7.
        exists x; split; auto.
      }
    }
  Qed.

  Lemma dnmchar : forall l c s, DoesNotMatch (Char c) (s :: l) ->
                           eq_dec c s = false.
    intros l c s.
    destruct (eq_dec c s) eqn:Heqdc.
    {
      intros H.
      apply eq_dec_correct in Heqdc as Heqs.
      subst s.
      {
        exfalso.
        apply H with (l1 := [c]) (l2 := l).
        constructor.
      }
    }
    {
      intros H.
      reflexivity.
    }
  Qed.

  Lemma dnm_catassoc : forall p1 p2 p3 l, DoesNotMatch (Concat (Concat p1 p2) p3) l ->
                                     DoesNotMatch (Concat p1 (Concat p2 p3)) l.
    intros p1 p2 p3 l.
    {
      intros Hdnm.
      intros l1 l2 m'.
      apply Hdnm with (l1 := l1) (l2 := l2).
      inversion m'.
      subst.
      inversion H5.
      subst.
      rewrite app_assoc.
      eapply CatS. { eapply CatS; eauto. } eauto.
    }
  Qed.

  Lemma impossible_listcons : forall {T}, forall l : list T, forall h, l = (h :: l) -> False.
    intros T l.
    induction l.
    {
      intros h H. inversion H.
    }
    {
      intros h H.
      inversion H.
      eapply IHl. exact H2.
    }
    Qed.

  Lemma impossible_listapp : forall {T}, forall l1 l2 : list T, forall h,
      l1 = (h :: l2) ++ l1 -> False.
    intros T l1.
    induction l1.
    {
      intros l2 h H. simpl in H. inversion H.
    }
    {
      intros l2 h H. inversion H.
      destruct l2. { simpl in H2. eapply impossible_listcons. exact H2. }
      replace ((t :: l2) ++ h :: l1) with (((t :: l2) ++ [h]) ++ l1) in H2 by (rewrite <- app_assoc; auto).
      eapply IHl1.
      exact H2.
    }
  Qed.

  Lemma headeq : forall {T}, forall l2 l3 l1 : list T, l2 ++ l1 = l3 ++ l1 -> l2 = l3.
    intros T l2.
    induction l2.
    { intros l3 l1 H. simpl in H. destruct l3. reflexivity. exfalso. eapply impossible_listapp. exact H.  }
    { intros l3 l1 H. destruct l3. { simpl in H. symmetry in H. eapply impossible_listapp in H. contradiction. } { inversion H. simpl. assert (l2 = l3) by eauto. rewrite <- H0. reflexivity. } }.
    Qed.

  Lemma dnmcat' : forall l1 l2 P1 P2, DoesNotMatch (Concat P1 P2) (l1 ++ l2) ->
                                 DoesNotMatch P1 l1 \/ (exists l3 l4, PegMatch P1 (l1 ++ l2) (Some (l3, l4)) /\ DoesNotMatch P2 l4).
    intros l1 l2 P1 P2 H.
    assert (DoesNotMatch P1 l1 \/ ~ (DoesNotMatch P1 l1)) by apply lem.
    inversion H0; try (left; assumption).
    right. unfold DoesNotMatch in H1.
    assert ((exists l3 l4 : list Σ, PegMatch P1 l1 (Some (l3, l4))) \/ ~(exists l3 l4 : list Σ, PegMatch P1 l1 (Some (l3, l4)))) by apply lem.
    inversion H2.
    2: {
      exfalso.
      eapply H1.
      intros l2' l3' H'.
      eapply H3.
      exists l2'. exists l3'. exact H'.
    }
    inversion H3.
    inversion H4.
    apply list_split in H5 as HLS1. subst l1.
    assert (WeakenMatch P1 x x0 l2) by eapply MatchWeaken.
    assert (PegMatch P1 (x ++ x0 ++ l2) (Some (x, x0 ++ l2))) by eauto.
    assert ((exists l2' l3', PegMatch P2 (x0 ++ l2) (Some (l2', l3'))) \/ ~(exists l2' l3', PegMatch P2 (x0 ++ l2) (Some (l2', l3')))) by apply lem.
    inversion H8.
    {
      inversion H9. inversion H10.
      rewrite <- app_assoc in H.
      assert (PegMatch (Concat P1 P2) (x ++ x0 ++ l2) (Some (x ++ x1, x2))) by eauto using PegMatch.
      exfalso.
      eapply H; eauto.
    }
    {
      assert (forall l2' l3', ~ PegMatch P2 (x0 ++ l2) (Some (l2', l3'))).
      {
        intros l2' l3' H'.
        apply H9. exists l2'. exists l3'. exact H'.
      }
      unfold not in H10.
      assert (DoesNotMatch P2 (x0 ++ l2)). { hnf. eapply H10. }
      exists x. exists (x0 ++ l2). split. rewrite <- app_assoc. all: assumption.
    }
    Qed.


  Theorem pegreg_correct : forall P r, LR P r (PEGREG P r). intros P.
    induction P.
    {
      intros r.
      unfold LR.
      repeat split.
      {
        unfold some_implies_match.
        intros l1 l2 l3 prf suf m Heql3 mr.
        inversion m.
        subst.
        simpl.
        replace (c :: prf) with ([c] ++ prf) by reflexivity.
        eapply RConcatS; eauto using RegMatch.
      }
      {
        unfold none_implies_nomatch.
        intros l1 HNoMatch.
        destruct l1 eqn:Hl1.
        {
          simpl. constructor. intros l1' l1'' HSplit.
          symmetry in HSplit.
          apply catnil in HSplit as HNil.
          subst l1'.
          simpl in HSplit.
          subst l1''.
          left.
          constructor.
        }
        apply dnmchar in HNoMatch as Hdnmchar.
        simpl.
        constructor.
        intros l1' l1'' HApp.
        destruct l1'; left; eauto using RegMatch; inversion HApp; eauto using RegMatch.
      }
      {
        unfold blame_remainder.
        intros l1 l2 l3 prf suf m Heql3 mr.
        inversion m.
        subst.
        simpl.
        now apply lop.
      }
    }
    {
      intros r.
      simpl.
      repeat split.
      {
        intros l1 l2 l3 prf suf m Heql3 mr.
        inversion m.
        apply list_split in H5 as HLS2. apply list_split in H3 as HLS1.
        subst.
        assert (LR P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) by eauto.
        assert (LR P2 r (PEGREG P2 r)) by eauto.
        assert (some_implies_match P2 r (PEGREG P2 r)) by apply H0.
        assert (some_implies_match P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) by apply H.
        assert (RegMatch (PEGREG P2 r) (l6 ++ prf) true) by eauto.
        rewrite <- app_assoc.
        eapply H2. { exact H3. } { rewrite <- app_assoc. reflexivity. } { exact H4. }
      }
      {
        intros l HDnm.
        (* Either p1 does not match all prefixes of l, or it matches a prefix of l, by lem. or maybe we could induct over l
         *)
        assert (none_implies_nomatch P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) by eapply IHP1.
        replace l with (l ++ []) in HDnm by eauto using app_nil_r.
        assert ((DoesNotMatch P1 (l)) \/ (exists l1 l2, PegMatch P1 (l ++ []) (Some (l1, l2)) /\ DoesNotMatch P2 l2)). { eapply dnmcat'. exact HDnm. }
        inversion H0.
        {
          now apply H.
        }
        {
          rewrite app_nil_r in H1.
          inversion H1. inversion H2. inversion H3.
          assert (none_implies_nomatch P2 r (PEGREG P2 r)) by eapply IHP2.
          assert (RegMatch (PEGREG P2 r) x0 false) by eauto.
          assert (blame_remainder P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))). { eapply IHP1. }
          unfold blame_remainder in H8.
          apply list_split in H4 as HLS. rewrite HLS.
          apply H8 with (l1 := l) (l2 := x) (l3 := x0) (prf := x0) (suf := []); eauto using app_nil_r.
        }
      }
      {
        intros l1 l2 l3 prf suf m Heql3 mr.
        inversion m.
        subst.
        assert (blame_remainder P2 r (PEGREG P2 r)) as HBlameRemainder by eapply IHP2.
        assert (blame_remainder P1 (PEGREG P2 r) (PEGREG P1 (PEGREG P2 r))) as HBlameRemainder0 by eapply IHP1.
        rewrite <- app_assoc.
        eapply list_split in H3 as HLS1. eapply list_split in H5 as HLS2. subst.
        eapply HBlameRemainder0.
        { exact H3. }
        { rewrite <- app_assoc. reflexivity. }
        {
          eapply HBlameRemainder. { exact H5. } { reflexivity. } { exact mr. }
        }
      }
    }
    {
      intros r.
      repeat split.
      {
        unfold some_implies_match.
        intros l1 l2 l3 prf suf m Heql3 mr.
        apply StarImpliesRemainderFail in H1 as HCF.
        apply list_split in H1 as HLS.
        rewrite HLS.
        simpl.
        assert (LR P l3 (PEGREG P))
      }
    }
  (* Fixpoint LR (P : PEG) (r__cont) : Prop := *)
  (*   forall l1 l2 l3, (some_implies_match P r__cont) /\ (none_implies_nomatch P r__cont) /\ *)
  (*                 (match P with *)
  (*                  | Char c => True *)
  (*                  | Concat p1 p2 => forall r, LR p2 r -> LR P (PEGREG p1 r) *)
  (*                  | PossesiveStar p1 => forall r, LR ) *)

  Lemma unmatchable_remainder : forall p1, forall l1 l2 l3, forall r,
      PegMatch p1 l1 (Some (l2, l3)) -> RegMatch r l3 false ->
      RegMatch (PEGREG p1 r) l1 false.
    intros p1 l1 l2 l3 r.
    generalize dependent l3.
    generalize dependent l2.
    generalize dependent l1.
    generalize dependent r.
    induction p1.
    {
      intros r l1 l2 l3 H1 H2.
      simpl.
      inversion H1.
      subst.
      now eapply lop.
    }
    {
      intros r l1 l2 l3 H1 H2.
      simpl.
      inversion H1.
      subst.
      assert (RegMatch (PEGREG p1_2 r) l5 false); eauto.
    }
    {
      intros r l1 l2 l3 H1 H2.
      inversion H1.
      {
        simpl.
        subst.
        constructor.
        {
          clear IHp1.
          clear H1.
          induction p1.
          {
            simpl.
            replace l3 with ([] ++ l3); try easy.
            eapply RStarF.
            {
              inversion H4.
              subst.
              now constructor.
            }
            {
              constructor.
            }
          }
          {
            simpl.
          }
        }
      }
    }
    intros r; induction r.
    {
      intros l1 l2 l3 H1 H2.
      simpl.
      inversion H1.
      subst.
      constructor.
      intros l1' l1'' H.
      destruct l1'.
      {
        left.
        constructor.
      }
      {
        destruct l1'.
        2: left; eapply RCharF2.
        inversion H.
        subst.
        right.
        split; eauto using RegMatch.
      }
    }
    {
      intros l1 l2 l3 H1 H2.
      inversion H1.
      subst.
      eapply lop.
      exact H2.
    }
    {
      intros l1 l2 l3 H1 H2.
      simpl.
      
    }

  Lemma unmatchable_p1 : forall p1, forall l,
      PegMatch p1 l None -> forall r, RegMatch (PEGREG p1 r) l false.
    intros p1.
    induction p1.
    {
      intros l H r.
      simpl.
      inversion H.
      subst.
      constructor.
      intros l1' l1'' H2.
      destruct l1'.
      {
        simpl in H2.
        subst.
        left.
        constructor.
      }
      {
        simpl in H2.
        inversion H2.
        subst.
        left.
        eapply RCharF1; eauto.
      }
    }
    {
      intros l H r.
      inversion H.
      {
        subst.
        simpl.
        now eapply IHp1_1.
      }
      {
        subst.
        simpl.
        assert (RegMatch (PEGREG p1_2 r) l2 false) by eauto.
        
      }
    }

  Lemma unmatchable_p2 : forall p2 p1, forall l1 l2,
      PegMatch p1 l1 (Some (l1, l2)) -> PegMatch p2 l2 None ->
      forall r, RegMatch (PEGREG p1 (PEGREG p2 r)) l1 false.
    intros p2.
    induction p2.
    {
      intros p1.
      induction p1.
      {
        intros l2 l0 H1 H2 r.
        simpl.
        inversion H1.
        subst.
        replace [c0] with ([c0] ++ []) by eauto.
        eapply RConcatF.
        intros l1'.
        destruct l1'; try eauto using RegMatch.
        intros l1''.
        destruct l1''.
        {
          intros H.
          right.
          split.
          {
            simpl in H.
            inversion H.
            subst.
            rewrite app_nil_r in H4.
            rewrite H4.
            constructor.
          }
          {
            eapply concat_char_nomatch_emp.
          }
        }
        {
          intros H.
          replace ([c0] ++ []) with [c0] in H. 2: rewrite app_nil_r; reflexivity.
          apply two_one_length_one_one_length_impossible in H.
          contradiction.
        }
      }
      {
        intros l1 l2 H1 H2 r.
        simpl.
        
        eapply IHp1_1.
      }
    }

  Theorem PEGREG_implies_reg : PEGREG_implies_reg_statement.
    unfold PEGREG_implies_reg_statement.
    intros p.
    induction p.
    {
      intros r1 r2 l1 l2 l3 H1.
      repeat split.
      {
        intros H2 H3.
        simpl in H1.
        subst r2.
        apply list_split in H2 as Hl1eq.
        inversion H2.
        subst.
        replace (c :: l3) with ([c] ++ l3) by auto.
        constructor; eauto using RegMatch.
      }
      {
        intros H.
        simpl in H1.
        inversion H.
        subst.
        eauto using RegMatch.
      }
      {
        intros H.
        unfold PEGREG__init.
        inversion H.
        constructor.
      }
    }
    {
      intros r1 r2 l1 l2 l3 H1.
      repeat split.
      {
        intros H2 H3.
        apply list_split in H2 as HLS.
        simpl in H1.
        inversion H2.
        subst l7. subst l2. subst l1. subst l0. subst p3. subst p1.
        remember (PEGREG p2 r1).
        assert (RegMatch r l5 true).
        {
          symmetry in Heqr.
          eapply IHp2. exact Heqr. exact H8. exact H3.
        }
        rewrite <- app_assoc.
        apply list_split in H8 as HLS.
        rewrite <- HLS.
        rewrite <- app_assoc in H6.
        rewrite <- HLS in H6.
        eapply IHp1; eassumption.
      }
      {
        intros H.
        inversion H.
        {
          subst.
          simpl PEGREG.
          remember (PEGREG p1 (PEGREG p2 r1)).
          symmetry in Heqr.
          eapply IHp1; eauto.
        }
        {
          subst.
          simpl PEGREG.
          assert ((PEGREG p2 r1) )
        }
      }
    }
    {
      intros r1 r2 l1 l2 l3 H1 H2 H3.
      apply list_split in H2 as HLS.
      simpl in H1.
      inversion H2.
      subst l3. subst l2. subst l1. subst p1. clear HLS.
      {

      }
    }
