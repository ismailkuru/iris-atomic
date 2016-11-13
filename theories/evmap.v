(* evmap.v -- generalized heap-like monoid composite *)
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Export auth frac gmap dec_agree.
From iris.proofmode Require Import tactics.

Section evmap.
  Context (K A: Type) (Q: cmraT) `{Countable K, EqDecision A}.
  Definition evkR := prodR Q (dec_agreeR A).
  Definition evmapR := gmapUR K evkR.
  Definition evidenceR := authR evmapR.
  Class evidenceG Σ := EvidenceG { evidence_G :> inG Σ evidenceR }.
  Definition evidenceΣ : gFunctors := #[ GFunctor (constRF evidenceR) ].

  Instance subG_evidenceΣ {Σ} : subG evidenceΣ Σ → evidenceG Σ.
  Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

  (* Some basic supporting lemmas *)
  Lemma map_agree_eq m m' (hd: K) (p q: Q) (x y: A):
    m !! hd = Some (p, DecAgree y) →
    m = {[hd := (q, DecAgree x)]} ⋅ m' → x = y.
  Proof.
    intros H1 H2.
    destruct (decide (x = y)) as [->|Hneq]=>//.
    exfalso.
    subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd) as [[b [c|]]|] eqn:Heqn; rewrite Heqn in H1; inversion H1=>//.
    destruct (decide (x = c)) as [->|Hneq3]=>//.
    - rewrite dec_agree_idemp in H3. by inversion H3.
    - rewrite dec_agree_ne in H3=>//.
  Qed.

  Lemma map_agree_somebot m m' (hd: K) (p q: Q) (x: A):
    m !! hd = Some (p, DecAgreeBot) → m' !! hd = None →
    m = {[hd := (q, DecAgree x)]} ⋅ m' → False.
  Proof.
    intros H1 H2 H3. subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd) as [[b [c|]]|] eqn:Heqn; rewrite Heqn in H1; inversion H1=>//.
  Qed.

  Lemma map_agree_none m m' (hd: K) (q: Q) (x: A):
    m !! hd = None → m = {[hd := (q, DecAgree x)]} ⋅ m' → False.
  Proof.
    intros H1 H2. subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd)=>//.
  Qed.
End evmap.

Section evmapR.
  Context (K A: Type) `{Countable K, EqDecision A}.
  Context `{!inG Σ (authR (evmapR K A unitR))}.

  (* Evidence that k immutably maps to some fixed v *)
  Definition ev γm (k : K) (v: A) := own γm (◯ {[ k := ((), DecAgree v) ]})%I.

  Global Instance persistent_ev γm k v : PersistentP (ev γm k v).
  Proof. apply _. Qed.

  (* Alloc a new mapsto *)
  Lemma evmap_alloc γm m k v:
    m !! k = None →
    own γm (● m) ⊢ |==> own γm (● (<[ k := ((), DecAgree v) ]> m) ⋅ ◯ {[ k := ((), DecAgree v) ]}).
  Proof.
    iIntros (?) "Hm".
    iDestruct (own_update with "Hm") as "?"; last by iAssumption.
    apply auth_update_alloc. apply alloc_singleton_local_update=>//.
  Qed.
  
  (* Some other supporting lemmas *)
  Lemma map_agree_none' γm (m: evmapR K A unitR) hd x:
    m !! hd = None →
    own γm (● m) ★ ev γm hd x ⊢ False.
  Proof.
    iIntros (?) "[Hom Hev]".
    iCombine "Hom" "Hev" as "Hauth".
    iDestruct (own_valid with "Hauth") as %Hvalid. iPureIntro.
    apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
    eapply (map_agree_none _ _ _ m)=>//.
  Qed.

  Lemma map_agree_eq' γm m hd x agy:
    m !! hd = Some ((), agy) →
    ev γm hd x ★ own γm (● m) ⊢ DecAgree x = agy.
  Proof.
    iIntros (?) "[#Hev Hom]".
    iCombine "Hom" "Hev" as "Hauth".
    iDestruct (own_valid γm (● m ⋅ ◯ {[hd := (_, DecAgree x)]})
               with "[Hauth]") as %Hvalid=>//.
    apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
    destruct agy as [y|].
    - iDestruct "Hauth" as "[? ?]". iFrame.
      iPureIntro. apply f_equal.
      eapply (map_agree_eq _ _ _ m)=>//.
    - iAssert (✓ m)%I as "H"=>//. rewrite (gmap_validI m).
      iDestruct ("H" $! hd) as "%".
      exfalso. subst. rewrite H0 in H1.
      by destruct H1 as [? ?].
  Qed.

  (* Evidence is the witness of membership *)
  Lemma ev_map_witness γm m hd x:
    ev γm hd x ★ own γm (● m) ⊢ m !! hd = Some (∅, DecAgree x).
  Proof.
    iIntros "[#Hev Hom]".
    destruct (m !! hd) as [[[] agy]|] eqn:Heqn.
    - iDestruct (map_agree_eq' with "[-]") as %H'=>//; first by iFrame. by subst.
    - iExFalso. iApply map_agree_none'=>//. by iFrame.
  Qed.
  
  (* Two evidences coincides *)
  Lemma evmap_frag_agree_split γm p (a1 a2: A):
    ev γm p a1 ★ ev γm p a2 ⊢ a1 = a2.
  Proof.
    iIntros "[Ho Ho']".
    destruct (decide (a1 = a2)) as [->|Hneq].
    - by iFrame.
    - iCombine "Ho" "Ho'" as "Ho".
      rewrite -(@auth_frag_op (evmapR K A unitR) {[p := (_, DecAgree a1)]} {[p := (_, DecAgree a2)]}).
      iDestruct (own_valid with "Ho") as %Hvalid.
      exfalso. rewrite op_singleton in Hvalid.
      apply auth_valid_discrete in Hvalid. simpl in Hvalid.
      apply singleton_valid in Hvalid.
      destruct Hvalid as [_ Hvalid].
      apply dec_agree_op_inv in Hvalid. inversion Hvalid. subst. auto.
  Qed.
End evmapR.