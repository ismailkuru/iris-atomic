From iris.program_logic Require Export auth weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import upred frac excl dec_agree upred_big_op gset gmap.
From iris.tests Require Import atomic treiber_stack.
From flatcomb Require Import misc.

Definition doOp (f: val) : val :=
  λ: "p",
     match: !"p" with
       InjL "x" => "p" <- InjR (f "x")
     | InjR "_" => #()
     end.

Definition loop (f: val): val :=
  rec: "loop" "p" "s" "lk" :=
    match: !"p" with
      InjL "_" =>
        if: try_acquire "lk"
          then iter' (!"s") (doOp f);;
               release "lk";;
               "loop" "p" "s" "lk"
          else "loop" "p" "s" "lk"
    | InjR "r" => "r"
    end.

(* Naive implementation *)
Definition install : val :=
  λ: "x" "s",
     let: "p" := ref (InjL "x") in
     push "s" "p";;
     "p".

Definition flat (f: val) : val :=
  λ: <>,
   let: "lk" := newlock #() in
   let: "s" := new_stack #() in
   λ: "x",
      let: "p" := install "x" "s" in
      loop f "p" "s" "lk".

Global Opaque doOp install loop flat.

Definition srvR := prodR fracR (dec_agreeR val).
Definition tokR := evmapR loc (gname * gname * gname * gname).
Class srvG Σ := SrvG {
  srv_G :> inG Σ srvR;
  tok_G :> inG Σ (authR tokR);
}.

Definition srvΣ : gFunctors :=
  #[ GFunctor (constRF srvR);
     GFunctor (constRF (authR tokR))
   ].

Instance subG_srvΣ {Σ} : subG srvΣ Σ → srvG Σ.
Proof. intros [?%subG_inG [?%subG_inG _]%subG_inv]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !evidenceG loc val Σ, !srvG Σ} (N : namespace).

  Definition p_inv
             (γm γx γ1 γ2 γ3 γ4: gname)
             (Q: val → val → Prop)
             (v: val): iProp Σ :=
    (∃ (p : loc) (q: Qp), v = #p ★ own γm (◯ ({[ p := (q, DecAgree (γx, γ1, γ3, γ4)) ]} : tokR)) ★
     ((∃ (y: val), p ↦{1/2} InjRV y ★ own γ1 (Excl ()) ★ own γ3 (Excl ())) ∨
      (∃ (x: val), p ↦{1/2} InjLV x ★ own γx ((1/2)%Qp, DecAgree x) ★ own γ1 (Excl ()) ★ own γ4 (Excl ())) ∨
      (∃ (x: val), p ↦{1/2} InjLV x ★ own γx ((1/4)%Qp, DecAgree x) ★ own γ2 (Excl ()) ★ own γ4 (Excl ())) ∨
      (∃ (x y: val), p ↦{1/2} InjRV y ★ own γx ((1/2)%Qp, DecAgree x) ★ ■ Q x y ★ own γ1 (Excl ()) ★ own γ4 (Excl ()))))%I.

  Definition p_inv_R γm γ2 Q v : iProp Σ :=
    (∃ γx γ1 γ3 γ4: gname, p_inv γm γx γ1 γ2 γ3 γ4 Q v)%I.

  Definition srv_stack_inv (γ γm γ2: gname) (s: loc) (Q: val → val → Prop) : iProp Σ :=
    (∃ xs, is_stack' (p_inv_R γm γ2 Q) xs s γ)%I.

  Definition srv_m_inv γm := (∃ m, own γm (● m) ★ [★ map] p ↦ _ ∈ m, ∃ v, p ↦{1/2} v)%I.

  Lemma install_push_spec
        (Φ: val → iProp Σ) (Q: val → val → Prop)
        (p: loc) (γ γm γx γ1 γ2 γ3 γ4: gname)
        (s: loc) (x: val) :
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γ γm γ2 s Q) ★ own γx ((1/2)%Qp, DecAgree x) ★
    own γm (◯ ({[ p := ((1 / 2)%Qp, DecAgree (γx, γ1, γ3, γ4)) ]})) ★
    p ↦{1/2} InjLV x ★ own γ1 (Excl ()) ★ own γ4 (Excl ()) ★ (True -★ Φ #())
    ⊢ WP push #s #p {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & Hx & Hpm & Hp & Ho1 & Ho2 & HΦ)".
    rewrite /srv_stack_inv.
    iDestruct (push_spec N (p_inv_R γm γ2 Q) with "[-HΦ]") as "Hpush"=>//.
    - iFrame "Hh". iSplitL "Hx Hp Hpm Ho1 Ho2"; last eauto.
      iExists γx, γ1, γ3, γ4. iExists p, (1/2)%Qp. iSplit=>//. iFrame "Hpm".
      iRight. iLeft.
      iExists x. iFrame.
    - iApply wp_wand_r.
      iSplitL "Hpush"; first done.
      iIntros (?). iIntros "%".
      inversion H. by iApply "HΦ".
  Qed.

  Lemma install_spec
        (Φ: val → iProp Σ) (Q: val → val → Prop)
        (x: val) (γ2 γm γ: gname) (s: loc):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γ γm γ2 s Q) ★ inv N (srv_m_inv γm) ★ 
    (∀ (p: loc) (γx γ1 γ2 γ3 γ4: gname),
       own γ3 (Excl ()) -★ own γm (◯ {[ p := ((1 / 2)%Qp, DecAgree (γx, γ1, γ3, γ4)) ]}) -★
       own γx ((1/2)%Qp, DecAgree x) -★ Φ #p)
    ⊢ WP install x #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #? & HΦ)".
    wp_seq. wp_let. wp_alloc p as "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iApply pvs_wp.
    iVs (own_alloc (Excl ())) as (γ1) "Ho1"; first done.
    iVs (own_alloc (Excl ())) as (γ3) "Ho3"; first done.
    iVs (own_alloc (Excl ())) as (γ4) "Ho4"; first done.
    iVs (own_alloc (1%Qp, DecAgree x)) as (γx) "Hx"; first done.
    iInv N as ">Hm" "Hclose".
    iDestruct "Hm" as (m) "[Hm HRm]".
    destruct (decide (m !! p = None)).
    - (* fresh name *)
      iAssert (|=r=> own γm (● ({[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅ m) ⋅
                             ◯ {[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]}))%I with "[Hm]" as "==>[Hm1 Hm2]".
      { iDestruct (own_update with "Hm") as "?"; last by iAssumption.
        apply auth_update_no_frag. apply alloc_unit_singleton_local_update=>//. }
      iVs ("Hclose" with "[HRm Hm1 Hl1]").
      { iNext. rewrite /srv_m_inv. iExists ({[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅ m).
        iFrame. replace ({[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅ m) with (<[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]> m); last admit.
        iDestruct (big_sepM_insert _ m with "[-]") as "?".
        - exact e.
        - iSplitR "HRm"; last done. simpl. eauto.
        - eauto. }
      iAssert (|=r=>own γm (◯ {[p := ((1/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅
                            ◯ {[p := ((1/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]}))%I
              with "[Hm2]" as "==>[Hfrag1 Hfrag2]".
      { iDestruct (own_update with "Hm2") as "?"; last by iAssumption.
        rewrite <- auth_frag_op.
        by rewrite op_singleton pair_op dec_agree_idemp frac_op' Qp_div_2. }
    iDestruct (own_update with "Hx") as "==>[Hx1 Hx2]"; first by apply pair_l_frac_op_1'.
    iVsIntro. wp_let. wp_bind ((push _) _).
    iApply install_push_spec=>//.
    iFrame "#". iFrame "Hx1 Hfrag1 Hl2 Ho1 Ho4". iIntros "_". wp_seq. iVsIntro.
    iSpecialize ("HΦ" $! p γx γ1 γ2 γ3 γ4 with "[-Hx2 Hfrag2]")=>//.
    iApply ("HΦ" with "Hfrag2 Hx2").
    - iExFalso. (* XXX: used name *)
      (* iAssert (([★ map] _↦v ∈ delete p m, ∃ v' : val, v = (1%Qp, DecAgree v') ★ p_inv_R γm γ2 Q v') ★ *)
      (*          (∃ v, v = (1%Qp, DecAgree #p) ★ p_inv_R γm γ2 Q #p))%I *)
      (*          with "[HRs]" as "[HRs Hp]". *)
      admit.
  Admitted.

  Lemma loop_iter_list_spec Φ (f: val) (s hd: loc) Q (γ γm γ2: gname) xs:
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γ γm γ2 s Q) ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★ own γ2 (Excl ()) ★
    is_list' γ hd xs ★ (own γ2 (Excl ()) -★ Φ #())
    ⊢ WP iter' #hd (doOp f) {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #Hf & Ho2 & Hlist' & HΦ)".
    rewrite /doOp.
    iApply pvs_wp.
    iDestruct (dup_is_list' with "[Hlist']") as "==>[Hl1 Hl2]"; first by iFrame.
    iDestruct (dup_is_list' with "[Hl2]") as "==>[Hl2 Hl3]"; first by iFrame.
    iDestruct (iter'_spec _ (p_inv_R γm γ2 Q) _ γ s (is_list' γ hd xs ★ own γ2 (Excl ()))%I xs hd (λ: "p",
      match: ! "p" with InjL "x" => "p" <- SOME (f "x") | InjR "_" => #() end)%V (λ: "p",
      match: ! "p" with InjL "x" => "p" <- SOME (f "x") | InjR "_" => #() end) with "[-Hl1]") as "Hiter'"=>//.
    - rewrite /f_spec.
      iIntros (Φ' x _ Hin) "(#Hh & #? & (Hls & Ho2) & HΦ')".
      wp_let. wp_bind (! _)%E. iInv N as (xs') ">Hs" "Hclose".
      iDestruct "Hs" as (hd') "[Hhd [Hxs HRs]]".
      iDestruct "HRs" as (m) "[Hom HRs]".
      (* now I know x conforms to p_inv:
         since is_list' γ hd xs, so for any x ∈ xs,
         we can attain its fragment as evidence that it is
         mapped to by some k in m; and since "HRs", so we know (tmeporarily)
         that x conforms to R.
         XXX: I suppose that this part can be further simplified and split out
         *)
      (* iAssert (p_inv_R γm γ2 Q x) as "Hx". *)
      admit.
    - apply to_of_val.
    - iFrame "#". iFrame "Hl2 Hl3 Ho2".
      iIntros "[_ H]". by iApply "HΦ".
    - done.
  Admitted.

  Lemma loop_spec Φ (p s: loc) (lk: val) (f: val)
        Q (γ2 γm γ γlk: gname) (γx γ1 γ3 γ4: gname):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γ γm γ2 s Q) ★ is_lock N γlk lk (own γ2 (Excl ())) ★
    own γ3 (Excl ()) ★ (∃ q: Qp, own γm (◯ {[ p := (q, DecAgree (γx, γ1, γ3, γ4)) ]})) ★
    □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★ (∀ x y,  own γx ((1 / 2)%Qp, DecAgree x) -★ ■ Q x y -★  Φ y)
    ⊢ WP loop f #p #s lk {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #? & Ho3 & Hγs & #? & HΦ)".
    iLöb as "IH". wp_rec. repeat wp_let.
    iDestruct "Hγs" as (q) "Hγs".
    wp_bind (! _)%E. iInv N as ">Hinv" "Hclose".
    iDestruct "Hinv" as (xs hd) "[Hs [Hxs HRs]]".
    (* iAssert (|=r=>own γm (◯ {[p := ((q/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅ *)
    (*                       ◯ {[p := ((q/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]}))%I *)
    (*         with "[Hγs]" as "==>[Hfrag1 Hfrag2]". *)
    (* { iDestruct (own_update with "Hγs") as "?"; last by iAssumption. *)
    (*   rewrite <- auth_frag_op. *)
    (*   by rewrite op_singleton pair_op dec_agree_idemp frac_op' Qp_div_2. } *)
    iDestruct "HRs" as (m) "[Hom HRs]".
    destruct (decide (m !! p = None)).
    - admit.
      (* impossible -- because of the fragment *)
    - iAssert (([★ map] _↦v ∈ delete p m, ∃ v' : val, v = (1%Qp, DecAgree v') ★ p_inv_R γm γ2 Q v') ★
               (∃ v, v = (1%Qp, DecAgree #p) ★ p_inv_R γm γ2 Q #p))%I
              with "[HRs]" as "[HRs Hp]".
      { admit. }
      iDestruct "Hp" as (?) "[% Hpr]"; subst.
      iDestruct "Hpr" as (γx' γ1' γ3' γ4' p' q') "(% & Hp' & Hp)".
      inversion H. subst.
      destruct (decide (γ1 = γ1' ∧ γx = γx' ∧ γ3 = γ3' ∧ γ4 = γ4')) as [[? [? [? ?]]]|Hneq].
      + subst. 
        iDestruct "Hp" as "[Hp | [Hp | [ Hp | Hp]]]".
        * admit.
        * iDestruct "Hp" as (x) "(Hp & Hx & Ho1 & Ho4)".
          wp_load.
          iVs ("Hclose" with "[-Hp' Ho3 HΦ]").
          { iNext. iExists xs, hd. iFrame. iExists m. iFrame. (* merge *) admit. }
          iVsIntro. wp_match. (* we should close it as it is in this case *)
          (* now, just reason like a server *)
          wp_bind (try_acquire _). iApply try_acquire_spec.
          iFrame "#". iSplit.
          { (* acquired the lock *)
            iIntros "Hlocked Ho2".
            wp_if. wp_bind ((iter' _) _). wp_bind (! _)%E.
            iInv N as ">H" "Hclose".
            iDestruct "H" as (xs' hd') "[Hs [Hxs HRs]]".
            wp_load. iDestruct (dup_is_list' with "[Hxs]") as "==>[Hxs1 Hxs2]"; first by iFrame.
            iVs ("Hclose" with "[Hs Hxs1 HRs]").
            { iNext. iExists xs', hd'. by iFrame. }
            iVsIntro. iApply loop_iter_list_spec=>//.
            iFrame "#". iSplitR; first eauto.
            iFrame. iIntros "Ho2".
            wp_seq. wp_bind (release _). iApply release_spec.
            iFrame "~ Hlocked Ho2". wp_seq.
            (* maybe q q' should be equal? or we just need any kind of q? *)
            iAssert ((∃ q0 : Qp,
                        own γm (◯ {[p' := (q0, DecAgree (γx', γ1', γ3', γ4'))]})))%I with "[Hp']" as "Hp'".
            { eauto. }
            by iApply ("IH" with "Ho3 Hp'"). }
          {  wp_if.
            iAssert ((∃ q0 : Qp,
                        own γm (◯ {[p' := (q0, DecAgree (γx', γ1', γ3', γ4'))]})))%I with "[Hp']" as "Hp'".
            { eauto. }
            iApply ("IH" with "Ho3 Hp'")=>//. }
        * iDestruct "Hp" as (x) "(Hp & Hx & Ho1 & Ho4)".
          wp_load.
          iVs ("Hclose" with "[-Hp' Ho3 HΦ]").
          { iNext. iExists xs, hd. iFrame. iExists m. iFrame. (* merge *) admit. }
          iVsIntro. wp_match. (* we should close it as it is in this case *)
          wp_bind (try_acquire _). iApply try_acquire_spec.
          iFrame "#". iSplit.
          { (* impossible *) admit. }
          { wp_if.
            iAssert ((∃ q0 : Qp,
                        own γm (◯ {[p' := (q0, DecAgree (γx', γ1', γ3', γ4'))]})))%I with "[Hp']" as "Hp'".
            { eauto. }
            iApply ("IH" with "Ho3 Hp'")=>//. }
        * iDestruct "Hp" as (x y) "(Hp & Hox & % & Ho1 & Ho4)".
          wp_load.
          iVs ("Hclose" with "[-Hp' Ho3 HΦ Hox]").
          { iNext. iExists xs, hd. iFrame. iExists m. iFrame. (* merge *) admit. }
          iVsIntro. wp_match. by iApply ("HΦ" with "Hox").
      + iCombine "Hγs" "Hp'" as "Hγs".
        iExFalso.
        admit.
  Admitted.

  Lemma flat_spec (f: val) Q:
    heapN ⊥ N →
    heap_ctx ★ □ (∀ x: val, WP f x {{ v, ■ Q x v }})%I
    ⊢ WP flat f #() {{ f', □ (∀ x: val, WP f' x {{ v, ■ Q x v }}) }}.
  Proof.
    iIntros (HN) "(#Hh & #?)".
    iVs (own_alloc (Excl ())) as (γ2) "Ho2"; first done.
    iVs (own_alloc (● (∅: tokR) ⋅ ◯ ∅)) as (γm) "[Hm _]".
    { by rewrite -auth_both_op. }
    iVs (inv_alloc N _ (srv_m_inv γm)%I with "[Hm]") as "#Hm"; first eauto.
    { iNext. rewrite /srv_m_inv. iExists ∅. iFrame. (* XXX: iApply big_sepM_empty. *)
      by rewrite /uPred_big_sepM map_to_list_empty. }
    wp_seq. wp_bind (newlock _).
    iApply newlock_spec=>//.
    iFrame "Hh Ho2". iIntros (lk γlk) "#Hlk".
    wp_let. wp_bind (new_stack _).
    iApply (new_stack_spec' _ (p_inv_R γm γ2 Q))=>//.
    iFrame "Hh". iIntros (γ s) "#Hss".
    wp_let. iVsIntro. iAlways.
    iIntros (x). wp_let.
    wp_bind ((install _) _).
    iApply install_spec=>//.
    iFrame "Hh Hss Hm". iIntros (p γx γ1 _ γ3 γ4) "Hp3 Hpx Hx".
    wp_let. iApply loop_spec=>//.
    iFrame "Hh Hss Hlk". iFrame.
    iSplitL "Hpx"; first eauto.
    iSplitR; first eauto. iIntros (? ?) "Hox %".
    destruct (decide (x = a)) as [->|Hneq]; first done.
    iExFalso. iCombine "Hx" "Hox" as "Hx".
    iDestruct (own_valid with "Hx") as "%".
    rewrite pair_op in H0. destruct H0 as [_ ?]. simpl in H0.
    rewrite dec_agree_ne in H0=>//.
  Qed.
End proof.
