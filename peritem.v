From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import frac auth upred gmap dec_agree upred_big_op csum.
From iris_atomic Require Export treiber misc evmap.

Section defs.
  Context `{heapG Σ, !evidenceG loc val unitR Σ} (N: namespace).
  Context (R: val → iProp Σ) (γ: gname) `{∀ x, TimelessP (R x)}.

  Definition allocated hd := (∃ q v, hd ↦{q} v)%I.

  Definition evs := ev loc val γ.

  Fixpoint is_list' (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (∃ q, hd ↦{ q } NONEV)%I
    | x :: xs => (∃ (hd': loc) q, hd ↦{q} SOMEV (x, #hd') ★ evs hd x ★ is_list' hd' xs)%I
    end.

  Lemma in_list' x xs:
    ∀ hd, x ∈ xs →
          is_list' hd xs
          ⊢ ∃ (hd' hd'': loc) q, hd' ↦{q} SOMEV (x, #hd'') ★ evs hd' x.
  Proof.
    induction xs as [|x' xs' IHxs'].
    - intros ? Hin. inversion Hin.
    - intros hd Hin. destruct (decide (x = x')) as [->|Hneq].
      + iIntros "Hls". simpl.
        iDestruct "Hls" as (hd' q) "(? & ? & ?)".
        iExists hd, hd', q. iFrame.
      + assert (x ∈ xs') as Hin'; first set_solver.
        iIntros "Hls". simpl.
        iDestruct "Hls" as (hd' q) "(? & ? & ?)".
        iApply IHxs'=>//.
  Qed.

  Definition perR' hd v v' := (v = ((∅: unitR), DecAgree v') ★ R v' ★ allocated hd)%I.
  Definition perR  hd v := (∃ v', perR' hd v v')%I.
  
  Definition allR := (∃ m : evmapR loc val unitR, own γ (● m) ★ [★ map] hd ↦ v ∈ m, perR hd v)%I.

  Definition is_stack' xs s := (∃ hd: loc, s ↦ #hd ★ is_list' hd xs ★ allR)%I.

  Global Instance is_list'_timeless hd xs: TimelessP (is_list' hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Global Instance is_stack'_timeless xs s: TimelessP (is_stack' xs s).
  Proof. apply _. Qed.

  Lemma dup_is_list': ∀ xs hd,
    heap_ctx ★ is_list' hd xs ⊢ |=r=> is_list' hd xs ★ is_list' hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "(#? & Hs)".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "(#? & Hs)". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & #Hev & Hs')".
      iDestruct (IHxs' with "[Hs']") as "==>[Hs1 Hs2]"; first by iFrame.
      iVsIntro. iSplitL "Hhd Hs1"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Lemma extract_is_list: ∀ xs hd,
    heap_ctx ★ is_list' hd xs ⊢ |=r=> is_list' hd xs ★ is_list hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "(#? & Hs)".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "(#? & Hs)". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & Hev & Hs')".
      iDestruct (IHxs' with "[Hs']") as "==>[Hs1 Hs2]"; first by iFrame.
      iVsIntro. iSplitL "Hhd Hs1 Hev"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Definition f_spec (xs: list val) (s: loc) (f: val) (Rf RI: iProp Σ) := (* Rf, RI is some frame *)
    ∀ Φ (x: val),
      heapN ⊥ N → x ∈ xs →
      heap_ctx ★ inv N ((∃ xs, is_stack' xs s) ★ RI) ★  Rf ★ (Rf -★ Φ #())
      ⊢ WP f x {{ Φ }}.
End defs.

Section proofs.
  Context `{heapG Σ, !evidenceG loc val unitR Σ} (N: namespace).
  Context (R: val → iProp Σ).

Lemma new_stack_spec' Φ RI:
    heapN ⊥ N →
    heap_ctx ★ RI ★ (∀ γ s : loc, inv N ((∃ xs, is_stack' R γ xs s) ★ RI) -★ Φ #s)
    ⊢ WP new_stack #() {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & HR & HΦ)".
    iVs (own_alloc (● (∅: evmapR loc val unitR) ⋅ ◯ ∅)) as (γ) "[Hm Hm']".
    { apply auth_valid_discrete_2. done. }
    wp_seq. wp_bind (ref NONE)%E. wp_alloc l as "Hl".
    wp_alloc s as "Hs".
    iAssert ((∃ xs : list val, is_stack' R γ xs s) ★ RI)%I with "[-HΦ Hm']" as "Hinv".
    { iFrame. iExists [], l. iFrame. simpl. iSplitL "Hl".
      - eauto.
      - iExists ∅. iSplitL. iFrame. by iApply (big_sepM_empty (fun hd v => perR R hd v)). }
    iVs (inv_alloc N _ ((∃ xs : list val, is_stack' R γ xs s) ★ RI)%I with "[-HΦ Hm']") as "#?"; first eauto.
    by iApply "HΦ".
  Qed.
    
  Lemma iter_spec Φ γ s (Rf RI: iProp Σ):
    ∀ xs hd (f: expr) (f': val),
      heapN ⊥ N → f_spec N R γ xs s f' Rf RI → to_val f = Some f' →
      heap_ctx ★ inv N ((∃ xs, is_stack' R γ xs s) ★ RI) ★
      is_list' γ hd xs ★ Rf ★ (Rf -★ Φ #())
      ⊢ WP (iter #hd) f {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs'].
    - simpl. iIntros (hd f f' HN ? ?) "(#Hh & #? & Hxs1 & HRf & HΦ)".
      iDestruct "Hxs1" as (q) "Hhd".
      wp_rec. wp_value. iVsIntro. wp_let. wp_load. wp_match. by iApply "HΦ".
    - simpl. iIntros (hd f f' HN Hf ?) "(#Hh & #? & Hxs1 & HRf & HΦ)".
      iDestruct "Hxs1" as (hd2 q) "(Hhd & Hev & Hhd2)".
      wp_rec. wp_value. iVsIntro. wp_let. wp_load. wp_match. wp_proj.
      wp_bind (f' _). iApply Hf=>//; first set_solver. iFrame "#". iFrame. iIntros "HRf".
      wp_seq. wp_proj. iApply (IHxs' with "[-]")=>//.
      + rewrite /f_spec. iIntros (? ? ? ?) "(#? & #? & ? & ?)".
        iApply Hf=>//.
        * set_solver.
        * iFrame "#". by iFrame.
      + apply to_of_val.
      + iFrame "#". by iFrame.
  Qed.
  
  Lemma push_spec Φ γ (s: loc) (x: val) RI:
    heapN ⊥ N →
    heap_ctx ★ R x ★ inv N ((∃ xs, is_stack' R γ xs s) ★ RI) ★ ((∃ hd, evs γ hd x) -★ Φ #())
    ⊢ WP push #s x {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & HRx & #? & HΦ)".
    iDestruct (push_atomic_spec N s x with "Hh") as "Hpush"=>//.
    iSpecialize ("Hpush" $! (R x) (fun _ ret => (∃ hd, evs γ hd x) ★ ret = #())%I with "[]").
    - iIntros "!# Rx".
      (* open the invariant *)
      iInv N as "[IH1 ?]" "Hclose".
      iDestruct "IH1" as (xs hd) "[>Hs [>Hxs HR]]".
      iDestruct (extract_is_list with "[Hxs]") as "==>[Hxs Hxs']"; first by iFrame.
      iDestruct (dup_is_list with "[Hxs']") as "[Hxs'1 Hxs'2]"; first by iFrame.
      (* mask magic *)
      iVs (pvs_intro_mask' (⊤ ∖ nclose N) heapN) as "Hvs"; first set_solver.
      iVsIntro. iExists (xs, hd).
      iFrame "Hs Hxs'1". iSplit.
      + (* provide a way to rollback *)
        iIntros "[Hs Hl']".
        iVs "Hvs". iVs ("Hclose" with "[-Rx]"); last done.
        { iNext. iFrame. iExists xs. iExists hd. by iFrame. }
      + (* provide a way to commit *)
        iIntros (v) "Hs".
        iDestruct "Hs" as (hd') "[% [Hs [[Hhd'1 Hhd'2] Hxs']]]". subst.
        iVs "Hvs".
        iDestruct "HR" as (m) "[>Hom HRm]".
        destruct (m !! hd') eqn:Heqn.
        * iDestruct (big_sepM_delete_later (perR R) m with "HRm") as "[Hx ?]"=>//.
          iDestruct "Hx" as (?) "(_ & _ & >Hhd'')".
          iDestruct (heap_mapsto_op_1 with "[Hhd'1 Hhd'2]") as "[_ Hhd]"; first iFrame.
          rewrite Qp_div_2.
          iDestruct "Hhd''" as (q v) "Hhd''". iExFalso.
          iApply (bogus_heap hd' 1%Qp q); first apply Qp_not_plus_q_ge_1.
          iFrame "#". iFrame.
        * iAssert (evs γ hd' x ★ ▷ (allR R γ))%I
                  with "==>[Rx Hom HRm Hhd'1]" as "[#Hox ?]".
          {
            iDestruct (evmap_alloc _ _ _ m with "[Hom]") as "==>[Hom Hox]"=>//.
            iDestruct (big_sepM_insert_later (perR R) m) as "H"=>//.
            iSplitL "Hox".
            { rewrite /evs /ev. eauto. }
            iExists (<[hd' := ((), DecAgree x)]> m).
            iFrame. iApply "H". iFrame. iExists x.
            iFrame. rewrite /allocated. iSplitR "Hhd'1"; auto.
          }
          iVs ("Hclose" with "[-]").
          { iNext. iFrame. iExists (x::xs).
            iExists hd'. iFrame.
            iExists hd, (1/2)%Qp. by iFrame.
          }
        iVsIntro. iSplitL; last auto. by iExists hd'.
    - iApply wp_wand_r. iSplitL "HRx Hpush".
      + by iApply "Hpush".
      + iIntros (?) "H". iDestruct "H" as (_) "[? %]". subst.
        by iApply "HΦ".
  Qed.

  (* some helpers *)
  Lemma access (γ: gname) (x: val) (xs: list val) (m: evmapR loc val unitR) :
    ∀ hd: loc,
    x ∈ xs  →
    ▷ ([★ map] hd↦v ∈ m, perR R hd v) ★ own γ (● m) ★
    is_list' γ hd xs
    ⊢ ∃ hd', ▷ ([★ map] hd↦v ∈ delete hd' m, perR R hd v) ★
             ▷ perR R hd' ((∅: unitR), DecAgree x) ★ m !! hd' = Some ((∅: unitR), DecAgree x) ★ own γ (● m).
  Proof.
    induction xs as [|x' xs' IHxs'].
    - iIntros (? Habsurd). inversion Habsurd.
    - destruct (decide (x = x')) as [->|Hneq].
      + iIntros (hd _) "(HR & Hom & Hxs)".
        simpl. iDestruct "Hxs" as (hd' q) "[Hhd [#Hev Hxs']]".
        rewrite /evs.
        iDestruct (ev_map_witness _ _ _ m with "[Hev Hom]") as %H'; first by iFrame.
        iDestruct (big_sepM_delete_later (perR R) m with "HR") as "[Hp HRm]"=>//.
        iExists hd. by iFrame.
      + iIntros (hd ?).
        assert (x ∈ xs'); first set_solver.
        iIntros "(HRs & Hom & Hxs')".
        simpl. iDestruct "Hxs'" as (hd' q) "[Hhd [Hev Hxs']]".
        iDestruct (IHxs' hd' with "[HRs Hxs' Hom]") as "?"=>//.
        iFrame.
  Qed.

End proofs.
