
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import dec_agree frac.
From iris_atomic Require Import atomic sync misc.

Definition syncR := prodR fracR (dec_agreeR val). (* track the local knowledge of ghost state *)
Class syncG Σ := sync_tokG :> inG Σ syncR.
Definition syncΣ : gFunctors := #[GFunctor (constRF syncR)].

Instance subG_syncΣ {Σ} : subG syncΣ Σ → syncG Σ.
Proof. by intros ?%subG_inG. Qed.

Section atomic_sync.
  Context `{EqDecision A, !heapG Σ, !lockG Σ, !inG Σ (prodR fracR (dec_agreeR A))} (N : namespace).

  (* TODO: Rename and make opaque; the fact that this is a half should not be visible
           to the user. *)
  Definition gHalf (γ: gname) g : iProp Σ := own γ ((1/2)%Qp, DecAgree g).

  Definition atomic_triple' γ (f: val)
             (α: A → val → iProp Σ)
             (β: A → A → val → val → iProp Σ)
             (Ei Eo: coPset) : iProp Σ :=
    (∀ x, atomic_triple A (fun g => gHalf γ g ★ □ α g x)%I
                    (fun g v => ∃ g':A, gHalf γ g' ★ β g g' x v)%I
                    Ei Eo (f x))%I.

(*  Definition seq_spec (f: val) (ϕ: val → A → iProp Σ) α β (E: coPset) :=
      ∀ (Φ: val → iProp Σ) (l: val),
         {{ True }} f l {{ f', ■ (∀ (x: val) (Φ: val → iProp Σ) (g: A),
                               heapN ⊥ N →
                               heap_ctx ★ ϕ l g ★ □ α x g ★
                               (∀ (v: val) (g': A),
                                  ϕ l g' -★ β x g g' v ={E}=★ Φ v)
                               ⊢ WP f' x @ E {{ Φ }} )}}.
  (* The linear view shift in the above post-condition is for the final step
     of computation. The client side of such triple will have to prove that the
     specific post-condition he wants can be lvs'd from whatever threaded together
     by magic wands. The library side, when proving seq_spec, will always have
     a view shift at the end of evalutation, which is exactly what we need.  *)*)

  Definition seq_spec ϕ f (α: A → val → iProp Σ) (β: A → A → val → val → iProp Σ) :=
    (□ ∀ g x Φ, (ϕ g ★ α g x ★ (∀ g' v, ϕ g' ★ β g g' x v -★ Φ v) -★ WP f #() {{ Φ }}))%I.

  (* TODO: Use our usual style with a generic post-condition. *)
  (* TODO: We could get rid of the x, and hard-code a unit. That would
     be no loss in expressiveness, but probably more annoying to apply.
     How much more annoying? And how much to we gain in terms of things
     becomign easier to prove? *)
  (* This is really the core of the spec: It says that executing `s` on `f`
     turns the sequential spec with f, α, β into the concurrent triple with f', α, β. *)
  Definition is_atomic_syncer (ϕ: A → iProp Σ) (s: val) γ := 
    (□ ∀ (f: val) α β, seq_spec ϕ f α β -★ WP s f {{ f', atomic_triple' γ f' α β ∅ ⊤ }})%I.

  Definition atomic_syncer_spec (atomic_syncer: val) :=
    ∀ (g0: A) (ϕ: A → iProp Σ) (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ ϕ g0 ★ (∀ γ s, gHalf γ g0 ★ is_atomic_syncer ϕ s γ -★ Φ s) ⊢ WP atomic_syncer #() {{ Φ }}.

  Lemma atomic_spec (mk_syncer: val):
      mk_syncer_spec N mk_syncer → atomic_syncer_spec mk_syncer.
  Proof.
    (* TODO: Proof needs updating. *)
    iIntros (g0 HN Hseq Hsync) "[#Hh Hϕ]".
    iVs (own_alloc (((1 / 2)%Qp, DecAgree g0) ⋅ ((1 / 2)%Qp, DecAgree g0))) as (γ) "[Hg1 Hg2]".
    { by rewrite pair_op dec_agree_idemp. }
    repeat wp_let. wp_bind (mk_syncer _).
    iApply (Hsync (∃ g: A, ϕ l g ★ gHalf γ g)%I)=>//. iFrame "Hh".
    iSplitL "Hg1 Hϕ".
    { iExists g0. by iFrame. }
    iIntros (s) "#Hsyncer".
    wp_let. wp_bind (f_seq _). iApply wp_wand_r.
    iSplitR; first iApply Hseq=>//; auto.
    iIntros (f) "%".
    iApply wp_wand_r.
    iSplitR; first iApply "Hsyncer".
    iIntros (f') "#Hsynced".
    iExists γ. iFrame.
    iIntros (x). iAlways.
    iIntros (P Q) "#Hvss".
    iSpecialize ("Hsynced" $! P Q x).
    iIntros "!# HP". iApply wp_wand_r. iSplitL "HP".
    - iApply ("Hsynced" with "[]")=>//.
      iAlways. iIntros "[HR HP]". iDestruct "HR" as (g) "[Hϕ Hg1]".
      (* we should view shift at this point *)
      iDestruct ("Hvss" with "HP") as "Hvss'". iApply pvs_wp.
      iVs "Hvss'". iDestruct "Hvss'" as (?) "[[Hg2 #Hα] [Hvs1 _]]".
      iDestruct (m_frag_agree with "[Hg1 Hg2]") as %Heq; first iFrame. subst.
      iVs ("Hvs1" with "[Hg2]") as "HP"; first by iFrame.
      iVsIntro. iApply H=>//.
      iFrame "Hh Hϕ". iSplitR; first done. iIntros (ret g') "Hϕ' Hβ".
      iVs ("Hvss" with "HP") as (g'') "[[Hg'' _] [_ Hvs2]]".
      iSpecialize ("Hvs2" $! ret).
      iDestruct (m_frag_agree' with "[Hg'' Hg1]") as "[Hg %]"; first iFrame. subst.
      rewrite Qp_div_2.
      iAssert (|=r=> own γ (((1 / 2)%Qp, DecAgree g') ⋅ ((1 / 2)%Qp, DecAgree g')))%I
              with "[Hg]" as "==>[Hg1 Hg2]".
      { iApply own_update; last by iAssumption.
        apply cmra_update_exclusive. by rewrite pair_op dec_agree_idemp. }
      iVs ("Hvs2" with "[Hg1 Hβ]").
      { iExists g'. iFrame. }
      iVsIntro. iSplitL "Hg2 Hϕ'"; last done.
      iExists g'. by iFrame.
    - iIntros (?) "?". by iExists g0.
  Qed.

End atomic_sync.
