(* Syncer spec *)

From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.

Section sync.
  Context `{!heapG Σ} (N : namespace).

  (* TODO: Use our usual style with a generic post-condition. *)
  (* TODO: We could get rid of the x, and hard-code a unit. That would
     be no loss in expressiveness, but probably more annoying to apply.
     How much more annoying? And how much to we gain in terms of things
     becomign easier to prove? *)
  Definition is_syncer (R: iProp Σ) (s: val) :=
    (□ ∀ (f : val) P Q, (∀ x, {{ R ★ P x }} f x {{ v, R ★ Q x v }}) -★
                    WP s f {{ f', ∀ x, {{ P x }} f' x {{ v, Q x v }} }})%I.

  Definition mk_syncer_spec (mk_syncer: val) :=
    ∀ (R: iProp Σ) (Φ: val -> iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ R ★ (∀ s, is_syncer R s -★ Φ s) ⊢ WP mk_syncer #() {{ Φ }}.
End sync.
