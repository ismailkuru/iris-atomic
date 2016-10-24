(* Logically atomic triple *)

From iris.program_logic Require Export hoare weakestpre pviewshifts.
From iris.prelude Require Export coPset.
Import uPred.

Section atomic.
  Context `{irisG Λ Σ} (A: Type).

  (* TODO RJ: IMHO it would make more sense to have the outer mask first, after all, that's what the shifts "starts" with. *)
  Definition atomic_triple_base
             (α: A → iProp Σ) (* atomic pre-condition *)
             (β: A → val _ → iProp Σ) (* atomic post-condition *)
             (Ei Eo: coPset) (* inside/outside masks *)
             (e: expr _) P Q : iProp Σ :=
    ((P ={Eo, Ei}=> ∃ x:A,
                       α x ★
                       ((α x ={Ei, Eo}=★ P) ∧
                        (∀ v, β x v ={Ei, Eo}=★ Q x v))
     ) -★ {{ P }} e @ ⊤ {{ v, (∃ x: A, Q x v) }})%I.

  (* logically atomic triple: <x, α> e @ E_i, E_o <v, β x v> *)
  Definition atomic_triple α β Ei Eo e := (∀ P Q, atomic_triple_base α β Ei Eo e P Q)%I.

  Arguments atomic_triple {_} _ _ _ _.
End atomic.
