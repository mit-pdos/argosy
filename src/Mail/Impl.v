From Coq Require Import List.

From RecoveryRefinement Require Export Lib.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Database.Base.
From RecoveryRefinement Require Import Database.Proof.FilesysSpecsForMail.
From RecoveryRefinement Require Export CSL.WeakestPre CSL.Lifting.
From RecoveryRefinement Require Import Database.Proof.BaseMachine.

From iris.algebra Require Import auth frac_auth.
From iris.base_logic.lib Require Import invariants.


Axiom pid_to_tmpfile : uint64 -> Path.
Axiom rnd_to_msgfile : uint64 -> Path.

Section MailServer.

  Context `{!baseG Σ}.
  Context `{!inG Σ (authR (optionUR (exclR boolC)))}.


  Import ProcNotations.
  Local Open Scope proc.


  Definition deliver (pid : uint64) (msg : ByteString) :=
    let tmpfile := pid_to_tmpfile pid in
    fd <- FS.create tmpfile;
    _ <- FS.append fd msg;
    _ <- FS.close fd;
    _ <- Loop
      (fun _ =>
        rnd <- FS.random;
        let msgfile := rnd_to_msgfile rnd in
        ok <- FS.link tmpfile msgfile;
        if ok then
          LoopRet tt
        else
          Continue tt) tt;
    FS.delete tmpfile.

  Definition pickup :=
    fns <- FS.list;
    Loop
      (fun '(fns, msgs) =>
        match fns with
        | nil => LoopRet msgs
        | fn :: fns' =>
          if is_tmpfile fn then Continue (fns', msgs)
          else
            fd <- FS.open fn;
            len <- FS.size fd;
            msg <- FS.readAt fd 0 len;
            _ <- FS.close fd;
            Continue (fns', (fn, msg) :: msgs)
        end) (fns, nil).

  Definition delete (fn : Path) :=
    FS.delete fn.


  Theorem deliver_ok G g pid msg :
    {{{ dir_inv G ∗ ▷ own g (◯ (Excl' false)) ∗ ⌜G !! (pid_to_tmpfile pid) = Some g⌝ }}}
      deliver pid msg
      {{{ RET (); own g (◯ (Excl' false)) }}}.
  Proof.
    iIntros (Φ) "(#Hinv&Hown&#Heq) Post".
    unfold deliver.

    wp_bind.
    iApply (wp_create with "[Hinv Hown Heq]").
    iFrame. eauto.
    iIntros (fh) "!> (Hown&Htmp&Hfd)".

    wp_bind.
    iApply (wp_append with "[Htmp Hfd]").
    iFrame.
    iIntros "!> (Htmp&Hfd)".

    wp_bind.
    iApply (wp_close with "Hfd").
    iIntros "!> _".

    wp_bind.

    iLöb as "IHloop".

    wp_loop.
    wp_bind.
    iApply (wp_random).
    eauto.
    iIntros (rnd) "!> _".

    wp_bind.
    iApply (wp_link with "[Hinv Htmp]").
    iFrame. eauto.
    iIntros (ok).
    destruct ok.

    - iIntros "!> (Htmp&Hrnd)".
      wp_ret.
      iNext.
      wp_ret.
      iApply (wp_delete with "[Hinv Hown Htmp Heq]").
      iFrame. eauto.

      iNext.
      iIntros "Hown".
      iApply "Post".
      iFrame.

    - iIntros "!> (Hd&Ht)".
      wp_ret.
      iNext.
      iApply ("IHloop" with "Post Hd Ho").
      iFrame.
  Qed.



(*
  What's going on with [iInv] here???



  Definition mbox_inv_inner (G : gmap Path gname) : iProp Σ :=
    ( ∃ msgs,
      mbox_rep G msgs )%I.

  Definition mbox_inv (G : gmap Path gname) : iProp Σ :=
    inv mboxN (mbox_inv_inner G).



  Definition deliver2 (pid : uint64) (msg : ByteString) :=
    res <- deliver pid msg;
    Ret res.

  Theorem deliver_inv_ok G g pid msg :
    {{{ mbox_inv G ∗ ▷ (own g (◯ (Excl' false))) ∗ ⌜G !! (pid_to_tmpfile pid) = Some g⌝ }}}
      deliver2 pid msg
      {{{ RET (); mbox_inv G ∗ own g (◯ (Excl' false)) }}}.
  Proof.
    iIntros (phi) "(#Hinv&H&#He) Post".
    unfold mbox_inv.

    wp_bind.
    wp_bind.
    iInv mboxN as "_".

    iApply deliver_ok.
    iInv mboxN as "H".

    iInv mboxN as "Hz" "Hclose".
    iApply deliver_ok.
    iNext.
*)

  Theorem pickup_ok G msgs :
    {{{ ▷ mbox_rep G msgs }}}
      pickup
      {{{ ret, RET ret;
          mbox_rep G msgs ∗ ⌜∀ msgid msg, (msgid, msg) ∈ msgs -> (msgid, msg) ∈ ret⌝ }}}.
  Proof.
    iIntros (Φ) "(Hd&Hrep) Post".
    unfold pickup.
    wp_bind.

    iApply (wp_list with "Hd").
    iIntros (r).
    iNext.
    iIntros "(Hr&Hd)".



End MailServer.
