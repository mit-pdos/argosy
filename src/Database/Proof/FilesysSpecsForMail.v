From iris.proofmode Require Export tactics.
From iris.algebra Require Import auth frac_auth.
From iris.base_logic.lib Require Import invariants.

From RecoveryRefinement Require Export CSL.WeakestPre CSL.Lifting.

From RecoveryRefinement Require Import Database.Proof.BaseMachine.
Require Import FilesysSpecs.

Implicit Types (p:Path) (fh:Fd) (bs:ByteString).

Definition path_dec : forall (a b : Path), {a=b}+{a<>b} := string_dec.

Axiom is_tmpfile : Path -> bool.

Section DerivedSpecs.
  Context `{!baseG Σ}.
  Context `{!inG Σ (authR (optionUR (exclR boolC)))}.

  (* TODO: should really be a set of paths, or invariant to permutation;
  currently ignoring this complication entirely *)
  Definition direntsG (S: list Path) (G: gmap Path gname) : iProp Σ :=
    ( dirents S ∗
      ⌜ ∀ fn g, G !! fn = Some g -> is_tmpfile fn = true ⌝ ∗
      ∀ fn g,
        ⌜ G !! fn = Some g ⌝ -∗
        own g (● (Excl' (if In_dec string_dec fn S then true else false))) )%I.

  Definition dir_inv_inner (G: gmap Path gname) : iProp Σ :=
    ( ∃ S,
      direntsG S G ∗
      ∀ fn, ⌜ fn ∈ S ⌝ -∗
        if is_tmpfile fn then
          True
        else
          ∃ bs, fn ↦ bs )%I.

  Definition dirN : namespace := nroot .@ "dir".
  Definition dir_inv (G : gmap Path gname) : iProp Σ :=
    inv dirN (dir_inv_inner G).

  Theorem create_ok G p g :
    {{{ dir_inv G ∗ ▷ own g (◯ (Excl' false)) ∗ ⌜G !! p = Some g⌝ }}}
      FS.create p
      {{{ fh, RET fh; own g (◯ (Excl' true)) ∗ p ↦ BS.empty ∗ fh ↦ (p, FS.Write) }}}.
  Proof.
    iIntros (phi).
    iIntros "(#Hinv&Hown&#Heq) Post".

    unfold dir_inv.
    iInv dirN as (S) "(H1&H2)" "Hclose".

    unfold direntsG.
    iDestruct "H1" as "[Hx [#Hy Hz]]".

    destruct (In_dec string_dec p S).
    {
      iSpecialize ("Hz" $! p g).
      (* contradiction: Hown and Hz.  but the triangle is preventing us.. *)
      (* iSpecialize ("Hy" with "Heq").
         ...
      *)
    }

    assert (¬ p ∈ S).
    {
      (* need some lemma about In implying elem_of *)
      admit.
    }

    iApply (wp_create with "[Hx Heq]").
    {
      iNext.
      iFrame.
      eauto.
    }

    iNext.
    iIntros (fh) "(Hdir&Hp&Hfd)".

    iMod ("Hclose" with "[Hdir H2 Heq Hy Hz Hown]") as "_".
    {
      iNext.
      iExists _.
      unfold direntsG.
      iSplitL "Hdir Hy Hz Hown". iSplitL "Hdir". iFrame.
      {
        iSplitL "Hy". eauto.
        iIntros.
        iSpecialize ("Hz" $! fn g0 a).
        destruct (string_dec fn p).
        {
          subst.
          rewrite a.
          simpl; destruct (string_dec p p); try congruence.
          (* g = g0 *)
          (* p not in S *)
          (* unify the two halves of the circles *)
          admit.
        }
        {
          (* fn != p, so equal to Hx *)
          admit.
        }
      }

      iIntros.
      inversion a; subst.
      {
        iDestruct "Hy" as %?.
        iDestruct "Heq" as %?.
        specialize (H0 p g H1).
        rewrite H0.
        eauto.
      }

      iApply "H2". eauto.
    }

    iApply "Post".
    iFrame.

  Admitted.

  Theorem wp_append fh bs' p bs :
    {{{ ▷ (p ↦ bs ∗ fh ↦ (p, FS.Write)) }}}
      FS.append fh bs'
      {{{ RET (); p ↦ (BS.append bs bs') ∗ fh ↦ (p, FS.Write) }}}.
  Admitted.

  Theorem wp_close fh p m :
    {{{ ▷ fh ↦ (p, m) }}}
      FS.close fh
      {{{ RET (); emp }}}.
  Admitted.

  (* TODO: is this the right spec? should [p ↦ bs] be in the precondition? how
  are [p ↦ ?] facts related to dirents S? *)
  Theorem wp_open G p bs :
    {{{ dir_inv G ∗ ▷ p ↦ bs }}}
      FS.open p
      {{{ fh, RET fh; p ↦ bs ∗ fh ↦ (p, FS.Read) }}}.
  Admitted.

  Theorem wp_readAt fh off len p bs :
    {{{ ▷ (p ↦ bs ∗ fh ↦ (p, FS.Read)) }}}
      FS.readAt fh off len
      {{{ bs_r, RET bs_r; ⌜bs_r = BS.take len (BS.drop off bs)⌝ ∗ p ↦ bs ∗ fh ↦ (p, FS.Read) }}}.
  Admitted.

  Theorem wp_size fh p bs :
    {{{ ▷ (p ↦ bs ∗ fh ↦ (p, FS.Read)) }}}
      FS.size fh
      {{{ len, RET len; ⌜len = BS.length bs⌝ ∗ p ↦ bs ∗ fh ↦ (p, FS.Read) }}}.
  Admitted.

  (* TODO: constrain result [r] in terms of owned ghost variables from g *)
  Theorem wp_list S G :
    {{{ ▷ dirents S G }}}
      FS.list
      {{{ r, RET r; ⌜ r = S ⌝ }}}.
  Admitted.

  (* TODO: require no open FDs for the deleted file? *)
  Theorem wp_delete G p g bs :
    {{{ dir_inv G ∗ ▷ (own g (◯ (Excl' true)) ∗ p ↦ bs) ∗ ⌜G !! p = Some g⌝ }}}
      FS.delete p
      {{{ RET (); own g (◯ (Excl' false)) }}}.
  Admitted.

  Theorem wp_link G (src dst : Path) bs :
    {{{ dir_inv G ∗ ▷ src ↦ bs }}}
      FS.link src dst
      {{{ ok, RET ok;
        match ok with
        | false => src ↦ bs
        | true => src ↦ bs ∗ dst ↦ bs (* XXX really need to connect to set of messages in mailbox *)
        end }}}.
  Admitted.

  Theorem wp_random :
    {{{ True }}}
      FS.random
      {{{ r, RET r; True }}}.
  Admitted.

End lifting.

(*
  Context `{baseG Σ}.

  Local Open Scope bi_scope.

  Definition appendFile p fh bs := p ↦ bs ∗ fh ↦ (p, FS.Write).
  Definition readFile p fh bs := p ↦ bs ∗ fh ↦ (p, FS.Read).

  Theorem create_ok S p fh :
    {{{ ▷ dirents S ∗ ⌜~p ∈ S⌝ }}}
      FS.create p
      {{{ RET fh; dirents (p::S) ∗ appendFile p fh BS.empty }}}.
  Proof.
    iIntros (Φ).
    iApply wp_create.
  Qed.

  Theorem append_ok fh bs' p bs :
    {{{ ▷ appendFile p fh bs }}}
      FS.append fh bs'
      {{{ RET (); appendFile p fh (BS.append bs bs') }}}.
  Proof.
    iIntros (Φ).
    iApply wp_append.
  Qed.

  Theorem append_close_ok fh p bs :
    {{{ ▷ appendFile p fh bs }}}
      FS.close fh
      {{{ RET (); p ↦ bs }}}.
  Proof.
    iIntros (Φ) "!> Hpre Post".
    iDestruct "Hpre" as "(Hp & Hfh)".
    iApply (wp_close with "Hfh").
    iIntros "!> _".
    iApply ("Post" with "Hp").
  Qed.

  Theorem read_close_ok fh p bs :
    {{{ ▷ readFile p fh bs }}}
      FS.close fh
      {{{ RET (); p ↦ bs }}}.
  Proof.
    iIntros (Φ) "!> Hpre Post".
    iDestruct "Hpre" as "(Hp & Hfh)".
    iApply (wp_close with "Hfh").
    iIntros "!> _".
    iApply ("Post" with "Hp").
  Qed.

  Theorem open_ok S p fh bs :
    {{{ ▷ (dirents S ∗ p ↦ bs) ∗ ⌜p ∈ S⌝ }}}
      FS.open p
      {{{ RET fh; dirents S ∗ readFile p fh bs }}}.
  Proof.
    iIntros (Φ).
    iApply wp_open.
  Qed.

  Theorem readAt_ok fh off len p bs bs_r :
    {{{ ▷ readFile p fh bs }}}
      FS.readAt fh off len
      {{{ RET bs_r; ⌜bs_r = BS.take len (BS.drop off bs)⌝ ∗ readFile p fh bs }}}.
  Proof.
    iIntros (Φ).
    iApply wp_readAt.
  Qed.

End DerivedSpecs.

Global Opaque appendFile readFile.
*)
